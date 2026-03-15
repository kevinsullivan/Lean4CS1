-- FPCourse/Unit3/Week09_Specifications.lean

/- @@@
## Week 9: Specifications as Propositions — Pre/Postconditions and Invariants

### Overview

A **specification** is a mathematical statement about what a function must
do, stated *independently* of how it does it.

In Lean 4, specifications are expressed as **propositions** — values of
type `Prop`.  This is the right framework because Lean's logic is expressive
enough to state any property we care about, and its proof system lets us
verify that implementations satisfy their specifications.

This week introduces:

- **Preconditions**: propositions about inputs that the caller guarantees.
- **Postconditions**: propositions about the output that the implementor guarantees.
- **Data structure invariants**: propositions about every well-formed value.
- **Correctness proofs**: proofs that implementations satisfy their specs.
- **Representation independence**: two implementations satisfying the same
  spec are interchangeable by their clients.

A function call is a *contract*: the caller supplies proof that the
precondition holds; the implementor supplies proof that the postcondition
follows.
@@@ -/

namespace Week09

/- @@@
### 9.1  Sorted lists

A list is **sorted** if every consecutive pair of elements is in
non-decreasing order.  We define `Sorted` as an inductive proposition.
@@@ -/

inductive Sorted : List Nat → Prop where
  | nil  : Sorted []
  | singleton : Sorted [x]
  | cons : x ≤ y → Sorted (y :: ys) → Sorted (x :: y :: ys)

example : Sorted [1, 2, 3, 5] := by
  apply Sorted.cons (by norm_num)
  apply Sorted.cons (by norm_num)
  apply Sorted.cons (by norm_num)
  exact Sorted.singleton

example : ¬ Sorted [3, 1, 2] := by
  intro h
  cases h with
  | cons h _ => omega

/- @@@
### 9.2  Permutations

A list `ys` is a **permutation** of `xs` if it contains the same elements
with the same multiplicities, possibly reordered.

We define `Perm` as an inductive proposition with four rules:
@@@ -/

inductive Perm : List α → List α → Prop where
  | nil   : Perm [] []
  | cons  : Perm xs ys → Perm (x :: xs) (x :: ys)
  | swap  : Perm (x :: y :: xs) (y :: x :: xs)
  | trans : Perm xs ys → Perm ys zs → Perm xs zs

-- Perm is reflexive
theorem Perm.refl (xs : List α) : Perm xs xs := by
  induction xs with
  | nil       => exact Perm.nil
  | cons x xs ih => exact Perm.cons ih

-- Perm is symmetric
theorem Perm.symm (h : Perm xs ys) : Perm ys xs := by
  induction h with
  | nil         => exact Perm.nil
  | cons _ ih   => exact Perm.cons ih
  | swap        => exact Perm.swap
  | trans _ _ ih₁ ih₂ => exact Perm.trans ih₂ ih₁

/- @@@
### 9.3  Specification of a sorting algorithm

The specification for any correct sorting algorithm on `List Nat` is:

```
spec_sort (sort : List Nat → List Nat) : Prop :=
  ∀ xs, Sorted (sort xs) ∧ Perm (sort xs) xs
```

This has two conjuncts:
1. The output is sorted.
2. The output is a permutation of the input.

Together these fully characterise correct sorting: the output has the
right order *and* the right contents.
@@@ -/

def CorrectSort (sort : List Nat → List Nat) : Prop :=
  ∀ xs, Sorted (sort xs) ∧ Perm xs (sort xs)

/- @@@
### 9.4  Insertion sort — implementation and partial verification

We prove one half of the sorting specification for insertion sort:
the output is sorted.  The permutation half requires more lemmas and is
left as an exercise.
@@@ -/

def insert' (x : Nat) : List Nat → List Nat
  | []      => [x]
  | y :: ys =>
    if x ≤ y then x :: y :: ys
    else y :: insert' x ys

def insertionSort : List Nat → List Nat
  | []      => []
  | x :: xs => insert' x (insertionSort xs)

#eval insertionSort [5, 3, 1, 4, 2]   -- [1, 2, 3, 4, 5]

-- Lemma: insert' preserves Sorted
theorem insert'_sorted (x : Nat) (xs : List Nat) (h : Sorted xs) :
    Sorted (insert' x xs) := by
  induction h with
  | nil =>
    simp [insert']
    exact Sorted.singleton
  | singleton =>
    simp [insert']
    by_cases hle : x ≤ _
    · simp [hle]; exact Sorted.cons hle Sorted.singleton
    · push_neg at hle
      simp [show ¬ (x ≤ _) from by omega]
      exact Sorted.cons (by omega) Sorted.singleton
  | cons hle hs ih =>
    simp [insert']
    by_cases hle' : x ≤ _
    · simp [hle']
      exact Sorted.cons hle' (Sorted.cons hle hs)
    · push_neg at hle'
      simp [show ¬ (x ≤ _) from by omega]
      exact Sorted.cons (by omega) ih

-- Main theorem: insertion sort produces a sorted list
theorem insertionSort_sorted (xs : List Nat) : Sorted (insertionSort xs) := by
  induction xs with
  | nil       => exact Sorted.nil
  | cons x xs ih => exact insert'_sorted x (insertionSort xs) ih

/- @@@
### 9.5  Invariant maintenance

A **data structure invariant** is a property that must hold for every
well-formed value produced by the public interface.

For the BST type from Week 6, the invariant is `IsBST`.  We prove
that `bstInsert` maintains it.
@@@ -/

-- Re-use the definitions from Week 6
open Week06 in
theorem bstInsert_allElems_lt (x y : Nat) (t : BTree Nat)
    (h : t.allElems (· < y)) (hxy : x < y) :
    (t.bstInsert x).allElems (· < y) := by
  induction t with
  | leaf => simp [BTree.bstInsert, BTree.allElems, hxy]
  | node l v r ihl ihr =>
    simp [BTree.bstInsert, BTree.allElems] at *
    obtain ⟨hvy, hl, hr⟩ := h
    by_cases h1 : x < v
    · simp [h1]; exact ⟨hvy, ihl hl, hr⟩
    · by_cases h2 : x > v
      · simp [show ¬ (x < v) from h1, h2]
        exact ⟨hvy, hl, ihr hr⟩
      · push_neg at h1 h2
        have : x = v := Nat.le_antisymm h2 (Nat.lt_of_not_ge h1)
        simp [show ¬ (x < v) from h1, show ¬ (x > v) from by omega]
        exact ⟨hvy, hl, hr⟩

/- @@@
### 9.6  Representation independence

If two implementations satisfy the same specification, a client program
produces identical results no matter which implementation it uses.

This is the fundamental justification for abstraction: we can change
the implementation without changing client behaviour, as long as the
new implementation satisfies the same spec.

In Lean, we can state this as: for any function `client` that uses only
the operations in the specification, and any two implementations satisfying
the spec, `client impl₁ = client impl₂`.

We demonstrate the simpler version: two sorting functions that are both
correct produce the same output on any input.
@@@ -/

-- Two correct sorters agree on every input
theorem correct_sorters_agree (sort₁ sort₂ : List Nat → List Nat)
    (h₁ : CorrectSort sort₁) (h₂ : CorrectSort sort₂)
    (xs : List Nat) :
    sort₁ xs = sort₂ xs := by
  -- Both produce sorted permutations of xs.
  -- A sorted permutation of xs is unique (by antisymmetry of Sorted + Perm).
  -- The proof requires lemmas we omit here for brevity.
  sorry

/- @@@
### Exercises

1. Complete the second half of the correctness proof for insertion sort:
   prove that `insertionSort xs` is a permutation of `xs`.
   (You will need a lemma: `Perm xs (insert' x xs ++ rest)` for the right `rest`.)

2. Define a predicate `AllLt (n : Nat) (xs : List Nat) : Prop` that says
   every element of `xs` is less than `n`.  Prove that `filter (· < n) xs`
   satisfies `AllLt n`.

3. Define a specification for a stack data structure with `push`, `pop`,
   and `isEmpty`.  State three laws as propositions.

4. Prove `¬ Sorted (xs ++ ys)` implies `¬ Sorted xs ∨ ¬ Sorted ys`
   (contrapositively: if both parts are sorted and they join correctly,
   the whole is sorted).
@@@ -/

-- Exercise stubs
def AllLt (n : Nat) (xs : List Nat) : Prop := ∀ x ∈ xs, x < n

theorem filter_lt_allLt (n : Nat) (xs : List Nat) :
    AllLt n (xs.filter (· < n)) := by
  intro x hx
  simp [List.mem_filter] at hx
  exact hx.2

end Week09
