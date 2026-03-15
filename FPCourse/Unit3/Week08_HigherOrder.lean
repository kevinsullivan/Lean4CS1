-- FPCourse/Unit3/Week08_HigherOrder.lean

/- @@@
# Unit 3 — Higher-Order Functions and Equational Proofs

## Week 8: Deriving Map, Filter, and Fold

### Overview

A **higher-order function** takes a function as an argument (or returns
one as a result).  We have already seen `applyTwice` and `polyMap`.
This week develops the three fundamental higher-order functions for lists:
**map**, **filter**, and **fold**.

The key methodology: *derivation by abstraction*.

1. Write two concrete functions that have identical structure.
2. Identify the sub-expression that differs between them.
3. Name that difference as a parameter.
4. The result is a higher-order function that subsumes both originals.

This derivation is not just a code-cleanliness technique.  It reveals
structure that was always there but not visible.  And once we have the
abstracted function, we can prove powerful general theorems about it —
theorems that apply to every concrete instance simultaneously.
@@@ -/

namespace Week08

open Week05 (myAppend)

/- @@@
### 8.1  Deriving map by abstraction

Consider these two functions:

```lean
def doubleAll : List Nat → List Nat
  | []      => []
  | x :: xs => (2 * x) :: doubleAll xs

def stringify : List Nat → List String
  | []      => []
  | x :: xs => toString x :: stringify xs
```

They have identical structure.  The only difference is the element
transformation: `(2 * x)` vs `toString x`.  Abstracting that difference
as a parameter `f` gives `map`.
@@@ -/

-- The general map function
def myMap (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: myMap f xs

-- The two originals are now special cases
def doubleAll  : List Nat → List Nat    := myMap (2 * ·)
def stringifyL : List Nat → List String := myMap toString

#eval doubleAll [1, 2, 3]    -- [2, 4, 6]
#eval stringifyL [1, 2, 3]   -- ["1", "2", "3"]

/- @@@
### 8.2  Deriving filter

Similarly, consider functions that keep or discard elements based on a
condition.  The condition differs; the structure is identical.
Abstracting the condition gives `filter`.
@@@ -/

def myFilter (p : α → Bool) : List α → List α
  | []      => []
  | x :: xs => if p x then x :: myFilter p xs else myFilter p xs

#eval myFilter (· % 2 == 0) [1, 2, 3, 4, 5, 6]   -- [2, 4, 6]
#eval myFilter (· > 3) [1, 2, 3, 4, 5]            -- [4, 5]

/- @@@
### 8.3  Deriving fold — the general list eliminator

`map` and `filter` preserve some structure of the list (they produce
lists).  **Fold** is more general: it can produce a value of any type.

The idea: a list is built from `[]` and `::`.  A fold *replaces* each
constructor with a function:

- Replace `[]` with a base value `z : β`.
- Replace `::` with a combining function `f : α → β → β`.

`foldr f z [a, b, c]`
`= f a (f b (f c z))`

This is the *universal property of fold*: every structural recursion on
a list is a fold.
@@@ -/

def myFoldr (f : α → β → β) (z : β) : List α → β
  | []      => z
  | x :: xs => f x (myFoldr f z xs)

-- map expressed as fold
def mapViaFold (f : α → β) (xs : List α) : List β :=
  myFoldr (fun x acc => f x :: acc) [] xs

-- filter expressed as fold
def filterViaFold (p : α → Bool) (xs : List α) : List α :=
  myFoldr (fun x acc => if p x then x :: acc else acc) [] xs

-- length expressed as fold
def lengthViaFold (xs : List α) : Nat :=
  myFoldr (fun _ acc => acc + 1) 0 xs

-- sum expressed as fold
def sumViaFold (xs : List Nat) : Nat :=
  myFoldr (· + ·) 0 xs

#eval sumViaFold [1, 2, 3, 4, 5]       -- 15
#eval lengthViaFold [1, 2, 3]           -- 3

/- @@@
### 8.4  The functor laws

`map` satisfies two laws that characterise it as a **functor**:

1. **Identity law**: `map id xs = xs`
   Mapping the identity function leaves the list unchanged.

2. **Composition law**: `map (f ∘ g) xs = map f (map g xs)`
   Mapping a composition equals two separate maps.

These laws are not just pleasant properties — they are the *specification*
of map.  Any function satisfying both laws is a map-like operation.
@@@ -/

-- Identity law
@[simp]
theorem myMap_id (xs : List α) : myMap id xs = xs := by
  induction xs with
  | nil       => rfl
  | cons x xs ih => simp [myMap, ih]

-- Composition law
@[simp]
theorem myMap_comp (f : β → γ) (g : α → β) (xs : List α) :
    myMap (f ∘ g) xs = myMap f (myMap g xs) := by
  induction xs with
  | nil       => rfl
  | cons x xs ih => simp [myMap, Function.comp, ih]

/- @@@
### 8.5  The fold fusion law

The **fusion law** says two passes over a list can be fused into one:

`myFoldr f z (myMap g xs) = myFoldr (f ∘ g) z xs`

This is the basis for *deforestation* — an optimisation that eliminates
intermediate data structures in function pipelines.
@@@ -/

theorem fold_map_fusion (f : β → γ → γ) (g : α → β) (z : γ) (xs : List α) :
    myFoldr f z (myMap g xs) = myFoldr (fun x acc => f (g x) acc) z xs := by
  induction xs with
  | nil       => rfl
  | cons x xs ih => simp [myMap, myFoldr, ih]

/- @@@
### 8.6  foldr over append

A key property: `foldr` distributes over `++`.
@@@ -/

theorem myFoldr_append (f : α → β → β) (z : β) (xs ys : List α) :
    myFoldr f z (xs ++ ys) = myFoldr f (myFoldr f z ys) xs := by
  induction xs with
  | nil       => simp [myFoldr]
  | cons x xs ih => simp [myFoldr, List.cons_append, ih]

/- @@@
### Exercises

1. Implement `myFoldl : (β → α → β) → β → List α → β` (left fold).
   Verify that `myFoldl (fun acc x => x :: acc) [] xs = xs.reverse`.

2. Prove that `mapViaFold f xs = myMap f xs` for all `f` and `xs`.

3. Prove that `lengthViaFold xs = xs.length` for all `xs`.

4. Implement `myConcat : List (List α) → List α` using `myFoldr` only
   (no explicit recursion, no `++` directly) and prove
   `myConcat xss = List.join xss`.

5. State and prove the following "filter-map" law:
   `myFilter p (myMap f xs) = myMap f (myFilter (p ∘ f) xs)`
   when `f` is injective.  (Hint: start without the injectivity
   assumption and see what goes wrong.)
@@@ -/

-- Exercise stubs
def myFoldl (f : β → α → β) (z : β) : List α → β
  | []      => z
  | x :: xs => myFoldl f (f z x) xs

theorem myFoldl_reverse (xs : List α) :
    myFoldl (fun acc x => x :: acc) [] xs = xs.reverse := by
  suffices h : ∀ acc, myFoldl (fun acc x => x :: acc) acc xs = xs.reverse ++ acc by
    simpa using h []
  induction xs with
  | nil       => simp [myFoldl]
  | cons x xs ih =>
    intro acc
    simp [myFoldl, ih, List.reverse_cons, List.append_assoc]

def myConcat (xss : List (List α)) : List α :=
  myFoldr (· ++ ·) [] xss

theorem mapViaFold_correct (f : α → β) (xs : List α) :
    mapViaFold f xs = myMap f xs := by
  induction xs with
  | nil       => rfl
  | cons x xs ih => simp [mapViaFold, myFoldr, myMap, ih]

end Week08
