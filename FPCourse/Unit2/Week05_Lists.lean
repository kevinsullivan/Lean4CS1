-- FPCourse/Unit2/Week05_Lists.lean

/- @@@
## Week 5: Inductive Types — Lists and Structural Induction

### Overview

The list is the canonical inductive type.  It is defined by exactly two
constructors:
- `nil`  — the empty list
- `cons` — a head element prepended to a tail list

This recursive definition (a `cons` cell contains a *smaller* list) is
why functions over lists are naturally recursive and why proofs about lists
naturally proceed by induction.

**Structural recursion**: a function over a list recurs on the *tail*,
which is structurally smaller.  Termination is guaranteed automatically.

**Structural induction**: a proof about all lists proceeds by:
1. Proving the property for `[]` (the base case).
2. Proving that if the property holds for `xs` (IH), it holds for `x :: xs`.

The IH corresponds *exactly* to the recursive call in the program.
Citing the IH in a proof is the same act as trusting the recursive call
in the program.
@@@ -/

namespace Week05

/- @@@
### 5.1  Defining lists

Lean 4 has a built-in `List α` type.  For exposition, here is its
definition written out explicitly:

```lean
inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α
```

We use the built-in `List α` (with notation `[]` and `x :: xs`) throughout.
@@@ -/

-- The template for a function over List α:
-- one case for nil, one case for cons.
def myLength : List α → Nat
  | []      => 0
  | _ :: xs => 1 + myLength xs

#eval myLength [1, 2, 3, 4]   -- 4
#eval myLength ([] : List Nat) -- 0

-- Append: join two lists
def myAppend : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: myAppend xs ys

#eval myAppend [1, 2] [3, 4]   -- [1, 2, 3, 4]

-- Reverse: reverse a list
def myReverse : List α → List α
  | []      => []
  | x :: xs => myReverse xs ++ [x]

#eval myReverse [1, 2, 3]   -- [3, 2, 1]

/- @@@
### 5.2  Algebraic specifications

Before proving theorems, we write *algebraic specifications*:
equations that must hold between functions.  These equations are
simultaneously (a) part of the specification and (b) the code itself
(for base cases).

Key specification for `myAppend`:
- `myAppend [] ys = ys`
- `myAppend (x :: xs) ys = x :: myAppend xs ys`

These hold by `rfl` — they are the *definition* of `myAppend`.
The non-trivial algebraic property is the *length* equation.
@@@ -/

-- Specification: length distributes over append
theorem myLength_append (xs ys : List α) :
    myLength (myAppend xs ys) = myLength xs + myLength ys := by
  induction xs with
  | nil        => simp [myLength, myAppend]
  | cons x xs ih =>
    -- myLength (x :: xs ++ ys)
    -- = 1 + myLength (xs ++ ys)     by def of myLength
    -- = 1 + (myLength xs + myLength ys)  by IH
    -- = (1 + myLength xs) + myLength ys  by Nat arithmetic
    -- = myLength (x :: xs) + myLength ys by def of myLength
    simp [myLength, myAppend, ih]
    omega

/- @@@
### 5.3  A more challenging proof: reverse reverses

`myReverse (myReverse xs) = xs` for all `xs`.

The direct induction does not work easily because the inductive step
has `myReverse (xs ++ [x])` which needs a *helper lemma* about how
`myReverse` interacts with `myAppend`.

This pattern — proving a *stronger* or *more general* statement to make
the induction go through — recurs throughout the course.
@@@ -/

-- Helper lemma: reverse of an append
theorem myReverse_append (xs ys : List α) :
    myReverse (myAppend xs ys) = myAppend (myReverse ys) (myReverse xs) := by
  induction xs with
  | nil        => simp [myReverse, myAppend]
  | cons x xs ih =>
    simp [myAppend, myReverse, ih]
    -- need: (reverse ys ++ reverse xs) ++ [x]
    --     = reverse ys ++ (reverse xs ++ [x])
    -- this is associativity of myAppend
    induction myReverse ys with
    | nil        => simp [myAppend]
    | cons y ys' ih2 => simp [myAppend, ih2]

-- Main theorem: reverse is an involution
theorem myReverse_reverse (xs : List α) :
    myReverse (myReverse xs) = xs := by
  induction xs with
  | nil        => rfl
  | cons x xs ih =>
    simp [myReverse, myReverse_append, ih, myAppend]

/- @@@
### 5.4  More list operations

The design recipe guides us to implement common list operations.
Each comes with its algebraic specification.
@@@ -/

-- Take the first n elements
def myTake : Nat → List α → List α
  | 0,     _      => []
  | _,     []     => []
  | n + 1, x :: xs => x :: myTake n xs

-- Drop the first n elements
def myDrop : Nat → List α → List α
  | 0,     xs      => xs
  | _,     []      => []
  | n + 1, _ :: xs => myDrop n xs

#eval myTake 3 [1, 2, 3, 4, 5]   -- [1, 2, 3]
#eval myDrop 3 [1, 2, 3, 4, 5]   -- [4, 5]

-- Specification: take and drop partition the list
theorem take_drop_append (n : Nat) (xs : List α) :
    myAppend (myTake n xs) (myDrop n xs) = xs := by
  induction n generalizing xs with
  | zero      => simp [myTake, myDrop, myAppend]
  | succ n ih =>
    cases xs with
    | nil        => simp [myTake, myDrop, myAppend]
    | cons x xs  => simp [myTake, myDrop, myAppend, ih]

-- Membership predicate
def myMem (a : α) [DecidableEq α] : List α → Bool
  | []      => false
  | x :: xs => x == a || myMem a xs

#eval myMem 3 [1, 2, 3, 4]   -- true
#eval myMem 5 [1, 2, 3, 4]   -- false

/- @@@
### 5.5  Lengths and sizes

Several properties connect the length of a list to operations on it.
These make good induction exercises because the proofs closely mirror
the definitions.
@@@ -/

@[simp]
theorem myLength_nil : myLength ([] : List α) = 0 := rfl

@[simp]
theorem myLength_cons (x : α) (xs : List α) :
    myLength (x :: xs) = 1 + myLength xs := rfl

theorem myLength_reverse (xs : List α) :
    myLength (myReverse xs) = myLength xs := by
  induction xs with
  | nil       => rfl
  | cons x xs ih =>
    simp [myReverse, myLength_append, ih, myLength]
    omega

/- @@@
### Exercises

1. Implement `myZip : List α → List β → List (α × β)` that pairs
   corresponding elements.  When the lists have different lengths,
   stop at the shorter one.  Verify `myZip [1,2,3] ["a","b"] = [(1,"a"),(2,"b")]`.

2. Prove `myLength (myTake n xs) ≤ n` for all `n` and `xs`.

3. Implement tail-recursive reverse using an accumulator and prove
   it equal to `myReverse`.

4. Prove `myMem x (myAppend xs ys) = (myMem x xs || myMem x ys)`
   for all `xs`, `ys`, and `x`.
@@@ -/

-- Exercise stubs
def myZip : List α → List β → List (α × β)
  | [],      _       => []
  | _,       []      => []
  | x :: xs, y :: ys => (x, y) :: myZip xs ys

example : myZip [1, 2, 3] ["a", "b"] = [(1, "a"), (2, "b")] := rfl

theorem myLength_take_le (n : Nat) (xs : List α) :
    myLength (myTake n xs) ≤ n := by
  induction n generalizing xs with
  | zero      => simp [myTake, myLength]
  | succ n ih =>
    cases xs with
    | nil       => simp [myTake, myLength]
    | cons x xs => simp [myTake, myLength, ih]; omega

def myReverseAcc : List α → List α → List α
  | [],      acc => acc
  | x :: xs, acc => myReverseAcc xs (x :: acc)

def myReverseTR (xs : List α) : List α := myReverseAcc xs []

theorem myReverseAcc_spec (xs acc : List α) :
    myReverseAcc xs acc = myAppend (myReverse xs) acc := by
  induction xs generalizing acc with
  | nil       => simp [myReverseAcc, myReverse, myAppend]
  | cons x xs ih =>
    simp [myReverseAcc, myReverse, ih]
    induction myReverse xs with
    | nil        => simp [myAppend]
    | cons y ys' ih2 => simp [myAppend, ih2]

theorem myReverseTR_correct (xs : List α) :
    myReverseTR xs = myReverse xs := by
  simp [myReverseTR, myReverseAcc_spec, myAppend]
  induction myReverse xs with
  | nil       => rfl
  | cons _ _ _ => simp [myAppend]

end Week05
