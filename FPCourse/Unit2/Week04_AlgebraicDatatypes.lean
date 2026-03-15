-- FPCourse/Unit2/Week04_AlgebraicDatatypes.lean

/- @@@
# Unit 2 — Inductive Datatypes and Structural Reasoning

## Week 4: Algebraic Datatypes — Sums, Products, and the Option Type

### Overview

So far we have worked only with built-in types: `Nat`, `Bool`, `String`.
This week we learn to *define our own types* using the `inductive` keyword.

An **inductive type** is defined by listing its *constructors* — the
ways to build a value of that type.  Every value of the type is formed
by exactly one constructor applied to zero or more arguments.

Two fundamental patterns:

- **Sum types** (also called *variant* or *union* types): a value is
  *one of* several alternatives.  Example: a traffic light is Red, Yellow,
  or Green.
- **Product types** (also called *record* types): a value carries *all of*
  several fields simultaneously.  Example: a point has an x-coordinate
  and a y-coordinate.

Lean's `inductive` keyword expresses both patterns (and their combinations).
@@@ -/

namespace Week04

/- @@@
### 4.1  Sum types

A **sum type** lists mutually exclusive alternatives.  Each alternative is
a *constructor* — a function that creates a value of the type.

The key rule: to *use* a value of a sum type, you must handle every
constructor.  Lean enforces this with **exhaustiveness checking**: a
pattern match that omits a constructor is a compile error.
@@@ -/

inductive TrafficLight where
  | red    : TrafficLight
  | yellow : TrafficLight
  | green  : TrafficLight

-- A function over TrafficLight MUST handle all three constructors
def TrafficLight.nextLight : TrafficLight → TrafficLight
  | .red    => .green
  | .yellow => .red
  | .green  => .yellow

#eval TrafficLight.nextLight .red    -- TrafficLight.green
#eval TrafficLight.nextLight .green  -- TrafficLight.yellow

/- @@@
### 4.2  The template principle

A function over a sum type `T` has exactly one case for each constructor
of `T`.  This is not a style guideline — it follows from the definition
of the type.  The *shape of the program* is determined by the *shape of
the data*.

This is the central insight of the HtDP design methodology, now enforced
by the type system:

1. Declare the type.
2. Count the constructors.
3. Write one case per constructor.
4. Fill in each case.

Step 3 is *mechanical*.  You cannot forget a case because the compiler
will tell you.
@@@ -/

inductive Direction where
  | north | south | east | west

def Direction.opposite : Direction → Direction
  | .north => .south
  | .south => .north
  | .east  => .west
  | .west  => .east

-- Proof by case analysis: opposite is an involution
theorem Direction.opposite_involution (d : Direction) :
    d.opposite.opposite = d := by
  cases d <;> rfl

/- @@@
### 4.3  Constructors with data (tagged unions)

Constructors can carry data.  A sum type whose constructors carry different
kinds of data corresponds to a *tagged union* in other languages.

The number of cases in the proof equals the number of constructors.
Each case has access to the data carried by that constructor.
@@@ -/

inductive Shape where
  | circle   : Float → Shape          -- radius
  | rectangle : Float → Float → Shape -- width × height
  | triangle  : Float → Float → Float → Shape  -- three sides

def Shape.perimeter : Shape → Float
  | .circle r         => 2 * Float.pi * r
  | .rectangle w h    => 2 * (w + h)
  | .triangle a b c   => a + b + c

#eval Shape.perimeter (.circle 1.0)          -- 2π ≈ 6.283
#eval Shape.perimeter (.rectangle 3.0 4.0)   -- 14.0
#eval Shape.perimeter (.triangle 3.0 4.0 5.0) -- 12.0

/- @@@
### 4.4  The Option type

The **option type** is one of the most important types in safe programming.
It represents a value that may or may not be present:

```
Option A = | none        (no value)
           | some (a : A)  (a value of type A)
```

`Option A` is the type-safe alternative to null pointers and exceptions
for partial functions.  A function that may fail to produce a result
returns `Option A` instead of `A`.  The caller is *forced* by the type
system to handle both `none` and `some`, preventing null-pointer errors.
@@@ -/

-- Safe division: returns none when divisor is zero
def safeDiv (m n : Nat) : Option Nat :=
  if n = 0 then none else some (m / n)

#eval safeDiv 10 2   -- some 5
#eval safeDiv 10 0   -- none

-- Safe list head
def safeHead : List α → Option α
  | []     => none
  | x :: _ => some x

#eval safeHead [1, 2, 3]   -- some 1
#eval safeHead ([] : List Nat)  -- none

/- @@@
### 4.5  Chaining with Option: the monad pattern

When several operations can each fail, we want to chain them and propagate
failure automatically.  Lean 4 allows `do` notation for `Option`, which
handles this:

- If any step returns `none`, the whole chain returns `none`.
- Otherwise the chain proceeds with the unwrapped values.
@@@ -/

def safeDivTwice (m n p : Nat) : Option Nat := do
  let q ← safeDiv m n   -- fails if n = 0
  let r ← safeDiv q p   -- fails if p = 0
  return r

#eval safeDivTwice 100 5 4   -- some 5
#eval safeDivTwice 100 0 4   -- none
#eval safeDivTwice 100 5 0   -- none

/- @@@
### 4.6  Proof by case analysis on a sum type

To prove a property `P x` for all `x : T` where `T` is a sum type, give
one sub-proof per constructor.  This is **case analysis** — the proof
analogue of pattern matching.

The number of cases in the proof equals the number of constructors in
the type.  This is no coincidence: it is the first glimpse of the
Curry–Howard correspondence.
@@@ -/

-- Every traffic light eventually returns to green after enough steps
-- (We prove the simpler statement: nextLight ∘ nextLight ∘ nextLight = id)
theorem trafficLight_cycle (l : TrafficLight) :
    l.nextLight.nextLight.nextLight = l := by
  cases l <;> rfl

-- Option map: applying a function inside an option
def Option.map' (f : α → β) : Option α → Option β
  | none   => none
  | some x => some (f x)

-- map' preserves identity
theorem Option.map'_id (o : Option α) :
    Option.map' id o = o := by
  cases o <;> rfl

-- map' distributes over composition
theorem Option.map'_comp (f : β → γ) (g : α → β) (o : Option α) :
    Option.map' (f ∘ g) o = Option.map' f (Option.map' g o) := by
  cases o <;> rfl

/- @@@
### Exercises

1. Define an inductive type `Suit` for the four card suits (Clubs,
   Diamonds, Hearts, Spades) and a function `isRed : Suit → Bool`.

2. Define a type `Expr` for arithmetic expressions:
   - A literal natural number
   - The sum of two expressions
   - The product of two expressions
   Then define `eval : Expr → Nat`.

3. Extend `safeDiv` to `Option Int` and prove that
   `safeDiv m n = some q → n * q = m` when `n ≠ 0` and division is exact.

4. Prove that `Option.map' f none = none` and
   `Option.map' f (some x) = some (f x)` hold for any `f`.
@@@ -/

inductive Suit where
  | clubs | diamonds | hearts | spades

def Suit.isRed : Suit → Bool
  | .diamonds | .hearts => true
  | _                   => false

example : Suit.isRed .hearts = true  := rfl
example : Suit.isRed .clubs  = false := rfl

inductive Expr where
  | lit  : Nat → Expr
  | add  : Expr → Expr → Expr
  | mul  : Expr → Expr → Expr

def Expr.eval : Expr → Nat
  | .lit n   => n
  | .add l r => l.eval + r.eval
  | .mul l r => l.eval * r.eval

example : Expr.eval (.add (.lit 2) (.mul (.lit 3) (.lit 4))) = 14 := rfl

end Week04
