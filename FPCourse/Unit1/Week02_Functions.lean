-- FPCourse/Unit1/Week02_Functions.lean

/- @@@
## Week 2: Functions, Signatures, and the Substitution Model

### Overview

A function is a value.  This single sentence distinguishes typed functional
programming from most other approaches.

In an imperative language, a function is a *command*: a named sequence of
side-effecting statements.  Here, a function is simply a value whose type
is a *function type* `A → B`.  It can be passed as an argument, returned
as a result, given a name, or left anonymous.  There is nothing special about
it that does not apply equally to a number or a boolean.

This week introduces:
- Function definitions and function types
- The substitution model of evaluation
- Currying and partial application
- The **typed design recipe**: a systematic method for writing functions

The substitution model is not a simplification for beginners — in a pure
language it is the *exact* semantics.  Every function call reduces by
substituting the argument for the parameter in the body.  No variables
change; no memory is allocated; no order of evaluation is ambiguous.
@@@ -/

namespace Week02

/- @@@
### 2.1  Function definitions and function types

A function definition names a function, declares its parameter type and
return type, and provides a body expression.

The type `A → B` is read "A arrow B" and denotes functions from `A` to `B`.
The arrow associates to the right: `A → B → C` means `A → (B → C)`.
@@@ -/

-- A function with an explicit type signature
def double (n : Nat) : Nat := 2 * n

-- The same function, showing the function type at the top level
def double' : Nat → Nat := fun n => 2 * n

-- The two are definitionally equal
example : double = double' := rfl

-- Checking and evaluating
#check double      -- Nat → Nat
#eval double 7     -- 14

/- @@@
### 2.2  The substitution model

To evaluate `double 7`, substitute `7` for `n` in the body `2 * n`:

```
double 7
= 2 * 7         (substitute 7 for n)
= 14            (evaluate 2 * 7)
```

This process — called *β-reduction* — is the entire evaluation rule for
function application.  There are no side effects, no mutable state, no
hidden dependencies.  The value of `double 7` depends only on the
definition of `double` and the value `7`.

**Referential transparency**: replacing any sub-expression with an
extensionally equal expression does not change the value of the whole.
Because `7 = 3 + 4`, we have `double 7 = double (3 + 4)` by substitution.

In Lean we can state referential transparency facts as equalities proved
by `rfl` (reflexivity), which succeeds when both sides evaluate to the
same normal form.
@@@ -/

example : double 7 = 14 := rfl
example : double (3 + 4) = double 7 := rfl   -- both sides = 14

/- @@@
### 2.3  The typed design recipe

Every function should be designed by following these steps *in order*:

1. **Type signature**: state the input and output types.
2. **Purpose statement**: state in one sentence what the output *means*
   relative to the input — not *how* it is computed.
3. **Examples as checked facts**: write concrete input-output pairs as
   `example` statements that Lean verifies.
4. **Body**: implement the function.
5. **Review**: re-read the purpose statement and verify the body matches.

Step 3 is not optional.  Examples are part of the specification;
they document behaviour for cases the type alone does not capture.
@@@ -/

-- Design recipe demonstration: `clamp`
-- 1. Type signature
def clamp (lo hi n : Nat) : Nat :=
-- 4. Body (written after purpose and examples)
  if n < lo then lo
  else if n > hi then hi
  else n
-- 2. Purpose statement:
-- clamp lo hi n = n if lo ≤ n ≤ hi, lo if n < lo, hi if n > hi

-- 3. Examples as checked facts
example : clamp 0 10 5  = 5  := rfl
example : clamp 0 10 15 = 10 := rfl
example : clamp 0 10 0  = 0  := rfl

/- @@@
### 2.4  Currying and partial application

A function of two arguments in Lean is, by default, a *curried* function:
it takes its first argument and returns a function waiting for the second.

```
add : Nat → Nat → Nat
    = Nat → (Nat → Nat)
```

**Partial application**: applying a curried function to fewer arguments
than it expects yields a function of the remaining arguments.
This is not a special feature — it follows directly from the type of
function application.
@@@ -/

def add (m n : Nat) : Nat := m + n

-- add has type Nat → Nat → Nat
#check add        -- Nat → Nat → Nat

-- Partial application: fix m = 3, get a function Nat → Nat
def add3 : Nat → Nat := add 3
#eval add3 7      -- 10
#eval add3 0      -- 3

-- The section notation (· + 3) is sugar for (fun n => n + 3)
def add3' : Nat → Nat := (· + 3)
example : add3 = add3' := rfl

/- @@@
### 2.5  Anonymous functions (lambdas)

A lambda expression `fun x => body` creates an unnamed function.
Lambdas are values exactly like named functions.

Multi-argument lambdas can be written `fun x y => body`
(sugar for `fun x => fun y => body`).
@@@ -/

-- A lambda with no name
#eval (fun n => n * n) 5     -- 25

-- Passing a lambda as an argument
def applyTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
#eval applyTwice (fun n => n + 1) 10   -- 12
#eval applyTwice double 3              -- 12

/- @@@
### 2.6  Function composition

Two functions `f : B → C` and `g : A → B` compose to give a function
`A → C`.  In Lean 4, function composition is written `f ∘ g`
(the `∘` symbol, typed `\circ`).

The composition law states: `(f ∘ g) x = f (g x)`.
This is not just a convenient notation — it will be a key tool for
equational proofs starting in Week 8.
@@@ -/

def square (n : Nat) : Nat := n * n
def increment (n : Nat) : Nat := n + 1

-- Compose: first increment, then square
def squareAfterIncrement : Nat → Nat := square ∘ increment

#eval squareAfterIncrement 4   -- (4+1)² = 25
#eval squareAfterIncrement 0   -- 1

-- The composition law, verified by rfl for concrete inputs
example : (square ∘ increment) 4 = square (increment 4) := rfl

/- @@@
### Exercises

1. Write a function `max2 : Nat → Nat → Nat` using the design recipe:
   state the purpose, write two examples, then provide the body.

2. Write the function `applyThrice : (Nat → Nat) → Nat → Nat` and
   verify that `applyThrice increment 0 = 3`.

3. Express `applyTwice double` as a lambda `fun n => …` without
   using either `applyTwice` or `double` by name.

4. Prove that `increment ∘ double` and `double ∘ increment` are
   *not* equal by finding an input where they differ.  Write an
   `example` using `native_decide` or `rfl` to confirm.
@@@ -/

-- Exercise stubs
def max2 (m n : Nat) : Nat := sorry

example : max2 3 7 = 7 := by sorry
example : max2 9 4 = 9 := by sorry

def applyThrice (f : Nat → Nat) (x : Nat) : Nat := sorry

example : applyThrice increment 0 = 3 := by sorry

-- Counterexample: increment ∘ double ≠ double ∘ increment
example : (increment ∘ double) 1 ≠ (double ∘ increment) 1 := by decide

end Week02
