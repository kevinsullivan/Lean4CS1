-- FPCourse/Unit1/Week03_RecursionInduction.lean

/- @@@
## Week 3: Recursion, Totality, and Mathematical Induction

### Overview

Recursion is the primary mechanism for iteration in typed functional
programming.  There are no `while` loops, no `for` loops — only functions
that call themselves on structurally smaller inputs.

This week introduces three tightly linked ideas:

1. **Recursive definitions**: functions whose bodies mention themselves.
2. **Totality**: the guarantee that a function terminates for every input.
3. **Mathematical induction**: the proof technique that corresponds, point
   for point, to recursive definition.

The correspondence is not accidental.  A proof by induction and a
recursive function over natural numbers are the same object viewed from
two perspectives.  Recognising this is the first step toward understanding
the Curry–Howard correspondence that closes the course in Week 14.
@@@ -/

namespace Week03

/- @@@
### 3.1  Recursive functions

A recursive definition is one whose body mentions the function being defined.
Lean requires every recursive function to be **total**: for every input of
the correct type, it must terminate and return a value.

Lean enforces this by checking that every recursive call is on a
*structurally smaller* argument.  For natural numbers, "smaller" means
closer to zero: `n` is structurally smaller than `n + 1`.
@@@ -/

-- Factorial: recursive on the natural number argument
def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 0   -- 1
#eval factorial 5   -- 120
#eval factorial 10  -- 3628800

-- Sum of a list of naturals
def sumList : List Nat → Nat
  | []      => 0
  | x :: xs => x + sumList xs

#eval sumList [1, 2, 3, 4, 5]   -- 15

/- @@@
### 3.2  Totality

A function is **total** if it terminates and returns a value of the
declared type for *every* input.  A function is **partial** if it may
fail to terminate or raise an error on some inputs.

In Lean, all definitions are total by default.  The compiler rejects
any recursive definition it cannot verify terminates.

The termination argument for `factorial n` is: the recursive call is
on `n`, which is strictly less than `n + 1`.  Since natural numbers
are bounded below by zero, this descent must terminate.

Lean checks this automatically for *structural recursion* on inductive
types.  For more complex recursion patterns, we supply an explicit
`termination_by` clause naming a decreasing measure.
@@@ -/

-- An explicit termination measure (not needed here, shown for illustration)
def factorial' (n : Nat) : Nat :=
  match n with
  | 0     => 1
  | n + 1 => (n + 1) * factorial' n
termination_by n

/- @@@
### 3.3  Tail recursion and accumulators

The definition of `factorial` above is *not* tail-recursive: after the
recursive call to `factorial n` returns, there is still a multiplication
to perform.  This means the call stack grows in proportion to `n`.

A call is in **tail position** if its result is the final value of the
enclosing expression — nothing more needs to be done after it.
Tail-recursive functions consume constant stack space because the compiler
can reuse the current stack frame.

To make `factorial` tail-recursive, we introduce an **accumulator**:
an extra parameter that carries the running result.
@@@ -/

def factorialAcc (n : Nat) (acc : Nat) : Nat :=
  match n with
  | 0     => acc
  | n + 1 => factorialAcc n ((n + 1) * acc)

-- The public interface hides the accumulator
def factorialTR (n : Nat) : Nat := factorialAcc n 1

#eval factorialTR 10   -- 3628800

/- @@@
### 3.4  Mathematical induction

To prove a property `P n` holds for every natural number `n`, it suffices
to show:

1. **Base case**: `P 0` holds.
2. **Inductive step**: for every `k`, if `P k` holds (the *inductive
   hypothesis*, abbreviated IH), then `P (k + 1)` holds.

The critical observation: the proof structure mirrors the program structure.

- The base case of the proof ↔ the base case of the recursive function.
- The inductive step ↔ the recursive case.
- The inductive hypothesis ↔ the recursive call (which is trusted to
  return a correct result for the smaller input).

In Lean, the `induction` tactic implements this proof strategy.
@@@ -/

-- Theorem: 0 + n = n for all n : Nat
-- (This is not trivial by rfl because Nat.add is defined by recursion
-- on the *second* argument, so n + 0 = n is rfl but 0 + n needs proof.)
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero      =>
    -- Base case: 0 + 0 = 0
    rfl
  | succ n ih =>
    -- Inductive step: assume 0 + n = n (ih),
    -- prove 0 + (n + 1) = n + 1
    -- Lean knows: 0 + (n + 1) = (0 + n) + 1  by definition of +
    -- By ih:                    = n + 1         ✓
    simp [Nat.add_succ, ih]

/- @@@
### 3.5  Proving accumulator correctness

The tail-recursive `factorialAcc` is only useful if it computes the same
result as the direct `factorial`.  This requires a proof.

The key insight: `factorialAcc n acc = factorial n * acc`.
We prove this by induction on `n`, with the IH being the instance
of this equation for `n` (one step smaller).
@@@ -/

theorem factorialAcc_spec (n acc : Nat) :
    factorialAcc n acc = factorial n * acc := by
  induction n generalizing acc with
  | zero =>
    -- factorialAcc 0 acc = acc = 1 * acc = factorial 0 * acc
    simp [factorialAcc, factorial]
  | succ n ih =>
    -- factorialAcc (n+1) acc
    -- = factorialAcc n ((n+1) * acc)         by def of factorialAcc
    -- = factorial n * ((n+1) * acc)           by IH
    -- = (n+1) * factorial n * acc             by arithmetic
    -- = factorial (n+1) * acc                 by def of factorial
    simp [factorialAcc, factorial, ih]
    ring

-- Corollary: factorialTR agrees with factorial
theorem factorialTR_correct (n : Nat) : factorialTR n = factorial n := by
  simp [factorialTR, factorialAcc_spec, factorial]

/- @@@
### 3.6  A classic induction: sum of the first n naturals

The formula `1 + 2 + … + n = n * (n + 1) / 2` is a standard induction
exercise.  We state it using integer arithmetic to avoid division.

Note how the proof exactly mirrors the recursive definition of `sumTo`.
@@@ -/

def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sumTo n

theorem sumTo_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero      => rfl
  | succ n ih =>
    -- 2 * sumTo (n+1)
    -- = 2 * ((n+1) + sumTo n)         by def
    -- = 2*(n+1) + 2*sumTo n           distribute
    -- = 2*(n+1) + n*(n+1)             by IH
    -- = (n+1)*(2 + n)                 factor
    -- = (n+1)*(n+2)                   rearrange
    simp [sumTo]
    omega

/- @@@
### Exercises

1. Define `fibonacci : Nat → Nat` with `fibonacci 0 = 0`,
   `fibonacci 1 = 1`, `fibonacci (n+2) = fibonacci (n+1) + fibonacci n`.
   Verify: `fibonacci 10 = 55`.

2. Define a tail-recursive `sumListTR` using an accumulator and prove
   it equal to `sumList` from Week 3.

3. Prove by induction: `sumList [0, 1, …, n] = sumTo n`.
   (Hint: you will need a helper lemma about `List.range`.)

4. Prove: `factorial n ≥ 1` for all `n : Nat`.
   (Hint: use `induction` and `omega`.)
@@@ -/

-- Exercise stubs
def fibonacci : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fibonacci (n + 1) + fibonacci n

example : fibonacci 10 = 55 := by native_decide

def sumListAcc : List Nat → Nat → Nat
  | [],      acc => acc
  | x :: xs, acc => sumListAcc xs (acc + x)

def sumListTR (xs : List Nat) : Nat := sumListAcc xs 0

theorem sumListTR_correct (xs : List Nat) :
    sumListTR xs = sumList xs := by
  suffices h : ∀ acc, sumListAcc xs acc = sumList xs + acc by
    simp [sumListTR, h]
  induction xs with
  | nil => simp [sumListAcc, sumList]
  | cons x xs ih =>
    intro acc
    simp [sumListAcc, sumList, ih]
    omega

theorem factorial_pos (n : Nat) : factorial n ≥ 1 := by
  induction n with
  | zero      => simp [factorial]
  | succ n ih => simp [factorial]; omega

end Week03
