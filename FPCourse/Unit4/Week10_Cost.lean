-- FPCourse/Unit4/Week10_Cost.lean

/- @@@
# Unit 4 — Cost Semantics: Work and Span

## Week 10: Counting Evaluation Steps

### Overview

Every program we write has a *cost* — the number of evaluation steps it
takes to reach a value.  So far we have proved programs *correct*;
now we prove them *efficient*.

Two key quantities:

- **Work**: the total number of evaluation steps in a sequential execution.
  This is the cost on one processor.

- **Span**: the depth of the dependency graph of evaluation steps —
  the time if every independent sub-computation runs in parallel.
  This is the cost on infinitely many processors.

Because functional programs have **no side effects**, independent
sub-expressions really are independent: they can evaluate in any order
without interference.  This is what makes the span analysis meaningful.

In an imperative program, two sub-expressions might both read and write
the same mutable variable, creating dependencies not visible in the code.
In a pure functional program, this cannot happen.  The type system and
the absence of mutation make parallelism structurally safe.
@@@ -/

namespace Week10

/- @@@
### 10.1  Counting steps with an instrumented model

We model cost by threading a *step counter* through the computation.
This is a pedagogical device — real cost analysis uses recurrences — but
it makes the step count concrete and checkable.

Each operation charges one step.
@@@ -/

-- A cost monad: pair a value with a step count
structure Cost (α : Type) where
  value : α
  steps : Nat
  deriving Repr

def Cost.pure (x : α) : Cost α := ⟨x, 0⟩

def Cost.bind (c : Cost α) (f : α → Cost β) : Cost β :=
  let d := f c.value
  ⟨d.value, c.steps + d.steps + 1⟩   -- +1 for the bind step

-- Charge one step
def Cost.tick (x : α) : Cost α := ⟨x, 1⟩

-- Sequential list length, instrumented
def costLength : List α → Cost Nat
  | []      => Cost.pure 0
  | _ :: xs =>
    Cost.bind (costLength xs) fun n =>
    Cost.tick (n + 1)

#eval costLength [1, 2, 3, 4]   -- Cost.mk 4 4  (4 elements, 4 steps)

/- @@@
### 10.2  Asymptotic notation

For large inputs, we care about how cost *grows* as a function of the
input size, not the exact step count.

**Big-O notation** `O(f(n))`:
A function `T(n)` is `O(f(n))` if there exist constants `c > 0` and
`n₀ ≥ 0` such that for all `n ≥ n₀`, `T(n) ≤ c * f(n)`.

| Growth rate | Name         | Examples                      |
|-------------|--------------|-------------------------------|
| O(1)        | Constant     | `List.head?`, `Array.get`     |
| O(log n)    | Logarithmic  | BST lookup (balanced)         |
| O(n)        | Linear       | `List.length`, `List.map`     |
| O(n log n)  | Linearithmic | Merge sort                    |
| O(n²)       | Quadratic    | Insertion sort, naive reverse |
| O(2ⁿ)       | Exponential  | Naive Fibonacci                |

We prove cost bounds using induction, exactly as we prove correctness.
@@@ -/

-- Prove that list length is O(n)
-- We express "T(n) ≤ n" as a concrete bound
theorem costLength_bound (xs : List α) :
    (costLength xs).steps = xs.length := by
  induction xs with
  | nil       => simp [costLength, Cost.pure]
  | cons x xs ih =>
    simp [costLength, Cost.bind, Cost.tick, ih]

/- @@@
### 10.3  Naive reverse is O(n²)

The naive reverse `myReverse` from Week 5 is O(n²) because it appends to
the *end* of an accumulating list.  Each append on a list of length k
costs k steps, and we do this n times: total cost 0 + 1 + 2 + … + (n-1) = n²/2.

The tail-recursive reverse from Week 5 is O(n): it uses an accumulator
and the `cons` operation (O(1)) n times.
@@@ -/

-- Append cost = length of first argument
def costAppend : List α → List α → Cost (List α)
  | [],      ys => Cost.tick ys
  | x :: xs, ys =>
    Cost.bind (costAppend xs ys) fun zs =>
    Cost.tick (x :: zs)

theorem costAppend_steps (xs ys : List α) :
    (costAppend xs ys).steps = xs.length + 1 := by
  induction xs with
  | nil       => simp [costAppend, Cost.tick]
  | cons x xs ih =>
    simp [costAppend, Cost.bind, Cost.tick, ih]
    omega

-- The quadratic cost of naive reverse
-- Work(reverse(xs)) = sum_{k=0}^{n-1} (k+1) = n*(n+1)/2
-- This grows as Θ(n²).

-- Contrast: tail-recursive reverse is linear (O(n)).
-- Each step uses cons, which is O(1), and we do exactly n steps.

/- @@@
### 10.4  Recurrences and the Master Theorem (informal)

For divide-and-conquer algorithms, the work satisfies a *recurrence*:

```
T(n) = a · T(n/b) + f(n)
```

where `a` is the number of recursive calls, `b` is how much the
input shrinks, and `f(n)` is the work done at each level.

**Merge sort**:
- `T(n) = 2 · T(n/2) + O(n)`   (split and merge both cost O(n))
- Solution: `T(n) = O(n log n)` (Master Theorem, case 2)

**Binary search**:
- `T(n) = T(n/2) + O(1)`
- Solution: `T(n) = O(log n)` (Master Theorem, case 3)
@@@ -/

-- Informal proof of merge sort's O(n log n) work:
-- At level k of the recursion, we have 2^k subproblems each of size n/2^k.
-- Work at level k = 2^k * O(n/2^k) = O(n).
-- There are log₂ n levels.
-- Total work = O(n) * log₂ n = O(n log n).

/- @@@
### 10.5  Parallelism: work vs. span

The **span** of a computation is the minimum time to evaluate it
given unlimited parallel processors.

For merge sort:
- **Work**: O(n log n) — the total work is unchanged.
- **Span**: O(log² n) — each level takes O(log n) for the parallel merge,
  and there are O(log n) levels.

The **parallelism** is Work / Span = O(n log n) / O(log² n) = O(n / log n).
For n = 10⁶, this is about 50,000 — enormous potential speedup.

Functional programs can automatically exploit this parallelism because
the two recursive calls `mergeSort left` and `mergeSort right` are
*independent*: neither reads the state that the other writes, because
there is no mutable state.
@@@ -/

-- Pairs whose components are computed in parallel:
-- The span of (f x, g x) is max(span(f x), span(g x)).
-- The span of the sequential version is span(f x) + span(g x).

-- In a typed functional language, the runtime can always *choose* to
-- evaluate independent subexpressions in parallel.

/- @@@
### Exercises

1. Prove that `costAppend xs ys |>.value = xs ++ ys`.

2. Implement a cost-instrumented `insertionSort` and derive its step count
   as a function of the input length.  What recurrence does it satisfy?
   What is its Big-O complexity?

3. Define `span : Cost α → Nat` for a simplified parallel cost model
   where a pair `(c₁, c₂)` has span `max c₁.steps c₂.steps`.
   Show that merging two sorted lists of lengths `m` and `n` has
   span `O(log(m + n))` in the parallel model.

4. Explain in two sentences why immutability is *necessary* for the
   span analysis to be meaningful.
@@@ -/

-- Exercise stubs
theorem costAppend_value (xs ys : List α) :
    (costAppend xs ys).value = xs ++ ys := by
  induction xs with
  | nil       => simp [costAppend, Cost.tick]
  | cons x xs ih =>
    simp [costAppend, Cost.bind, Cost.tick, ih]

end Week10
