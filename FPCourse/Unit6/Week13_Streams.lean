-- FPCourse/Unit6/Week13_Streams.lean

/- @@@
# Unit 6 — Lazy Evaluation, Streams, and Synthesis

## Week 13: Infinite Structures and Coinductive Reasoning

### Overview

Every type we have defined so far has been **inductive**: its values are
*built up* from constructors applied to strictly smaller pieces.  An
inductive type is always *finite*.

This week introduces **coinductive** types: types defined by their
*observable behaviour* rather than their construction.  A coinductive value
is characterised by what you see when you *take it apart* — not by how
it was put together.  A coinductive value can be **infinite**.

The running example is the **stream**: a potentially infinite sequence.
A stream of `α` values is not built from the empty stream the way a list is;
instead, it is characterised by:
- `head : α` — the first element
- `tail : Stream' α` — the rest of the stream (another stream)

Lean 4 allows productive corecursion on such types, using `Thunk` to
delay evaluation.

**The duality**:
- Induction reasons about *finite* data by building up from the base case.
- Coinduction reasons about *infinite* data by observing from the outside.
@@@ -/

namespace Week13

/- @@@
### 13.1  Thunks: delaying evaluation

Lean 4 is *strictly evaluated* (call-by-value): all arguments are evaluated
before being passed to a function.  To build infinite structures, we need
to *delay* evaluation of the tail.

A **thunk** is a suspended computation: a function from `Unit` to `α` that
produces a value of type `α` only when *forced* (called with `()`).

Lean 4 has a built-in `Thunk α` type.  We use it directly.
@@@ -/

-- Force a thunk
def Thunk.force (t : Thunk α) : α := t.get

-- Delay a value (wrap in a thunk)
def Thunk.delay (x : α) : Thunk α := Thunk.mk (fun () => x)
def Thunk.delay' (f : Unit → α) : Thunk α := Thunk.mk f

/- @@@
### 13.2  Streams via thunks

We define a *lazy list* (stream) using a `Thunk` for the tail.
The `Thunk` breaks the strict positivity requirement that would otherwise
prevent the inductive definition — the tail is not evaluated eagerly.
@@@ -/

inductive LList (α : Type) where
  | nil  : LList α
  | cons : α → Thunk (LList α) → LList α

-- Produce the first n elements as a regular List
def LList.take : Nat → LList α → List α
  | 0,     _           => []
  | _,     .nil        => []
  | n + 1, .cons x xs  => x :: xs.get.take n

-- The infinite stream of ones: 1, 1, 1, ...
def ones : LList Nat :=
  .cons 1 (.mk fun () => ones)

#eval ones.take 5    -- [1, 1, 1, 1, 1]

-- The natural numbers: 0, 1, 2, ...
def natsFrom (n : Nat) : LList Nat :=
  .cons n (.mk fun () => natsFrom (n + 1))

def nats : LList Nat := natsFrom 0

#eval nats.take 8    -- [0, 1, 2, 3, 4, 5, 6, 7]

/- @@@
### 13.3  Stream operations

We can define `map`, `filter`, `zip`, and other operations on streams.
Each operation preserves the lazy character: it does not force more of
the stream than necessary.
@@@ -/

def LList.map (f : α → β) : LList α → LList β
  | .nil        => .nil
  | .cons x xs  => .cons (f x) (.mk fun () => xs.get.map f)

def LList.zip : LList α → LList β → LList (α × β)
  | .nil,       _            => .nil
  | _,          .nil         => .nil
  | .cons x xs, .cons y ys   =>
    .cons (x, y) (.mk fun () => xs.get.zip ys.get)

-- zipWith: element-wise application
def LList.zipWith (f : α → β → γ) : LList α → LList β → LList γ
  | .nil,       _            => .nil
  | _,          .nil         => .nil
  | .cons x xs, .cons y ys   =>
    .cons (f x y) (.mk fun () => xs.get.zipWith f ys.get)

-- Fibonacci as a stream: fib n = fib (n-1) + fib (n-2)
-- fibs = [0, 1, 1, 2, 3, 5, 8, 13, ...]
def fibs : LList Nat :=
  let rec go (a b : Nat) : LList Nat :=
    .cons a (.mk fun () => go b (a + b))
  go 0 1

#eval fibs.take 10   -- [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]

/- @@@
### 13.4  Memoisation

A *memoised* function computes each result at most once, caching the
value in a table for future use.

The classic example: the naive recursive Fibonacci is O(2ⁿ) because
it recomputes the same values repeatedly.  The stream-based Fibonacci
above is O(n) because each value is computed once from the previous two.

We can also build an explicit memo table:
@@@ -/

-- Memoised Fibonacci using an Array as a cache
def fibMemo (n : Nat) : Nat :=
  let rec fill (arr : Array Nat) (i : Nat) : Array Nat :=
    if i > n then arr
    else
      let v := if i ≤ 1 then i
               else arr[i - 2]! + arr[i - 1]!
      fill (arr.push v) (i + 1)
  let arr := fill #[] 0
  arr[n]!

#eval fibMemo 40    -- 102334155 (computed in O(n))

/- @@@
### 13.5  Bisimulation: coinductive reasoning

Two streams are **bisimilar** if they have the same head and their tails
are bisimilar.  Bisimilarity is the coinductive counterpart of equality.

To prove that two stream definitions produce the same stream, we show
they are bisimilar: at every position, they produce the same element.

We express this using the standard equality on the result of `take`:
if two streams agree on every finite prefix, they are equal.
@@@ -/

-- Two streams are equivalent if they agree on every finite prefix
def StreamEq (s₁ s₂ : LList α) : Prop :=
  ∀ n, s₁.take n = s₂.take n

-- Prove that two definitions of nats are equivalent
def natsAlt : LList Nat :=
  LList.zipWith (· + ·)
    (LList.map (2 * ·) nats)
    (LList.map (2 * · + 1) nats) |>.map (· / 2)

-- (This is a contrived example; in practice bisimulation proofs are
--  more subtle and may require coinduction principles.)

/- @@@
### 13.6  The sieve of Eratosthenes

A classic stream program: generate all prime numbers using the sieve.
The stream is infinite but each element is computed on demand.
@@@ -/

def sieve : LList Nat → LList Nat
  | .nil        => .nil
  | .cons p xs  =>
    .cons p (.mk fun () =>
      sieve (LList.filter (fun n => n % p != 0) xs.get))

-- Filter for lazy lists
def LList.filter (p : α → Bool) : LList α → LList α
  | .nil        => .nil
  | .cons x xs  =>
    if p x then .cons x (.mk fun () => xs.get.filter p)
    else xs.get.filter p

def primes : LList Nat := sieve (natsFrom 2)

-- Note: sieve can be slow due to repeated filtering;
-- this is the pedagogically clear version, not the optimised one.
#eval primes.take 10   -- [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

/- @@@
### Exercises

1. Implement `LList.drop : Nat → LList α → LList α` and
   `LList.nth : Nat → LList α → Option α`.
   Verify `(nats.nth n) = some n` for small `n`.

2. Implement a lazy `LList.merge` that interleaves two streams,
   alternating elements.  Apply it to create a stream of all
   non-negative integers in the order 0, 1, -1, 2, -2, … (as Int).

3. Prove that `(LList.map f s).take n = (s.take n).map f`
   for all streams `s`, functions `f`, and natural numbers `n`.

4. Implement a memoised version of the function that counts the number
   of ways to make change for `n` cents using 1, 5, 10, and 25 cent coins.
   Compare the running time of the memoised and naive versions for `n = 200`.
@@@ -/

-- Exercise stubs
def LList.drop : Nat → LList α → LList α
  | 0,     s            => s
  | _,     .nil         => .nil
  | n + 1, .cons _ xs   => xs.get.drop n

def LList.nth (n : Nat) (s : LList α) : Option α :=
  match s.drop n with
  | .nil       => none
  | .cons x _  => some x

theorem map_take (f : α → β) (s : LList α) (n : Nat) :
    (s.map f).take n = (s.take n).map f := by
  induction n generalizing s with
  | zero      => rfl
  | succ n ih =>
    cases s with
    | nil        => rfl
    | cons x xs  => simp [LList.map, LList.take, ih]

end Week13
