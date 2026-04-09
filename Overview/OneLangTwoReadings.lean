-- Overview/OneLangTwoReadings.lean
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Basic

/-! @@@
# One Language, Two Readings

## Reasoning and Computation

The same six type constructors build all data structures in computing
AND express all of propositional logic.

| Constructor | Computation | Logic |
|---|---|---|
| Basic type | Atomic data (`Nat`, `Bool`) | Atomic proposition (`P`, `Q`) |
| `α → β` | Function from `α` to `β` | Implication `P → Q`; Universal `∀ x : α, P x` |
| `α × β` | Pair of `α` and `β` | Conjunction: `P ∧ Q` |
| `α ⊕ β` | Choice of `α` or `β` | Disjunction: `P ∨ Q` |
| `Empty` | Uninhabitable type | Falsity: `False` |
| `α → Empty` | `α` is uninhabitable | Negation: `¬P` (i.e., `P → False`) |

We walk through this table one row at a time.  Each row gets: what it
computes, what it proves, and real Lean code for both.

Our running examples:

- *"If it's raining, the ground is wet."*
- *"If n is a positive even, then n = 2 or n > 2 — and n is
  definitely not a unicorn."*
@@@ -/

namespace Overview

-- ============================================================

/-! @@@
## 1  Basic Types

### Atomic data, atomic propositions

In computation, basic types are your raw materials.  In logic, they are
atomic claims — true or false, no internal structure.
@@@ -/

-- Computation: basic types hold data
#eval 2 + 3              -- 5
#eval "rain" ++ "drop"   -- "raindrop"
#eval true && false       -- false

-- Logic: basic propositions are claims
#check (by decide : 2 + 3 = 5)        -- a proof that 2 + 3 = 5
#check (by decide : "rain".length = 4) -- a proof about strings

/-! @@@
`#eval` runs the reduction machine.  `by decide` runs the same machine
and packages the result as a proof.

### Setting up the running examples
@@@ -/

-- Model "raining" and "ground is wet" as simple propositions
def Raining : Prop := True    -- let's say it is raining today
def GroundWet : Prop := True  -- and the ground is indeed wet

-- Model our number example
def isEven (n : Nat) : Bool := n % 2 == 0
def isPositive (n : Nat) : Bool := n > 0

#eval isEven 6        -- true
#eval isPositive 6    -- true
#eval isEven 3        -- false

/-! @@@
These are the atoms.  Now we connect them.
@@@ -/

-- ============================================================

/-! @@@
## 2  The Arrow: Functions and Implication

### `α → β` — computation is function, logic is implication
@@@ -/

-- Computation: a function takes input, returns output
def double : Nat → Nat := fun n => n * 2
#eval double 21   -- 42

-- Logic: "if it's raining, the ground is wet"
-- A proof of P → Q is a function from proofs of P to proofs of Q
theorem rain_means_wet : Raining → GroundWet :=
  fun _ => trivial   -- given any proof of Raining, produce a proof of GroundWet

/-! @@@
The `→` is the same symbol in both.  A function IS an implication
proof.  That is not a metaphor.

### `∀` is also `→`
@@@ -/

-- "For all n, double n = n + n" is a function that takes any n
-- and returns a proof for that specific n
theorem double_spec : ∀ n : Nat, double n = n + n := by
  intro n; simp [double]; omega

-- Concrete verification
#check (by decide : double 21 = 42)

-- Universal over Bool: decide handles finite domains
#check (by decide : ∀ b : Bool, b || true = true)

/-! @@@
`∀ n : Nat, P n` is definitionally `(n : Nat) → P n`.  A proof of a
universal IS a function.
@@@ -/

-- ============================================================

/-! @@@
## 3  Products: Pairs and Conjunction

### `α × β` — bundling two things
@@@ -/

-- Computation: a pair carries two values at once
def weather : String × Bool := ("rainy", true)
#eval weather.1   -- "rainy"
#eval weather.2   -- true

-- A function that returns two things about a number
def evenAndPositive (n : Nat) : Bool × Bool :=
  (isEven n, isPositive n)

#eval evenAndPositive 6   -- (true, true)
#eval evenAndPositive 0   -- (true, false)

/-! @@@
### `P ∧ Q` — proving two things at once

| Data | Logic |
|------|-------|
| `(a, b) : α × β` | `pf : P ∧ Q` |
| `.1` / `.2` | `.left` / `.right` |

Same constructor.  Two readings.
@@@ -/

-- Logic: "6 is even AND 6 is positive"
-- To prove P ∧ Q, supply a proof of P and a proof of Q
#check (by decide : 6 % 2 = 0 ∧ 6 > 0)

-- Extract each half
theorem six_even : 6 % 2 = 0 ∧ 6 > 0 → 6 % 2 = 0 :=
  fun h => h.left

theorem six_pos : 6 % 2 = 0 ∧ 6 > 0 → 6 > 0 :=
  fun h => h.right

-- ============================================================

/-! @@@
## 4  Sums: Choice and Disjunction

### `α ⊕ β` — one or the other
@@@ -/

-- Computation: a value of α ⊕ β is either a left α or a right β
-- "Is 6 small (≤ 2) or big (> 2)?"
def classify (n : Nat) : String ⊕ Nat :=
  if n ≤ 2 then Sum.inl "small" else Sum.inr n

#eval classify 2   -- Sum.inl "small"
#eval classify 6   -- Sum.inr 6

-- To use a sum, you must do case analysis: handle both alternatives
def describeSize (v : String ⊕ Nat) : String :=
  match v with
  | Sum.inl s => s              -- left case: got a String
  | Sum.inr n => s!"big: {n}"   -- right case: got a Nat

#eval describeSize (classify 2)   -- "small"
#eval describeSize (classify 6)   -- "big: 6"

/-! @@@
To use a sum, you must handle both cases — the compiler enforces
exhaustiveness.

### `P ∨ Q` — proving at least one

| Data | Logic |
|------|-------|
| `Sum.inl a` | `Or.inl hp : P ∨ Q` |
| `Sum.inr b` | `Or.inr hq : P ∨ Q` |
| Exhaustive `match` | Case analysis on a proof |
@@@ -/

-- Logic: "6 = 2 OR 6 > 2" — commit to the true side
theorem six_big : 6 = 2 ∨ 6 > 2 :=
  Or.inr (by decide)    -- we pick the right side: 6 > 2

-- To USE a disjunction, do case analysis: handle both alternatives
theorem even_pos_classify (n : Nat)
    (h : n = 2 ∨ n > 2) : n ≥ 2 :=
  match h with
  | Or.inl heq => by omega   -- left case: n = 2, so n ≥ 2
  | Or.inr hgt => by omega   -- right case: n > 2, so n ≥ 2

-- ============================================================

/-! @@@
## 5  Empty and Negation: Falsity and Impossibility

### `Empty` / `False` — the type with nothing inside
@@@ -/

-- Computation: Empty has no constructors — no value can be produced
-- A function from Empty can promise any return type (it is never called)
def fromVoid : Empty → Nat := fun e => nomatch e

-- Logic: False has no proofs
-- From a proof of False you can derive anything
theorem explosion : False → 6 = 7 := fun h => nomatch h

/-! @@@
Zero-case pattern match = "there are no cases to consider."  This is
*ex falso quodlibet*: from impossibility, anything.

### `¬P` is `P → False` — negation is a function type
@@@ -/

-- Computation: "is n a unicorn?" — there are no unicorns
inductive Unicorn : Type where   -- no constructors!

def notAUnicorn (_ : Nat) : Unicorn → False :=
  fun u => nomatch u

-- Logic: "6 is NOT odd" means "6 is odd → False"
#check (by decide : ¬ (6 % 2 = 1))   -- ¬P is P → False

/-! @@@
Negation is not a primitive.  It is the arrow to the empty type.  The
sixth constructor is just the first and fifth combined.

### The running example, completed

"If 6 is a positive even, then (6 = 2 ∨ 6 > 2) ∧ ¬ Unicorn."

That is: implication, conjunction, disjunction, negation — four rows
of the master table in one proposition.
@@@ -/

theorem the_running_example
    (_ : 6 % 2 = 0 ∧ 6 > 0) : (6 = 2 ∨ 6 > 2) ∧ (Unicorn → False) :=
  ⟨Or.inr (by decide), fun u => nomatch u⟩

-- ============================================================

/-! @@@
## 6  Recursion and Higher-Order Functions

### Recursion = Induction
@@@ -/

-- Computation: structural recursion follows the inductive type
def sum : List Nat → Nat
  | []     => 0
  | h :: t => h + sum t

#eval sum [1, 2, 3, 4]   -- 10

/-! @@@
| Computation | Logic |
|---|---|
| Base: `f [] = ...` | Prove `P []` |
| Step: `f (h :: t)` uses `f t` | From `P t`, prove `P (h :: t)` |

Same structure.  You do not write induction proofs in this course —
but every recursive function you write IS one.

### Higher-order functions = higher-order proof combinators
@@@ -/

-- map applies a function to every element
#eval List.map (· * 2) [1, 2, 3]            -- [2, 4, 6]

-- filter keeps elements satisfying a predicate
#eval List.filter (· % 2 == 0) [1, 2, 3, 4] -- [2, 4]

-- fold collapses a list: iterated function application
#eval List.foldl (· + ·) 0 [1, 2, 3, 4]     -- 10

/-! @@@
| Computational law | Logical reading |
|---|---|
| `map f` | Apply implication `P → Q` uniformly across a collection |
| `fold f init` | Chain inference steps from a base fact: iterated modus ponens |

Higher-order functions correspond to proofs of propositions that take
and return proofs of implications as arguments.
@@@ -/

-- ============================================================

/-! @@@
## 7  Specifications and the Verification Ladder

The design recipe: write the spec BEFORE the implementation.
@@@ -/

def absDiff (a b : Nat) : Nat := if a ≥ b then a - b else b - a

/-! @@@
The verification ladder — each rung is strictly stronger:

| Rung | What it checks |
|------|----------------|
| `#eval` | Spot-check one example |
| `rfl` | Exact definitional equality |
| `decide` | Decision procedure over decidable domains |
| `theorem` | Kernel-verified proof over ALL inputs |
@@@ -/

-- Rung 1: spot check
#eval absDiff 5 3                                    -- 2

-- Rung 2: exact equality
#check (rfl : absDiff 5 3 = 2)

-- Rung 3: decision procedure
#check (by decide : absDiff 5 3 = 2)

-- Rung 4: universally quantified theorem
theorem absDiff_comm (a b : Nat) :
    absDiff a b = absDiff b a := by
  simp only [absDiff]; split <;> split <;> omega

/-! @@@
A correct program is a proof of its specification.  The type checker
verifies both at once.
@@@ -/

-- ============================================================

/-! @@@
## 8  The Curry-Howard Correspondence

Return to the master table — now every row has been lived:

| Constructor | Computation | Logic | You saw it as... |
|---|---|---|---|
| Basic | `Nat`, `Bool` | `P`, `Q` | `isEven`, `isPositive` |
| `α → β` | `double` | `Raining → GroundWet`; `∀ n, ...` | Function = implication |
| `α × β` | `evenAndPositive` | `6 % 2 = 0 ∧ 6 > 0` | Pair = conjunction |
| `α ⊕ β` | `classify` | `6 = 2 ∨ 6 > 2` | Case analysis = disjunction |
| `Empty` | `fromVoid` | `False` | Zero cases = explosion |
| `α → Empty` | `notAUnicorn` | `¬(6 % 2 = 1)` | Arrow to void = negation |

**One language.  Two readings.  No analogy.**

The Curry-Howard correspondence is not something you learn at the end.
It is what the entire course has been all along.  Lean does not
*implement* this correspondence — Lean IS a system in which it is the
foundational design principle.

*What comes next:* this course uses `by decide` to produce proofs
automatically.  The sequel course crosses that boundary into tactic
proofs, dependent types, and verified software.
@@@ -/

end Overview
