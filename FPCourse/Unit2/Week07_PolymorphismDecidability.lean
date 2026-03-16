-- FPCourse/Unit2/Week07_PolymorphismDecidability.lean
import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic

/-! @@@
# Week 7: Polymorphism and Decidability

## Type variables and parametric polymorphism

A *polymorphic* function works uniformly for any type.  Type variables
(written with lowercase letters like `α`, `β`) stand for any type.

A function is *parametrically polymorphic* if its behavior does not
depend on which type the variable is instantiated to.  The type alone
constrains what the function can do — a polymorphic `f : List α → List α`
cannot inspect element values, so it can only permute, drop, or
duplicate them.
@@@ -/

namespace Week07

/-! @@@
## 7.1  Polymorphic functions and their types
@@@ -/

-- id works for any type
#check @id        -- (α : Type u) → α → α

-- const ignores its second argument
def myConst (a : α) (_ : β) : α := a
#check @myConst   -- (α β : Type u) → α → β → α

-- flip swaps argument order
def myFlip (f : α → β → γ) : β → α → γ := fun b a => f a b
#check @myFlip    -- (α β γ : Type u) → (α → β → γ) → β → α → γ

/-! @@@
## 7.2  Bounded polymorphism: type class constraints

Sometimes a polymorphic function needs *some* knowledge about the type.
Type classes express this: `[DecidableEq α]` says "α must have a
decidable equality test."  The constraint is explicit in the type.
@@@ -/

-- Without DecidableEq, we cannot compare elements
def contains [DecidableEq α] (x : α) : List α → Bool
  | []      => false
  | h :: t  => x == h || contains x t

-- The type class constraint is part of the specification:
-- "for any type α with decidable equality, ..."
theorem contains_spec [DecidableEq α] (x : α) (xs : List α) :
    contains x xs = true ↔ x ∈ xs := by
  induction xs with
  | nil => simp [contains]
  | cons h t ih =>
    simp only [contains, List.mem_cons]
    constructor
    · intro hc
      by_cases heq : x = h
      · left; exact heq
      · right
        have : contains x t = true := by
          have hne : (x == h) = false := beq_eq_false_iff_ne.mpr heq
          simp [hne] at hc
          exact hc
        exact ih.mp this
    · intro hm
      cases hm with
      | inl heq => simp [contains, heq]
      | inr ht  =>
        simp [contains]
        right
        exact ih.mpr ht

/-! @@@
## 7.3  The DecidableEq type class

`DecidableEq α` is a type class that provides, for every pair `a b : α`,
a decision: either a proof that `a = b` or a proof that `a ≠ b`.

```lean
class DecidableEq (α : Type u) where
  decEq : (a b : α) → Decidable (a = b)
```

Instances of `Decidable`:
```lean
inductive Decidable (p : Prop) where
  | isFalse : ¬p → Decidable p
  | isTrue  :  p → Decidable p
```

A `Decidable` value IS either a proof of `p` or a proof of `¬p`.
When `decide` is used as a proof term, it extracts the `isTrue h`
component and provides `h : p`.

Types with `DecidableEq`: `Nat`, `Int`, `Bool`, `Char`, `String`,
`List α` (when α has it), `Option α` (when α has it), and all types
you define with `deriving DecidableEq`.

Types WITHOUT `DecidableEq`: functions `α → β` in general (you cannot
check `f = g` by running them), and — crucially — `Float`.
@@@ -/

-- Nat has DecidableEq:
example : DecidableEq Nat := inferInstance
example : (3 : Nat) = 3 ∨ (3 : Nat) ≠ 3 := by decide

-- Bool has DecidableEq:
example : DecidableEq Bool := inferInstance

-- List Nat has DecidableEq:
example : DecidableEq (List Nat) := inferInstance
example : ([1, 2, 3] : List Nat) = [1, 2, 3] := by decide

/-! @@@
## 7.4  Float and the absence of DecidableEq

`Float` represents IEEE 754 double-precision floating-point numbers.
IEEE 754 specifies that `NaN ≠ NaN` — the special "not a number" value
is not equal to itself.

This violates the *reflexivity* of equality: `∀ x, x = x`.
Lean's equality is reflexive by definition (`rfl : a = a`).
If `Float` had `DecidableEq`, we could derive `NaN = NaN` (by `rfl`),
contradicting IEEE 754.

Therefore `Float` does NOT have a `DecidableEq` instance in Lean.
This is not a missing feature.  It is the type system correctly
refusing to certify something that is not true.

The practical consequence:
- You CANNOT use `decide` to prove propositions involving `Float` equality.
- You CANNOT use `Float` values as keys in structures requiring `DecidableEq`.
- Specifications about floating-point programs must use `Real` or `Rat`
  for the mathematical content, with a separate claim about approximation.

More importantly, this is a lesson that applies in *every* programming language:
**never use `==` to compare floating-point values.**
The same IEEE 754 semantics that breaks `DecidableEq` here — `NaN ≠ NaN`, and
rounding means two computations of "the same" value may produce slightly different
results — make floating-point equality unreliable in Python, Java, C, and everywhere
else.  Always compare floats with a tolerance: `|x - y| < ε`.
@@@ -/

-- Float DOES have BEq (Boolean equality), but that is NOT the same as =
#check (inferInstance : BEq Float)   -- BEq Float is available

-- BEq.beq : α → α → Bool   -- a computation returning Bool
-- Decidable (a = b)          -- a proof of a logical claim
-- These are different things.

-- The == operator on Float uses BEq, not DecidableEq.
-- It handles NaN by returning false, matching IEEE 754.
-- #eval (Float.nan == Float.nan : Bool)    -- false  (IEEE 754)

-- But we CANNOT write:
-- example : (1.0 : Float) = 1.0 := decide   -- DOES NOT COMPILE

-- We CAN write specifications using Real (the mathematical reals):
-- "the floating-point addition of x and y approximates real addition"
-- ∀ x y : Float, |Float.toReal (x + y) - (Float.toReal x + Float.toReal y)| < ε
-- This is a real-valued specification; its verification uses a different
-- methodology (floating-point error analysis).

/-! @@@
## 7.5  Summary: the decidability boundary

**Reading `∀` and `∃`.**  Two quantifiers appear throughout this table
and the rest of the course.  Read them aloud as follows:

- `∀ x : α, P x` — "for every `x` of type `α`, the proposition `P x` holds"
- `∃ x : α, P x` — "there exists some `x` of type `α` such that `P x` holds"

Both are types.  A proof of `∀ x : α, P x` is a *function* `(x : α) → P x` —
given any `x`, produce a proof of `P x`.  A proof of `∃ x : α, P x` is a
*dependent pair* `⟨witness, proof⟩` — a specific value together with a proof
that the claim holds for that value.

| Proposition form | Decidable? | Proof term |
|-----------------|-----------|------------|
| `a = b` for `Nat`, `Bool`, `List Nat`, etc. | Yes | `decide` |
| `a < b` for `Nat`, `Int` | Yes | `decide` |
| `∀ x ∈ xs, P x` (finite `xs`, decidable `P`) | Yes | `decide` |
| `∃ x ∈ xs, P x` (finite `xs`, decidable `P`) | Yes | `decide` |
| `a = b` for `Float` | **No** | Cannot be proved with `decide` |
| `a = b` for function types | **No** | Not decidable in general |
| `∀ n : Nat, P n` (unbounded) | Not in general | Requires a proof |
| `∃ n : Nat, P n` (unbounded) | Not in general | Requires a witness + proof |

This table is one of the most important things in the course.

## Exercises

1. Define a polymorphic function `myNub [DecidableEq α] : List α → List α`
   that removes duplicate elements.  State its specification: "every
   element of the result appears in the input, and no element appears twice."

2. Explain in your own words why `Float` cannot have `DecidableEq`.
   What goes wrong if you assume it does?

3. Use `decide` to check: `"hello" = "hello"` as a Prop.  Then explain
   why this works but `(1.0 : Float) = 1.0` does not.

4. Give an example of a type you define yourself, add `deriving DecidableEq`,
   and use `decide` to check an equality proposition about it.

5. Define a type `Color` with constructors `Red`, `Green`, `Blue` and
   add `deriving DecidableEq`.  Use `decide` to prove:
   (a) `Color.Red ≠ Color.Blue`
   (b) `∀ c ∈ [Color.Red, Color.Green, Color.Blue], c = Color.Red ∨ c ≠ Color.Red`
   Explain why `decide` can handle this but could not handle the same
   claim over all `Nat` values.
@@@ -/

end Week07
