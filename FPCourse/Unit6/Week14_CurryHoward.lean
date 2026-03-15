-- FPCourse/Unit6/Week14_CurryHoward.lean

/- @@@
## Week 14: Types, Propositions, Programs, Proofs — The Curry–Howard Correspondence

### Overview

Every week of this course, we have done two things simultaneously:
1. Written a program.
2. Proved something about it.

This week we reveal that these were always the *same thing*.

The **Curry–Howard correspondence** (also called the propositions-as-types
correspondence, or the proofs-as-programs correspondence) is a precise
mathematical theorem:

> **Types are propositions.  Programs are proofs.  Evaluation is proof normalisation.**

In Lean 4, this is not a metaphor or an analogy — it is the literal design
of the language.  `Prop` (the type of propositions) and `Type` (the type of
types) are two faces of the same universe.  A term of type `P : Prop` *is*
a proof of `P`.  A term of type `T : Type` *is* a program of type `T`.

| Type system concept          | Logic concept                   |
|------------------------------|---------------------------------|
| `A × B` (product)            | `A ∧ B` (conjunction)           |
| `A ⊕ B` (sum/variant)        | `A ∨ B` (disjunction)           |
| `A → B` (function)           | `A ⊃ B` (implication)           |
| `Unit`                       | `⊤` (truth)                     |
| `Empty`                      | `⊥` (falsity)                   |
| `∀ (α : Type), P α`          | `∀ α, P α` (universal quant.)  |
| `∃ (α : Type), P α`          | `∃ α, P α` (existential quant.) |
| A well-typed term `t : A`    | A proof of `A`                  |
| Evaluation `t →* v`          | Proof normalisation              |
| Type checking                | Proof checking                  |
@@@ -/

namespace Week14

/- @@@
### 14.1  Propositions are types in Lean 4

In Lean 4, `Prop` is the sort (universe) of propositions.  Every
proposition is a type.  A proof of a proposition `P` is a term of type `P`.

The familiar tactic proofs we have been writing all semester are constructing
terms of types in `Prop`.  When we write `intro h`, we are building a
function (`→`-introduction).  When we write `exact ⟨ha, hb⟩`, we are
building a pair (`∧`-introduction).  The tactics are just a convenient
syntax for term construction.
@@@ -/

-- Conjunction is the product type — a proof of A ∧ B is a pair
theorem and_intro_example (ha : α) (hb : β) : α ∧ β := ⟨ha, hb⟩

-- The same proof in term mode (no tactics):
def and_intro_term (ha : α) (hb : β) : α ∧ β := And.intro ha hb

-- Implication is the function type — a proof of A → B is a function
theorem impl_example : α → β → α := fun ha _ => ha   -- this is `myConst`!

-- Disjunction is the sum type
theorem or_intro_left_example (ha : α) : α ∨ β := Or.inl ha
theorem or_intro_right_example (hb : β) : α ∨ β := Or.inr hb

-- Universal quantification is the dependent function type (Π type)
theorem forall_example : ∀ (n : Nat), n + 0 = n := fun n => Nat.add_zero n

/- @@@
### 14.2  Structural induction is the induction principle of an inductive type

When we proved theorems by `induction xs with | nil => ... | cons x xs ih => ...`,
we were using the *recursion principle* of the `List` type.

In the Curry–Howard view:
- The recursion principle of `List α` is a *term* of a certain dependent type.
- Structural induction *is* structural recursion, viewed through the lens of propositions.
- The inductive hypothesis (IH) is the *result of the recursive call* applied to
  the smaller piece of data.

The structural induction principle for lists, stated as a Lean type:
@@@ -/

-- The induction principle for List α (this is List.rec in the standard library)
-- We spell it out to make the Curry-Howard reading explicit:
-- "To prove P for all lists, give a proof of P [] and a function that,
--  given any x : α, any xs : List α, and assuming P xs (the IH),
--  produces a proof of P (x :: xs)."
def myListInd
    {α : Type}
    {P : List α → Prop}
    (base : P [])
    (step : ∀ (x : α) (xs : List α), P xs → P (x :: xs))
    (xs : List α) : P xs :=
  match xs with
  | []      => base
  | x :: xs => step x xs (myListInd base step xs)

-- This IS structural recursion: myListInd is a recursive function!
-- The Curry-Howard correspondence says: structural induction = structural recursion.

/- @@@
### 14.3  Falsehood and negation

The empty type `Empty` has no constructors — it is uninhabited.
In the Curry–Howard correspondence, `Empty` corresponds to `⊥` (falsity).

Negation `¬ P` is defined as `P → False` — a function from a proof of `P`
to a proof of falsehood, which must be impossible to call if `P` is truly false.

`False.elim` is the principle of explosion (*ex falso quodlibet*): from
a proof of `False`, we can derive any proposition.
@@@ -/

-- Negation: ¬ P is P → False
example (h : False) : α := False.elim h

-- Proof by contradiction: to prove P, assume ¬P and derive False
theorem not_not_elim (h : ¬¬ α) : α := by
  -- In classical logic, this holds. In constructive logic, we need
  -- the law of excluded middle. Lean includes classical reasoning.
  by_contra hn
  exact h hn

/- @@@
### 14.4  The capstone: a type-checker as a correctness proof

A **type-checker** is a program that decides whether an expression has a
given type.  In the Curry–Howard view:
- The types of the source language are *propositions*.
- A well-typed expression is a *proof* of its type.
- The type-checker *verifies* the proof.

We implement a type-checker for a minimal typed language.
Its correctness connects type theory, computation, and logic directly.
@@@ -/

-- A minimal typed expression language
inductive Ty where
  | nat  : Ty
  | bool : Ty
  | arr  : Ty → Ty → Ty     -- function type
  deriving DecidableEq, Repr

inductive Expr where
  | litNat  : Nat → Expr
  | litBool : Bool → Expr
  | var     : String → Expr
  | app     : Expr → Expr → Expr
  | lam     : String → Ty → Expr → Expr
  | ite     : Expr → Expr → Expr → Expr    -- if-then-else
  deriving Repr

-- A typing context: maps variable names to their types
abbrev Ctx := List (String × Ty)

def ctxLookup (x : String) : Ctx → Option Ty
  | []              => none
  | (y, τ) :: rest  => if x == y then some τ else ctxLookup x rest

/- @@@
The **typing relation** for this language is:

- `Γ ⊢ n : nat`                                    (literal nat)
- `Γ ⊢ b : bool`                                   (literal bool)
- `Γ(x) = τ ⊢ x : τ`                              (variable)
- `Γ ⊢ f : τ₁ → τ₂` and `Γ ⊢ e : τ₁ ⊢ f e : τ₂` (application)
- `(Γ, x:τ₁) ⊢ e : τ₂ ⊢ λx:τ₁.e : τ₁ → τ₂`      (abstraction)
- `Γ ⊢ c : bool`, `Γ ⊢ t : τ`, `Γ ⊢ f : τ ⊢ if c t f : τ` (conditional)

The type-checker implements this relation as a function returning `Option Ty`.
@@@ -/

def typecheck (Γ : Ctx) : Expr → Option Ty
  | .litNat _        => some .nat
  | .litBool _       => some .bool
  | .var x           => ctxLookup x Γ
  | .app f e         => do
      let τf ← typecheck Γ f
      let τe ← typecheck Γ e
      match τf with
      | .arr τ₁ τ₂ => if τ₁ == τe then some τ₂ else none
      | _           => none
  | .lam x τ₁ e     => do
      let τ₂ ← typecheck ((x, τ₁) :: Γ) e
      return .arr τ₁ τ₂
  | .ite c t f       => do
      let τc ← typecheck Γ c
      let τt ← typecheck Γ t
      let τf ← typecheck Γ f
      if τc == .bool && τt == τf then some τt else none

-- Examples
#eval typecheck [] (.litNat 42)                            -- some nat
#eval typecheck [] (.lam "x" .nat (.var "x"))              -- some (nat → nat)
#eval typecheck [] (.app (.lam "x" .nat (.var "x")) (.litNat 5))  -- some nat
#eval typecheck [] (.ite (.litBool true) (.litNat 1) (.litNat 2)) -- some nat

-- Type error: applying a nat to an argument
#eval typecheck [] (.app (.litNat 5) (.litNat 3))          -- none

/- @@@
### 14.5  Correctness of the type-checker

The type-checker's correctness has two parts:

1. **Soundness**: if `typecheck Γ e = some τ`, then `e` is genuinely
   well-typed in `Γ` with type `τ`.
2. **Completeness**: if `e` is well-typed in `Γ` with type `τ`, then
   `typecheck Γ e = some τ`.

We prove soundness for the base cases.
@@@ -/

-- The typing relation (the "official" spec)
inductive Typed : Ctx → Expr → Ty → Prop where
  | litNat  : Typed Γ (.litNat n) .nat
  | litBool : Typed Γ (.litBool b) .bool
  | var     : ctxLookup x Γ = some τ → Typed Γ (.var x) τ
  | app     : Typed Γ f (.arr τ₁ τ₂) → Typed Γ e τ₁ → Typed Γ (.app f e) τ₂
  | lam     : Typed ((x, τ₁) :: Γ) e τ₂ → Typed Γ (.lam x τ₁ e) (.arr τ₁ τ₂)
  | ite     : Typed Γ c .bool → Typed Γ t τ → Typed Γ f τ → Typed Γ (.ite c t f) τ

-- Soundness for base cases
theorem typecheck_sound_litNat (n : Nat) :
    Typed Γ (.litNat n) .nat := Typed.litNat

theorem typecheck_sound_litBool (b : Bool) :
    Typed Γ (.litBool b) .bool := Typed.litBool

-- The full soundness theorem requires induction on the expression structure
-- (left as the capstone exercise)

/- @@@
### 14.6  Looking forward: dependent types

In Lean 4, types can *depend on values*.  The type `Vector α n`
is the type of lists of exactly `n` elements of type `α`.  The length
is not just a runtime value — it is *encoded in the type*.

```lean
def Vector (α : Type) : Nat → Type
  | 0     => Unit
  | n + 1 => α × Vector α n
```

A function `head : Vector α (n + 1) → α` is *total* — it can never
be called on an empty vector because the type forbids it.  The precondition
"the vector is non-empty" is enforced statically.

This is the payoff of the Curry–Howard perspective: more expressive types
let you state more precise specifications, and Lean verifies those
specifications at compile time.

The path forward:
- **CS 2 in this sequence**: data structures and algorithms with verified cost.
- **Type theory and proof assistants**: Coq, Agda, Lean's Mathlib.
- **Dependent types in production**: Idris, F* (for verified security).
- **The ideas everywhere**: Rust's ownership (linear types), TypeScript's
  union types (sum types), Scala/F#'s type classes (bounded quantification).
@@@ -/

-- A final demonstration: the identity function IS a proof of A → A
-- The type checker IS checking a logical proof
-- Every well-typed program we wrote was a theorem

theorem identity_is_a_proof : ∀ (α : Prop), α → α := fun _ h => h

-- This is definitionally equal to our id function from Week 2:
-- def myId (x : α) : α := x
-- Both are the term `fun x => x`, typed at `α → α`.
-- One is a program; the other is a proof.  In Lean 4, they are the same.

/- @@@
### Exercises

1. Prove the soundness of `typecheck` for the `var` case:
   `typecheck Γ (.var x) = some τ → Typed Γ (.var x) τ`.

2. Prove the soundness of `typecheck` for the `lam` case.

3. Prove the completeness of `typecheck` for the `litNat` case:
   `Typed Γ (.litNat n) τ → typecheck Γ (.litNat n) = some τ`.
   (Hint: what does the `Typed` derivation tell you about `τ`?)

4. State and prove the **subject reduction** (preservation) property for
   our language: if `Typed Γ e τ` and `e` steps to `e'`, then `Typed Γ e' τ`.
   You will need to define a small-step reduction relation first.

5. Revisit any proof from Weeks 3–9 and explicitly identify:
   - which proof technique it uses (induction, case analysis, etc.)
   - which Curry–Howard concept it corresponds to
   - what the IH is as a recursive call
@@@ -/

-- Exercise stub: full soundness by induction on the expression
theorem typecheck_sound (Γ : Ctx) (e : Expr) (τ : Ty)
    (h : typecheck Γ e = some τ) : Typed Γ e τ := by
  induction e generalizing Γ τ with
  | litNat n  => cases h; exact Typed.litNat
  | litBool b => cases h; exact Typed.litBool
  | var x     => exact Typed.var h
  | lam x τ₁ e ih =>
    simp [typecheck] at h
    obtain ⟨τ₂, hτ₂, hτ⟩ := h
    cases hτ
    exact Typed.lam (ih Γ τ₂ hτ₂)  -- note: needs generalizing
  | _ => sorry  -- remaining cases left as exercises

end Week14
