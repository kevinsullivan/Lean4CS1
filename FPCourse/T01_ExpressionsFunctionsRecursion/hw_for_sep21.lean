structure Rice
structure Potato
structure Fish
structure Chicken

def swap {α β : Type u} (p: α × β) := (p.2, p.1)

/- @@@
## EXERCISES:
@@@ -/

-- #1: PROVE: Chicken ⊕ Fish → Fish ⊕ Chicken

def sumIsCommutative : Chicken ⊕ Fish → Fish ⊕ Chicken
  | Sum.inl chicken => Sum.inr chicken
  | Sum.inr fish => Sum.inl fish

/- @@@
#2: PROVE: that someone who ordered "Fish, and either
Rice or Potato" should be satisfied to be served
"Rice or Potato, and Fish. Clearly, it's true: you
just have to turn the plate a little! To prove it
it would do to show there's a function that applied
to a whole *meal, "Fish, and either Rice or Potato"
derives and returns a meal, "either Rice or Potato,
and Fish."
@@@-/

example : Fish × (Rice ⊕ Potato) → (Rice ⊕ Potato) × Fish
| a => (a.snd, a.fst)    -- replace this line

/- @@@
That's just commutativity of × again. We proved it by
running the whole proof strategy again for this special
case of the general principle; but we don't have to, as
we have a general "theorem" (swap function) for that.

The reason we prefer to prove generalized theorems or
write general-purpose functions is because we can then
*apply* them where needed without having to reproduce
the whole derivation from scratch. It's makes math work!
@@@ -/

example :
  Fish × (Rice ⊕ Potato) → (Rice ⊕ Potato) × Fish
  | meal => swap meal

/- @@@
#3: Prove. Here's an example suggesting that × distributes
over ⊕ just as numerical multiplication distributes over
addition: x * (y + z) = x * y + x * z. Show that the
same principle holds for × and ⊕, first in a specific
example, then in general.
@@@ -/

example :
  Fish × (Rice ⊕ Potato) → Fish × Rice ⊕ Fish × Potato
  | (f, Sum.inl rice) => Sum.inl (f, rice)
  | (f, Sum.inr potato) => Sum.inr (f, potato)
  -- you've got fish; now does rop hold rice or potato?

-- #4 Prove the other direction too.
example :
  Fish × Rice ⊕ Fish × Potato → Fish × (Rice ⊕ Potato)
  | Sum.inl (f, rice) => (f, Sum.inl rice)
  | Sum.inr (f, potato) => (f, Sum.inr potato)




/- @@@
### The Curry-Howard Twin of ⊕ is ∨

Just as *And* (∧) is the Curry-Howard twin of *×*,
so *Or* (∨) is the twin of ⊕. Go back and study the
inductive definition of *Sum* (⊕) then compare with
it's logical counterpart, `Or` (∨), copied below.

```lean
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
```

Infix notation for the type, *Or P Q*, is *P ∨ Q*.
@@@ -/


-- #5: PROVE: `Or` (∨) is commutative *in general*

example {P Q : Prop} : P ∨ Q → Q ∨ P
| Or.inl a => Or.inr a
| Or.inr a => Or.inl a

-- #6: Prove ∧ distributes over or in the usual way
example {P Q R : Prop } : P ∧ (Q ∨ R) → P ∧ Q ∨ P ∧ R
  | And.intro p (Or.inl q) => Or.inl (And.intro p q)
  | And.intro p (Or.inr r) => Or.inr (And.intro p r)

-- #7: Prove that ∨ is associative. It's left associative
-- so note that P ∨ Q ∨ R is read as (P ∨ Q) ∨ R.
example {P Q R : Prop } :  P ∨ Q ∨ R → (P ∨ Q) ∨ R
 | Or.inl p => Or.inl (Or.inl p)
 | Or.inr (Or.inl q) => Or.inl (Or.inr q)
 | Or.inr (Or.inr r) => Or.inr r
