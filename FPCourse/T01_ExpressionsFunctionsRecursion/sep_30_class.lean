-- propositional logic vs predicate logic
-- propositional is just bools? predicate is for anything. -- predicate the sky is blue
-- predicate requires proofs and construction?

theorem notpandnotp {P : Prop} : ¬(P ∧ ¬P) :=
  fun h => h.right h.left


-- Predicate logic:
-- has for instances:
-- literal True
-- literal False
-- And P Q
-- Or P Q
-- not p : p -> False
-- Iff
-- for all is literally like implication like a function. you can take any proof of P and get a proof of Q
-- exists
-- functions

-- predicates
-- Dog with two values : Fido and Iris.
-- objects have properties like friendly, furry (vs. has hair)
-- Fido is friendly
-- Fido is not furry
-- Iris is not friendly

-- inductive FidoFriendly: Prop where
-- | mk

-- inductive FidoNotFurry where -- no values, so it's not true.

-- inductive IrisFriendly where
-- | mk

-- predicate is a proposition with a variable/placeholder
-- friendly is parametrized

-- predicates are functions that take variables and return propositions.
-- inductive Friendly: Dog → Prop
-- | irisFr : Friendly Iris
-- | fidoFr : Friendly Fido

inductive Dog : Type where
| Iris
| Fido
| Sargeant

open Dog

inductive Friendly : Dog → Prop where
| irisFriendly : Friendly Iris
| fidoFriendly : Friendly Fido

inductive Furry : Dog → Prop where
| irisFurry : Furry Iris
| sargeantFurry : Furry Sargeant

example : Furry Iris ∧ Friendly Iris := And.intro Furry.irisFurry Friendly.irisFriendly

def Suitable : Dog → Prop := fun d => (Friendly d ∧ Furry d)
def Suitable1 (d : Dog) : Prop := (Friendly d ∧ Furry d)
-- Furry and Friendly are both props. And of props is also a prop

example : Suitable Iris := And.intro (Friendly.irisFriendly) (Furry.irisFurry)

-- predicates are functions. takes objects and returns propositions

#check (Suitable)
#check (Friendly)
#check (Furry)

#check (∀ (d : Dog), Friendly d)
#check ∀ (d : Dog), Friendly d
-- Friendly d is a type. Does it have a proof for every dog?

-- example : ∀ (d : Dog), Friendly d :=
--   fun d =>
--   match d with
--   | Fido => Friendly.fidoFriendly
--   | Iris => Friendly.irisFriendly
--   | Sargeant => -- we don't have a proof for this

example : ¬( ∀ (d : Dog), Friendly d) :=
  fun allDogsFriendly =>
    let sf := allDogsFriendly Sargeant
    nomatch sf


example : ∃ (d : Dog), Friendly d := Exists.intro Iris Friendly.irisFriendly
-- existential quantification does not tell you what the specific example was. once you put
-- it in, you can never get it back out
