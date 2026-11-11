-- abstract syntax: functions, not intuitive
-- concrete syntax: defining the use of operators as standard symbols
-- for whatever operations you're doing.

-- difference between And function and implementing &&

-- UNDERSTAND false -> true. trivially true

-- false to false

-- this is a valid but uncallable function because
-- the definition assumes you have a value of type empty
def e2e : Empty → Empty
  | e => e

theorem fimpf : False → False
  | f => f

inductive MyEmpty where
--| mk

open MyEmpty

def me2e : MyEmpty → Empty
  | m => nomatch m -- you need nomatch because MyEmpty is a
  -- different type than Empty

-- if this function above exists, proves MyEmpty is uninhabited
-- functions must be total, so if there's at least one constructor
-- for MyEmpty, you can't build a function that takes a value of
-- myEmpty and returns an Empty. that does not exist


inductive MyFalse : Prop where
--| mk

theorem myFalseIsReallyFalse : MyFalse → False
| m => nomatch m
-- if we can't define this function, MyFalse is not really uninhabited

def neg (a : Prop) : Prop := a → False

#check MyFalse

example : neg MyFalse | m => nomatch m

example : ¬MyFalse
| m => nomatch m


inductive KevinIsFromCville : Prop where
| driversLicense

example : KevinIsFromCville := KevinIsFromCville.driversLicense

inductive JorgIsFromToronto : Prop where
| driversLicense
| utilityBill
| healthCard

example: And KevinIsFromCville JorgIsFromToronto := And.intro KevinIsFromCville.driversLicense JorgIsFromToronto.utilityBill

-- all proofs are equal in Prop. You can't match on proofs or distinguish them
-- not so in Types, not all bools are equal (literally 3 and 5 are not equal).

inductive Cat : Type where
| siamese
| tabby

example : Cat.tabby ≠ Cat.siamese
  | m => nomatch m -- the fact that this works PROVES that Cat.tabby ≠ Cat.siamese


-- THESE ARE DIFFERENT VALUES BUT THEY ARE CONSIDERED EQUAL BECAUSE THEY ARE BOTH PROPS AND PROVE THE SAME THING
example : JorgIsFromToronto.driversLicense = JorgIsFromToronto.healthCard := rfl

-- proofs of the same thing are equal. proofs of different things are not equal
-- example : KevinIsFromCville.driversLicense = JorgIsFromToronto.healthCard := rfl

-- go look up demorgan's laws. prove them in Lean

-- not all cases are valid in Lean

theorem negationOfConjunction {P Q : Prop} : ¬P ∨ ¬Q → ¬(P ∧ Q) :=
  fun h hpq =>
    match h with
    | Or.inl np => np hpq.1
    | Or.inr nq => nq hpq.2


theorem negationOfDisjunction_way_1 {P Q: Prop} : ¬(P ∨ Q) → ¬P ∧ ¬Q := -- P or Q -> false -> not P and not Q
  fun h => And.intro (fun p => h (Or.inl p)) (fun q => h (Or.inr q))

-- theorem negationOfDisjunction_way_2 {P Q: Prop} : ¬P ∧ ¬Q → ¬(P ∨ Q) :=
--   fun h =>
--     let p : P := And.left h
--     let q : Q := And.right h
--     match h with
--     | Or.inl p => nomatch h
--     | Or.inr q => nomatch h

theorem negationOfDisjunction_way_12 {P Q : Prop} : ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  fun h =>
    let np : ¬P := fun p => h (Or.inl p)
    let nq : ¬Q := fun q => h (Or.inr q)
    And.intro np nq




theorem negationOfDisjunction_way_2 {P Q: Prop} : ¬P ∧ ¬Q → ¬(P ∨ Q) :=
  fun h horq =>
    let np : ¬P := And.left h
    let nq : ¬Q := And.right h
    match horq with
    | Or.inl p => np p
    | Or.inr q => nq q

example (P Q : Prop) (em : ∀ (X : Prop), X ∨ ¬X) : ¬(P ∧ Q) → (¬P ∨ ¬Q)

-- axiom of the excluded middle



-- h : ¬ (P∧Q)
-- not (P ∧ Q)
-- (P ∧ Q) → False
