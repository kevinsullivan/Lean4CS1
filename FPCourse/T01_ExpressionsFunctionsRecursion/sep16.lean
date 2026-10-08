-- Pred Logic injectively maps to Type theory.
-- some things map to type theory but type theory is way bigger

-- Shallow embedding -- implementation strategy. takes
-- Language constructs as types
-- Abstract mathematics theory

-- regular languages don't have propositional facilities like Lean does
namespace hey -- THIS IS A DEEP EMBEDDING
-- you can't build a thing like this for the syntax for C code because
-- some C programs don't terminate.
-- if you have this case where you don't know if the program will terminate
-- (like a total function with infinite inputs if I understand),
-- you then have to start reasoning logically about your programs, instead
-- of checking the finite cases computationally, in order to check for correctness

-- BUT -- deep embedding x86 and C code to prove the compiler is correct is a thing

inductive Variable where
| Xvar
| Yvar
| Zvar

open Variable

def varInterp : Type := Variable → Bool -- literally the TYPE of functions from Variable to Bool

def i1 : varInterp := -- this is one implementation of the above type. 8 possible since 3 variables
 fun (v : Variable) =>
  match v with
  | Xvar => true
  | Yvar => true
  | Zvar => true

inductive PropLogicSyntax where
| T
| F
| And (p1 p2 : PropLogicSyntax): PropLogicSyntax
| Or (p1 p2: PropLogicSyntax) : PropLogicSyntax
| Not (p: PropLogicSyntax): PropLogicSyntax
| Var (v : Variable)

open PropLogicSyntax

def eval : PropLogicSyntax → varInterp → Bool -- LEAN CHECKS CASES FROM TOP TO BOTTOM
| T, _ => true
| F, _ => false
| PropLogicSyntax.And p1 p2, i => (eval p1 i) && (eval p2 i)
| PropLogicSyntax.Or p1 p2, i => (eval p1 i) || (eval p2 i)
| PropLogicSyntax.Not p1, i => !(eval p1 i)
| PropLogicSyntax.Var v, i => i v
-- | BarnyRubble => false  -- can use any name for the default case

def e1 := F
def e2 := T
def e3 := PropLogicSyntax.And e1 e2

def X := PropLogicSyntax.Var Xvar
def Y := PropLogicSyntax.Var Yvar
def Z := PropLogicSyntax.Var Zvar



#eval eval e1 i1
#eval eval e2 i1
#eval eval e3 i1

end hey


-- curry howard

-- AND ∧ ⇔ Prod ×

-- always has one inhabitant and a default constructor. Rice.mk. So you can
-- still do case analysis
structure Rice
structure Potato

def choiceRice: Rice Potato := Sum
