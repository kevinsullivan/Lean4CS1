def sumtoN : Nat → Nat
| Nat.zero => 0
| Nat.succ n => n+1 + sumtoN n

def sumToN' (n : Nat) : Nat :=
  match n with
  | Nat.zero => 0
  | Nat.succ n => n+1 + sumToN' n

--def sumToN'' (n : Nat) : Nat :=
--  match n with
--  | Nat.zero => 0
--  | n => n + sumToN'' (n-1) -- doesn't work since it's not guaranteed to terminate by structural recursion

#eval sumToN' 3
#eval sumToN' 4

def factorial (n : Nat) : Nat :=
  match n with
  | Nat.zero => 1
  | Nat.succ n' => (n'+1) * factorial n'

#eval factorial 2

inductive Variable where
| Xvar
| Yvar
| Zvar

open Variable

namespace Arith

inductive ArithExpr where
| lit (n : Nat)
| plus (x y : ArithExpr) -- add mul/times. go back and study for propositional logic
| mul (x y : ArithExpr)
| Var (v : Variable)
-- do the same for variables

#eval 1000000000000000 * 1000000000000000

open ArithExpr

def X : ArithExpr := ArithExpr.Var Variable.Xvar
def Y : ArithExpr := ArithExpr.Var Variable.Yvar
def Z : ArithExpr := ArithExpr.Var Variable.Zvar

def varInterp : Type := Variable → Nat

def i1 : varInterp :=
  fun (v : Variable) =>
    match v with
    | Xvar => 2
    | Yvar => 5
    | Zvar => 7

def a1 : ArithExpr := lit 1
def a7 : ArithExpr := lit 7
def a1plusa7 : ArithExpr := plus a1 a7

-- operational semantics

def arithEval (t : ArithExpr) (i : varInterp): Nat :=
match t with
| lit t => t
| plus x y => (arithEval x i) + (arithEval y i)
| mul x y => (arithEval x i) * (arithEval y i)
| Var v => i v

#eval arithEval a1plusa7 i1

end Arith
