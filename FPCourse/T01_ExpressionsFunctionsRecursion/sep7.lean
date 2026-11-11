-- computational type
-- logical type
-- Unit has 1 value (kind of like void in Java)
-- true is a propositional type - value is a proof. 1 proof. having a proof means that it's true (because there's a proof)

-- Sort vs type
-- prop universe - if there exists a proof, it is true!
-- Bool: 2 values. Nat: infinitude

-- inductive - defining new type. Types can be parametrized. Empty has no constructors
-- same as inductive False : Prop

-- PUnit has 1 value. PUnit.unit of type PUnit. it's a proof of itself.

example : Nat := 3
example : True := True.intro -- an implementation of True
example : Unit := Unit.unit

-- Bool has 2 constructors: false and true

namespace hidden
inductive Bool : Type where
  | false : Bool
  | true : Bool

def b2s (b : Bool) : String :=
  match b with -- must exhaust every case since every function must be total
  | Bool.true => "It's true"
  | Bool.false => "It's false"

end hidden


-- introduction and elimination rules - how to build a proof or data value
-- how do you use Bool? Case analysis. what are the constructors that could have built it? only 2 cases in this case analysis

-- if B is false, do something, else do something else
-- elimination rules help you decide how to do the case analysis

namespace hidden

inductive Nat : Type where
  | Zero : Nat -- define what this means exactly later. Zero is the base case
  | Succ (n : Nat) : Nat -- successor of any natural number is also a natural number.

open hidden.Nat

def zero : Nat := Nat.Zero
def one := Nat.Succ Zero
--def two := Nat.Succ one
def two := Nat.Succ (Nat.Succ Nat.Zero)

def funk (n : Nat) : String :=
  match n with
  | Nat.Zero => ""
  | Nat.Succ n' => "1" ++ funk n'

#eval funk two

end hidden
