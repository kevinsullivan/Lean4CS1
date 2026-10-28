-- type class
-- structure object.
-- one constructor. one or more fields
-- inductive type

-- an instance is a value of that kind of type

def add : Nat → Nat → Nat
| a, Nat.zero => a
| a, Nat.succ b => Nat.succ (add a b)

-- Zero is a type class

instance : Zero Nat where
zero := Nat.zero -- allows us to use the character 0

--instance : Add Knat where
--  add := add

def mul : Nat → Nat → Nat
| _, Nat.zero => Nat.zero
| Nat.zero, _ => Nat.zero
| a, Nat.succ b => add a (mul a b)

def exp : Nat → Nat → Nat
| _, Nat.zero => 1
| 0, _ => Nat.zero
| a, Nat.succ b => mul a (exp a b)

-- #check ((1 + 1) : Knat)

def addAnything (α : Type) [Add α] : α → α → α
| a, b => a + b
-- Add α is a type guard. checks if there's an add method for that type

#eval addAnything Nat 4 5 -- must make type argument explicit unless you make it implicit

-- define group in math. 0 element, additive inverse to get back to 0 aka a and -a, associativity and commutativity etc.
-- define a function : i'll take any type as long as it's a group and satisfies all group axions.
-- can now treat polymorphic object assuming all properties of groups
-- a set of things

-- fields of type classes can be proofs. so you verify you have properties of groups?
--
