-- getting a type that is inhabited means there's a proof
-- Curry Howard correspondence - computability theorists
-- List isn't a type. it's a type builder. takes one argument: the type you want
-- then you get, List Type, List Nat, List Bool. - parametric polymorphism

-- Polymorphic types - type of the first element, type of the second element. in an ordered pair
-- Prod Nat String is the type of ordered pair where first is Nat, second is String
-- de-sugars. Couple different notations mean the same thing - de-sugaring is finding what the specific notation corresponds to

-- overloaded operator - different definitions for the same operator. One + (addition function) for Nats, one for Floats
-- this is "AD HOC" because it determines which algorithm to use for the operator based on context (whether you have Nats or Floats)

-- Sum type is an inclusive OR, not EXCLUSIVE OR

-- IDENTITY FUNCTIONS:
def id_Nat : Nat → Nat := fun n => n

def id' (α : Sort u) : α → α := fun n => n -- sort u is inferred
-- under the hood, id' Bool returns a function from Bool to Bool that returns the same value
-- so it's like (id' Bool) 3.
-- Lean does type inference - that is the underscore



#eval id' Nat 3
#eval id' Bool true

-- again, downstream arguments can affect the value of upstream arguments. Lean sees 3 is Nat, fills it in

#eval id' _ 3
#eval id' _ true
#eval id' _ [1,2,3]

-- don't even have to write _
def id'' {α : Sort u} : α -> α := fun n => n

#eval id'' 3
#eval id'' true
#eval id'' [1,2,3]

-- You can't give an implicit argument explicitly.
-- #eval id'' Nat 3 -- doesn't work
#eval @id'' Nat 3 -- @ allows you to specify the implicit type


-- parametricity - if you want to write a totally polymorphic function - LITERALLY ANY TYPE -
-- then all you can

-- meta variables, adhoc parametricity




#check Nat.add
#check Nat.add 3

def myAdd := Nat.add
#check myAdd
#eval myAdd 3 4

def add3 := Nat.add 3
#check add3
#eval add3 7

def sum := Nat.add 3 4
#check sum
-- a function is curried.
-- fun 1 2 3 -- this is left associative. (fun 1) returns a function, then (fun 1) 2 is done, then ((fun 1) 2) is computed

def f' (b1 b2 b3 : Bool) : Bool := true
#check (f' true)

def f'' : Nat → Nat → Nat → Nat := fun a b c => 0
#check (((f'' 0) 1) 2)
#eval (((f'' 0) 1) 2)
