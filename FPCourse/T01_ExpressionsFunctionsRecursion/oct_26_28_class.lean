namespace hi

inductive MyOption α
| None
| Some (a: α)
open Option

inductive MyList α
| nil -- empty
| cons (h : α) (l : List α)

def dec : Nat → MyOption Nat
| 0 => MyOption.None
| (n+1) => MyOption.Some n

def head {α : Type} : MyList α → MyOption α
| MyList.nil => MyOption.None
| MyList.cons h _ => MyOption.Some h

def head' {α : Type} : List α → Option α
| [] => none
| h::t => some h


end hi

def myfold {α : Type}
(mylist : List α)
(f : α → α → α)
(f_assoc: ∀ (a b c: α ), f (f a b) c = f a (f b c))
(id : α)
(fid : ∀ (a : α), f id a = a ∧ f a id = a)
: α :=
match mylist with
| [] => id
| h::t => f h (myfold t f f_assoc id fid)


def myMap {α β : Type} (f : α → β) : List α → List β
| [] => []
| h::t => (f h)::(myMap f t) -- why do you need f. the colon is confusing.

#eval myMap (fun n => n*n) [1,2,3,4,5]



-- oct 28

-- "container types"
-- talking about functions from type to type
-- takes a type as an argument, returns the type of LISTS OF NAT
-- a type CONSTRUCTOR
#check (Option)



class Foldable (F : Type → Type) where
  foldr {α β : Type} : (α → β → β) → β → F α → β

-- 3 + (nat.add rest of the list) = sum
-- (isAnd 3) AND (isEven(rest of the list)) = BOOL
-- Nat to Bool to Bool for instance: the accumulator function
-- taking a new nat, converting it to the new type, ANDing it with the result
-- for the rest of the list, then return the result at the end


-- F is the container like Tree or List
