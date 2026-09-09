/- @@@
# In-Class Plan

The plan for today is to continue to learn about and practice with
inductive type definitions. For today, pair up with a study buddy:
someone to work and chat with today.
@@@ -/


/- @@@
## Computational types and Logical types

- Empty and False
- Unit and True
- Polymorphic types
- Sum (⊕) and Or (∨)
- Prod (×) and And (∧)
- _ → Empty and Not (¬)
@@@ -/

/- @@@
## Parametric Polymorphism

Suppose you've defined some type, α, and now you wish
to define the identity function on values of this type.
Here's what that looks like with α = Nat, α = Bool, and
α = List Nat. It even works for the Empty type.
@@@ -/

def id_Empty    : Empty     → Empty     := fun n => n
def id_Bool     : Bool      → Bool      := fun n => n
def id_Nat      : Nat       → Nat       := fun n => n
def id_ListNat  : List Nat  → List Nat  := fun n => n

/- @@@
It should be obvious that every implementation is exactly
the same *except* for the single type of value it consumes
and returns.

## Factor into Fixed Template with Variable Parameters

In such cases we can *factor* these programs into a single
*parameterized* definition, with a fixed template capturing
the commonalities, and parameters that can be set  to any
value to express the variability. This is that looks like.
@@@ -/

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

def f' : Nat → Nat → Nat → Nat := fun a b c => 0

#check (((f' 0) 1) 2)
-- #check (f' 0 (1 2))

def id' (α : Sort u) : α → α               := fun n => n

#eval id' Nat 3
#eval id' Bool true
#eval id' (List Nat) [1,2,3]

/- @@@

## Type (Actually Value) Inference
In each of these examples the second *actual
parameter* is a value of the type, α, given by
the first parameter. The type checker enforces
this rule. Try it. This is an example of what
we've called *dependent typing.* The *value* of
α (a type), determines the *type* of the second
argument.

Q: what does that say, in principle, about the
need to give the first argument explicitly?
@@@ -/

#eval id' _ 3
#eval id' _ true
#eval id' _ [1,2,3]

/- @@@

## Implciit Arguments for Better Readability

Lean syntax allows for even further cleanup in
the form of what Lean calls *implicit arguments*.
Curly braces around a parameter declaration tells
Lean to infer it, allowing the user not to write
anything at all.
@@@ -/

def id'' {α : Sort u} : α → α := fun n => n

#eval id'' 3
#eval id'' true
#eval id'' [1,2,3]

/- @@@
## Disabling Implicit Arguments When Necessary

You may *not* provide an implicit parameter
explicitly. If Lean can't infer an implicit
argument and you must give it explicitly you
can turn off *inference* locally using @.
@@@ -/

-- will not work
-- #eval id'' Nat 3

#eval @id'' Nat 3

/- @@@
Lean's standard library includes the polymorphic
identity function for you. It's called `id`. Let's
look at its type and a few applications.
@@@ -/

#check id''     -- C-style and explicit args
#check (id'')   -- → notation and meta-variables
#check @id''    -- C-style and explicit args
#check (@id'')  -- → notation, explicit args (my fav)


/- @@@
## Parametricity

Parametric polymorphism depends on the implentation
*not* relying on any knowledge at all of its actual
argument type. Polymorphic functions must handle their
arguments as entirely *opaque*. You cannot *match* on
a value of a polynmorphic type argument. Interestingly
polymorphic functions sometimes have a single unique
implementation, one that's literally forced. How else
can you complete this function definition except with
*a*? There is no other choice!
@@@ -/

def id''' {α : Sort u} (a : α) : α := a

/- @@@

(Note the alternative function definition syntax used
in this case. Rather than α → α and fun a => a, we've
moved the first α argument to the left of the colon and
gave it a name, making its scope global; then we return
just *a* rather than *fun a => a*.

## Binding Names to Arguments

Moving an argument to the left of the , which should
look to you like ordinary, say, Python, syntax, means
that a name must be bound to it right there, (unless
it's unused in the body, where _ works). Our earlier
examples bound names during pattern matching. You then
cannot pattern match using `|` function notation on a
value for which a name is already bound. Use *match*
instead.
@@@ -/

-- This is fine
def yep : Bool → Bool
| true => true
| false => false

-- def nope (b : Bool) : Bool
-- | true => true
-- | false => false

def yep' (b : Bool) : Bool :=
match b with
| true => true
| false => false

/- @@@
## Abstract Data/Proof Types
- inductive definition
- elimination functions
- domain-specific notations
- domain-soecific functions
- domain-specific syntax
- already proven theorems
- proof automations
@@@ -/

/- @@@
## Example: Bool
@@@ -/

namespace hide

/- @@@
Here's the standard definition of Bool.
@@@ -/

inductive Bool where
| true
| false

/- @@@
Suppose we want to define a function from Bool to some
other type, β, where the return value of type β
To define any function whose behavior depends on
the actual value of the argument requires case analysis
@@@ -/

-- elimination function: provide result for each case
def myBoolElim
  {α : Sort u}
  (b : Bool)
  (f : Bool → α)
  (t: Bool → α) :=
match b with
| Bool.true => t b
| Bool.false => f b




end hide
