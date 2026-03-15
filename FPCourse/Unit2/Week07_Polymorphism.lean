-- FPCourse/Unit2/Week07_Polymorphism.lean

/- @@@
## Week 7: Parametric Polymorphism and Free Theorems

### Overview

A **polymorphic** function works uniformly for all types.  It is
parameterised by a *type variable* — a placeholder that can be
instantiated to any type.

Polymorphism is a *specification tool* as much as a *code reuse* tool.
A more polymorphic type signature is a *stronger* specification: it rules
out more possible implementations.

The strongest illustration of this: some function types have *only one*
total implementation.  The type alone determines the behaviour.

This week also introduces **free theorems**: properties that follow from
a function's type *alone*, without looking at the implementation.
Free theorems are one of the most powerful techniques for reasoning about
polymorphic code.
@@@ -/

namespace Week07

/- @@@
### 7.1  Type variables

In Lean 4, type variables are written with lowercase names and are either
introduced explicitly as `{α : Type}` (curly braces for implicit) or
`(α : Type)` (parentheses for explicit), or inferred automatically
via *auto-bound implicit* variables.

When we write `def id (x : α) : α := x`, Lean automatically makes `α`
an implicit type argument: `id : {α : Type u} → α → α`.
@@@ -/

-- The identity function: the ONLY total function of type α → α
def myId (x : α) : α := x

-- The constant function: the ONLY total function of type α → β → α
def myConst (x : α) (_ : β) : α := x

-- Flip the arguments of a two-argument function
def myFlip (f : α → β → γ) (b : β) (a : α) : γ := f a b

-- Compose two functions (already in stdlib as ∘, shown for clarity)
def myComp (f : β → γ) (g : α → β) (x : α) : γ := f (g x)

#check @myId     -- {α : Type u_1} → α → α
#check @myConst  -- {α : Type u_1} → {β : Type u_2} → α → β → α
#check @myFlip   -- ...

/- @@@
### 7.2  The type determines the function

For many polymorphic types, there is only *one* total implementation.

**Why?** A polymorphic function does not know what type `α` is.  It cannot
inspect the value `x : α`, compare it to other values of type `α`, or
create new values of type `α` from scratch.  The only thing it can do is
move values around — pass them to other functions, return them, store
them in pairs, etc.

**Consequence**: the type `α → α` is inhabited by exactly one *total*
function: the identity.  Any other implementation would either:
- not be total (diverge for some input), or
- require knowing something about `α` that a polymorphic function cannot.

This is the idea behind *parametricity* — a formal theorem that says:
any function of a sufficiently polymorphic type must behave in a
structurally constrained way.
@@@ -/

-- There is essentially one function of type (α → α) → α → α
-- (applying the function once, twice, or n times — but not zero for the
-- interesting non-trivial case)
def applyOnce (f : α → α) (x : α) : α := f x
def applyTwice (f : α → α) (x : α) : α := f (f x)

-- There is only one function of type α → (α → α) → α
-- that is total and uses both arguments: f x = x, or ignores f, or applies f.
-- A polymorphic function cannot do anything else.

/- @@@
### 7.3  Polymorphic data structures

The list, option, pair, and tree types from earlier weeks are all
polymorphic.  They work uniformly for any element type.

The functions over these types inherit the polymorphism: `List.map`,
`List.filter`, `Option.map` are all polymorphic.
@@@ -/

-- Polymorphic list map (redefined for exposition)
def polyMap (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: polyMap f xs

-- A polymorphic tree fold
def BTree.fold (leaf : β) (node : β → α → β → β) : Week06.BTree α → β
  | .leaf       => leaf
  | .node l x r => node (Week06.BTree.fold leaf node l) x
                        (Week06.BTree.fold leaf node r)

/- @@@
### 7.4  Free theorems

A **free theorem** is a property that holds for *any* total implementation
of a given polymorphic type, derived from the type alone.

**Example**: for any function `f : List α → List α` that is parametrically
polymorphic, the following must hold for any `g : α → β`:

```
List.map g (f xs) = f (List.map g xs)
```

This says `f` commutes with `map g`.  Since `f` cannot inspect element
values, it can only rearrange, duplicate, or drop positions — and any such
operation commutes with applying a function elementwise.

We cannot state this fully in Lean 4 without the formal parametricity
theorem, but we can state and prove it for specific functions.
@@@ -/

-- For the specific case f = reverse:
theorem map_reverse_commute (f : α → β) (xs : List α) :
    (xs.reverse).map f = (xs.map f).reverse := by
  induction xs with
  | nil       => rfl
  | cons x xs ih =>
    simp [List.map, List.reverse_cons, List.map_append, ih]

-- For the specific case f = polyMap g:
theorem polyMap_comp (f : β → γ) (g : α → β) (xs : List α) :
    polyMap (f ∘ g) xs = polyMap f (polyMap g xs) := by
  induction xs with
  | nil       => rfl
  | cons x xs ih =>
    simp [polyMap, Function.comp, ih]

/- @@@
### 7.5  Bounded polymorphism: type class constraints

Sometimes a polymorphic function needs to know *something* about its type
variable: for example, that values can be compared.  Lean expresses this
with **type class constraints**.

`[Ord α]` means "type `α` has an ordering".
`[DecidableEq α]` means "equality on `α` is decidable".
`[Repr α]` means "values of type `α` can be printed".

These are the typed-functional-programming equivalents of interfaces.
@@@ -/

-- Sort requires an ordering on elements
def insertSorted [Ord α] (x : α) : List α → List α
  | []      => [x]
  | y :: ys =>
    match Ord.compare x y with
    | .lt => x :: y :: ys
    | .eq => x :: y :: ys
    | .gt => y :: insertSorted x ys

def insertionSort [Ord α] : List α → List α
  | []      => []
  | x :: xs => insertSorted x (insertionSort xs)

#eval insertionSort [3, 1, 4, 1, 5, 9, 2, 6]   -- [1, 1, 2, 3, 4, 5, 6, 9]

/- @@@
### Exercises

1. Write `myFst : α × β → α` and `mySnd : α × β → β`.
   Then write `mySwap : α × β → β × α`.
   Prove that `mySwap (mySwap p) = p`.

2. Write `optionApply : Option (α → β) → Option α → Option β`
   (often called `ap` or `<*>`).

3. Prove the functor identity law for lists:
   `polyMap id xs = xs` for all `xs`.

4. Prove the functor composition law for lists:
   `polyMap (f ∘ g) xs = polyMap f (polyMap g xs)`.
   (This is `polyMap_comp` above — try to prove it without `simp`
   using only `rfl` and `congr`.)
@@@ -/

-- Exercise stubs
def myFst : α × β → α := Prod.fst
def mySnd : α × β → β := Prod.snd
def mySwap (p : α × β) : β × α := (p.2, p.1)

theorem mySwap_involution (p : α × β) : mySwap (mySwap p) = p := rfl

def optionApply : Option (α → β) → Option α → Option β
  | none,   _      => none
  | _,      none   => none
  | some f, some x => some (f x)

theorem polyMap_id (xs : List α) : polyMap id xs = xs := by
  induction xs with
  | nil       => rfl
  | cons x xs ih => simp [polyMap, ih]

end Week07
