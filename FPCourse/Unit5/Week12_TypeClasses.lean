-- FPCourse/Unit5/Week12_TypeClasses.lean

/- @@@
## Week 12: Type Classes as Parametric Module-Level Abstraction

### Overview

In ML-family languages, a **functor** is a module-to-module function:
it takes a module satisfying one signature and produces a module satisfying
another.  Lean 4 expresses this same idea using **type classes** with
constraints.

A type class instance that depends on another type class instance is the
Lean 4 analogue of a functor: given an implementation of `Ord α` (the
"parameter module"), we automatically derive an implementation of
`Comparable (List α)` (the "result module").

The correspondence:

| ML module concept    | Lean 4 concept                          |
|----------------------|-----------------------------------------|
| Signature            | Type class declaration                  |
| Structure            | Type class instance                     |
| Functor              | Instance that takes other instances     |
| Opaque type          | `opaque` keyword                        |
| Parameter signature  | Constraint in instance declaration      |

This week also presents the **Functor**, **Foldable**, and **Traversable**
type classes — three standard abstractions that generalise `map`, `fold`,
and `mapM` to any type constructor that supports them.
@@@ -/

namespace Week12

/- @@@
### 12.1  The Functor type class

The `Functor` type class captures the essential property of `map`:
a type constructor `F : Type → Type` is a functor if it supports a `map`
operation satisfying the two functor laws.

Lean 4 has `Functor` built in.  We redeclare a simplified version
for pedagogy.
@@@ -/

class MyFunctor (F : Type → Type) where
  fmap : (α → β) → F α → F β

-- The functor laws (expressed as a separate structure, as in Week 11)
structure FunctorLaws (F : Type → Type) [MyFunctor F] : Prop where
  fmap_id   : ∀ (x : F α), MyFunctor.fmap id x = x
  fmap_comp : ∀ (f : β → γ) (g : α → β) (x : F α),
    MyFunctor.fmap (f ∘ g) x = MyFunctor.fmap f (MyFunctor.fmap g x)

-- List is a functor
instance : MyFunctor List where
  fmap := List.map

-- Option is a functor
instance : MyFunctor Option where
  fmap := Option.map

-- Prove List satisfies the functor laws
theorem listFunctorLaws : FunctorLaws List :=
  { fmap_id   := fun xs => by simp [MyFunctor.fmap, List.map_id]
    fmap_comp := fun f g xs => by
      simp [MyFunctor.fmap]
      induction xs with
      | nil       => rfl
      | cons x xs ih => simp [List.map, Function.comp, ih] }

-- Prove Option satisfies the functor laws
theorem optionFunctorLaws : FunctorLaws Option :=
  { fmap_id   := fun o => by cases o <;> rfl
    fmap_comp := fun f g o => by cases o <;> rfl }

/- @@@
### 12.2  Functor instance for binary trees

Any type constructor whose values can have their elements transformed
uniformly is a functor.  Binary trees are a natural example.
@@@ -/

instance : MyFunctor Week06.BTree where
  fmap := Week06.BTree.map

theorem btreeFunctorLaws : FunctorLaws Week06.BTree :=
  { fmap_id := fun t => by
      induction t with
      | leaf         => rfl
      | node l x r ihl ihr =>
        simp [MyFunctor.fmap, Week06.BTree.map, ihl, ihr]
    fmap_comp := fun f g t => by
      induction t with
      | leaf         => rfl
      | node l x r ihl ihr =>
        simp [MyFunctor.fmap, Week06.BTree.map, Function.comp, ihl, ihr] }

/- @@@
### 12.3  The Foldable type class

`Foldable` generalises `foldr` to any container:
a type constructor `F : Type → Type` is foldable if we can reduce an
`F α` to a single value by combining elements with a function.
@@@ -/

class MyFoldable (F : Type → Type) where
  foldr : (α → β → β) → β → F α → β

instance : MyFoldable List where
  foldr := List.foldr

instance : MyFoldable Option where
  foldr f z
    | none   => z
    | some x => f x z

instance : MyFoldable Week06.BTree where
  foldr f z t := t.inorder |>.foldr f z

-- toList: extract all elements in traversal order
def toList [MyFoldable F] (xs : F α) : List α :=
  MyFoldable.foldr (fun x acc => x :: acc) [] xs

#eval toList [1, 2, 3]               -- [1, 2, 3]
#eval toList (some 42)               -- [42]
#eval toList (none : Option Nat)     -- []

/- @@@
### 12.4  Parametric type classes: the functor-as-functor pattern

A type class that *requires* another type class in its instance is the
Lean 4 analogue of an ML functor.

Example: to show that `List (α × β)` has an ordering whenever `α` and `β`
do, we write an instance that requires `[Ord α] [Ord β]`.

The parameter signatures (`[Ord α]`, `[Ord β]`) are the "preconditions";
the instance `Ord (α × β)` is the "result module".
@@@ -/

-- Lexicographic ordering on pairs: requires orderings on both components
instance [Ord α] [Ord β] : Ord (α × β) where
  compare p q :=
    match Ord.compare p.1 q.1 with
    | .eq => Ord.compare p.2 q.2
    | ord => ord

-- Dictionary ordering on lists: requires ordering on elements
instance [Ord α] : Ord (List α) where
  compare xs ys := match xs, ys with
    | [],      []      => .eq
    | [],      _ :: _  => .lt
    | _ :: _,  []      => .gt
    | x :: xs, y :: ys =>
      match Ord.compare x y with
      | .eq => Ord.compare xs ys
      | ord => ord

#eval Ord.compare [1, 2, 3] [1, 2, 4]  -- Ordering.lt
#eval Ord.compare [1, 2, 3] [1, 2]     -- Ordering.gt

/- @@@
### 12.5  Generic algorithms via type classes

A function parameterised by a type class is a generic algorithm that
works for any conforming type.  This is the payoff of the functor/foldable
abstraction.
@@@ -/

-- Sum of any foldable container of Nats
def sum [MyFoldable F] (xs : F Nat) : Nat :=
  MyFoldable.foldr (· + ·) 0 xs

#eval sum [1, 2, 3, 4]              -- 10
#eval sum (some 7)                  -- 7

-- Maximum element, if any
def maximum [MyFoldable F] [Ord α] (xs : F α) : Option α :=
  MyFoldable.foldr
    (fun x acc => match acc with
      | none   => some x
      | some y => some (if Ord.compare x y == .gt then x else y))
    none xs

#eval maximum [3, 1, 4, 1, 5, 9, 2, 6]   -- some 9

/- @@@
### Exercises

1. Implement `MyFunctor` for the pair type `(γ × ·)` (mapping over the
   second component).  Prove the functor laws.

2. Define a `Traversable` type class with `traverse : Applicative F → (α → F β) → G α → F (G β)`
   and implement it for `Option`.

3. Implement a `Monoid` type class with `empty : α` and `append : α → α → α`,
   plus the three monoid laws.  Implement it for `List`, `Nat` (with +, 0),
   and `Nat` (with *, 1).  Show that the three implementations are distinct.

4. Prove that any `FunctorLaws` instance satisfies:
   `fmap f (fmap g x) = fmap (f ∘ g) x`
   (the composition law in the other direction).
@@@ -/

-- Exercise stubs
instance [Ord α] : Ord (Week06.BTree α) where
  compare t₁ t₂ := Ord.compare t₁.inorder t₂.inorder

class Monoid' (α : Type) where
  empty'  : α
  append' : α → α → α

structure MonoidLaws (α : Type) [Monoid' α] : Prop where
  left_id  : ∀ x : α, Monoid'.append' Monoid'.empty' x = x
  right_id : ∀ x : α, Monoid'.append' x Monoid'.empty' = x
  assoc    : ∀ x y z : α, Monoid'.append' (Monoid'.append' x y) z =
                           Monoid'.append' x (Monoid'.append' y z)

instance : Monoid' (List α) where
  empty'  := []
  append' := (· ++ ·)

theorem listMonoidLaws (α : Type) : MonoidLaws (List α) :=
  { left_id  := fun xs => rfl
    right_id := fun xs => by simp [Monoid'.append']
    assoc    := fun xs ys zs => by simp [Monoid'.append', List.append_assoc] }

end Week12
