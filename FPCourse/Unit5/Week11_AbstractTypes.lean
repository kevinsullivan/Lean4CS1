-- FPCourse/Unit5/Week11_AbstractTypes.lean

/- @@@
# Unit 5 — Abstract Types and Module Specifications

## Week 11: Signatures, Structures, and Abstraction Barriers

### Overview

The type system does not, by itself, enforce data structure invariants.
Consider our BST type from Week 6: any value of type `BTree Nat` can be
constructed directly by a client, even one that violates the BST invariant.
The type does not stop you from writing `.node .leaf 5 (.node .leaf 3 .leaf)`
even though 3 < 5 should mean 3 is in the *left* subtree, not the right.

The solution is **abstraction**: hide the representation, expose only
operations that maintain the invariant.

In Lean 4, we use **type classes** as *signatures* (interfaces) and
**instances** as *implementations* (structures).  The `opaque` keyword
hides implementation details.

Key ideas:
- A **signature** declares what operations a type supports, with their
  types and semantic specifications.
- An **implementation** provides concrete definitions satisfying the
  signature.
- **Opaque ascription** makes the representation invisible to clients.
- **Representation independence**: any two implementations satisfying
  the same signature are interchangeable.
@@@ -/

namespace Week11

/- @@@
### 11.1  Type classes as signatures

A **type class** in Lean 4 declares a collection of operations on a type,
together with their type signatures.  Think of it as an *interface* or
*signature* in the module-system sense.

The semantic specification (what the operations *mean*) is expressed as
additional propositions, separate from the type class definition itself.
@@@ -/

-- Signature for a finite dictionary from keys to values
class Dict (κ : Type) (α : Type) where
  empty  : Dict κ α
  insert : κ → α → Dict κ α → Dict κ α
  lookup : κ → Dict κ α → Option α
  delete : κ → Dict κ α → Dict κ α

-- Semantic specification for Dict (stated separately as propositions)
-- These are the *laws* any correct implementation must satisfy.
structure DictLaws (κ : Type) (α : Type) [DecidableEq κ] [Dict κ α] : Prop where
  -- Looking up a key just inserted returns the inserted value
  lookup_insert_same :
    ∀ (k : κ) (v : α) (d : Dict κ α),
      Dict.lookup k (Dict.insert k v d) = some v
  -- Looking up a different key after insert is unchanged
  lookup_insert_diff :
    ∀ (k k' : κ) (v : α) (d : Dict κ α),
      k ≠ k' →
      Dict.lookup k (Dict.insert k' v d) = Dict.lookup k d
  -- Empty has no bindings
  lookup_empty :
    ∀ (k : κ), Dict.lookup k (Dict.empty (κ := κ) (α := α)) = none

/- @@@
### 11.2  Association list implementation

The simplest implementation of `Dict`: a list of key-value pairs.
Lookup scans the list; insert prepends; delete filters.

This implementation is O(n) for all operations.
@@@ -/

-- Association list backed dictionary
def AList (κ : Type) (α : Type) := List (κ × α)

namespace AListDict

def empty' : AList κ α := []

def insert' [DecidableEq κ] (k : κ) (v : α) (d : AList κ α) : AList κ α :=
  (k, v) :: d.filter (fun p => p.1 ≠ k)

def lookup' [DecidableEq κ] (k : κ) (d : AList κ α) : Option α :=
  (d.find? (fun p => p.1 == k)).map (·.2)

def delete' [DecidableEq κ] (k : κ) (d : AList κ α) : AList κ α :=
  d.filter (fun p => p.1 ≠ k)

-- Verify the lookup_insert_same law
theorem lookup_insert_same' [DecidableEq κ] (k : κ) (v : α) (d : AList κ α) :
    lookup' k (insert' k v d) = some v := by
  simp [lookup', insert', List.find?_cons]
  simp [beq_iff_eq]

-- Verify the lookup_empty law
theorem lookup_empty' [DecidableEq κ] (k : κ) :
    lookup' k (empty' (κ := κ) (α := α)) = none := by
  simp [lookup', empty']

end AListDict

/- @@@
### 11.3  The opaque keyword: hiding representation

The `opaque` keyword declares a function or definition whose implementation
is hidden from other modules.  Clients can use the type and the operations,
but cannot access the underlying representation.

This is the Lean 4 equivalent of ML's opaque ascription.
@@@ -/

-- An abstract counter type with a hidden implementation
namespace Counter

private def CounterImpl := Nat

opaque Counter : Type := CounterImpl

opaque Counter.zero : Counter := (0 : CounterImpl)
opaque Counter.inc  : Counter → Counter := Nat.succ
opaque Counter.get  : Counter → Nat     := id

-- The client cannot see that Counter = Nat.
-- They can only use zero, inc, and get.
-- This enforces that Counter values are always non-negative (which Nat
-- guarantees) and created only through the public interface.

-- Laws the counter satisfies (proved once, used by all clients)
theorem Counter.get_zero : Counter.get Counter.zero = 0 := rfl
theorem Counter.get_inc (c : Counter) : Counter.get (Counter.inc c) =
    Counter.get c + 1 := rfl

end Counter

/- @@@
### 11.4  Invariant protection

The key benefit of hiding the representation: clients *cannot* construct
an invalid value.  The only way to obtain a value of the abstract type is
through the constructors the module provides — and those constructors
maintain the invariant.

For a BST, exposing only `empty`, `insert`, and `lookup` (not the
`BTree` constructors) ensures that every BST value in client code was
built by operations that maintain the BST invariant.
@@@ -/

-- Abstract ordered set backed by a BST
namespace OrderedSet

-- We re-use the BTree type from Week 6 but hide it
private abbrev Impl := Week06.BTree Nat

opaque OSet : Type := Impl

opaque OSet.empty  : OSet := .leaf
opaque OSet.insert : Nat → OSet → OSet := Week06.BTree.bstInsert
opaque OSet.member : Nat → OSet → Bool := Week06.BTree.bstLookup

-- These operations maintain IsBST by construction.
-- A client cannot produce an OSet that violates BST order.

-- The specification laws:
-- member x (insert x s) = true
-- member y (insert x s) = member y s  when y ≠ x

end OrderedSet

/- @@@
### 11.5  Representation independence

Two implementations satisfying the same specification produce the same
observable results for any client program.

The formal statement: if `impl₁` and `impl₂` both satisfy `DictLaws`,
then for any client function `f` that uses only the `Dict` operations
(and not the internal representation), `f impl₁ = f impl₂`.

We demonstrate this with a small example: counting elements.
@@@ -/

-- Count of elements is the same for any two correct dicts
-- (here, elements we inserted but did not delete)
-- This holds because the specification uniquely determines the
-- observable behaviour; implementations can differ only in
-- non-observable ways (e.g., order of internal storage).

/- @@@
### Exercises

1. Implement `DictLaws` proofs for the `AListDict` implementation.
   Specifically, prove `lookup_insert_diff`.

2. Implement a second `Dict` instance backed by a sorted association list
   (insertion maintains sorted order).  Verify the `DictLaws`.

3. Write a `Stack` type class with `push`, `pop`, and `peek`.
   State the specification laws: `peek (push x s) = some x`,
   `pop (push x s) = s`.  Provide an instance backed by `List`.

4. Use `opaque` to hide the representation of your `Stack` instance
   and verify that the laws still hold after hiding.
@@@ -/

-- Exercise stubs
class Stack (α : Type) where
  empty : Stack α
  push  : α → Stack α → Stack α
  pop   : Stack α → Stack α
  peek  : Stack α → Option α

structure StackLaws (α : Type) [Stack α] : Prop where
  peek_push : ∀ (x : α) (s : Stack α), Stack.peek (Stack.push x s) = some x
  pop_push  : ∀ (x : α) (s : Stack α), Stack.pop  (Stack.push x s) = s

instance : Stack α where
  empty := []
  push  := List.cons
  pop   := List.tail
  peek  := List.head?

theorem listStackLaws (α : Type) : StackLaws α :=
  { peek_push := fun _ _ => rfl
    pop_push  := fun _ _ => rfl }

end Week11
