-- FPCourse/Unit2/Week06_Trees.lean

/- @@@
## Week 6: Trees, Mutual Recursion, and Data Structure Invariants

### Overview

Lists are *linear* inductive types: the `cons` constructor has one
recursive occurrence of `List`.  This week we study *branching* inductive
types — trees — where a constructor can have *multiple* recursive occurrences.

Structural induction on trees requires one inductive hypothesis per
recursive subtree.  Correspondingly, structural recursion on trees makes
one recursive call per subtree.

We also introduce **data structure invariants**: global properties that
every well-formed value of a type must satisfy.  Binary search trees (BSTs)
are our running example.  The BST invariant cannot be expressed in the type
alone — it is a *proposition* about the tree.  This motivates the design
choice we will formalise in Week 11: hiding the representation behind a
verified interface.
@@@ -/

namespace Week06

/- @@@
### 6.1  Binary trees

A binary tree is either empty (`leaf`) or a `node` with a value and
two subtrees.
@@@ -/

inductive BTree (α : Type) where
  | leaf : BTree α
  | node : BTree α → α → BTree α → BTree α
  deriving Repr

-- Template: one case per constructor, two recursive calls in node
def BTree.size : BTree α → Nat
  | .leaf        => 0
  | .node l _ r  => 1 + l.size + r.size

def BTree.height : BTree α → Nat
  | .leaf        => 0
  | .node l _ r  => 1 + max l.height r.height

def BTree.mirror : BTree α → BTree α
  | .leaf        => .leaf
  | .node l x r  => .node (r.mirror) x (l.mirror)

-- Build a small test tree
def testTree : BTree Nat :=
  .node (.node .leaf 1 .leaf) 2 (.node .leaf 3 .leaf)

#eval testTree.size     -- 3
#eval testTree.height   -- 2
#eval testTree.mirror

/- @@@
### 6.2  Structural induction on trees

Structural induction on `BTree α`:

1. **Base case**: prove `P .leaf`.
2. **Inductive step**: assume `P l` and `P r` (the two IHs), prove
   `P (.node l x r)`.

The two IHs correspond to the two recursive calls in the function.
@@@ -/

-- mirror does not change size
theorem BTree.mirror_size (t : BTree α) : t.mirror.size = t.size := by
  induction t with
  | leaf         => rfl
  | node l x r ihl ihr =>
    simp [BTree.mirror, BTree.size, ihl, ihr]
    omega

-- mirror is an involution
theorem BTree.mirror_involution (t : BTree α) : t.mirror.mirror = t := by
  induction t with
  | leaf         => rfl
  | node l x r ihl ihr =>
    simp [BTree.mirror, ihl, ihr]

/- @@@
### 6.3  In-order traversal and sorted trees

The **in-order traversal** of a binary tree visits the left subtree,
then the root, then the right subtree.  It produces a list of values.
@@@ -/

def BTree.inorder : BTree α → List α
  | .leaf        => []
  | .node l x r  => l.inorder ++ [x] ++ r.inorder

#eval testTree.inorder   -- [1, 2, 3]

-- inorder of a mirror is the reverse of inorder
theorem BTree.inorder_mirror (t : BTree α) :
    t.mirror.inorder = t.inorder.reverse := by
  induction t with
  | leaf         => rfl
  | node l x r ihl ihr =>
    simp [BTree.mirror, BTree.inorder, ihl, ihr]
    simp [List.reverse_append, List.append_assoc]

/- @@@
### 6.4  Binary search trees

A **binary search tree** is a `BTree Nat` satisfying the **BST invariant**:
for every node `node l x r`:
- every value in `l` is strictly less than `x`
- every value in `r` is strictly greater than `x`

We express this as an inductive proposition.  Note that `IsBST` is *not*
a type — it is a **proof** that a given tree satisfies the invariant.
@@@ -/

-- A helper: all elements in a tree satisfy a predicate
def BTree.allElems (p : α → Prop) : BTree α → Prop
  | .leaf        => True
  | .node l x r  => p x ∧ l.allElems p ∧ r.allElems p

-- The BST invariant
def IsBST : BTree Nat → Prop
  | .leaf        => True
  | .node l x r  =>
      l.allElems (· < x) ∧ r.allElems (· > x) ∧ IsBST l ∧ IsBST r

-- BST lookup: returns true if x is in the BST
def BTree.bstLookup (x : Nat) : BTree Nat → Bool
  | .leaf        => false
  | .node l y r  =>
      if x < y      then l.bstLookup x
      else if x > y then r.bstLookup x
      else true

-- BST insertion: inserts x into a BST, maintaining the invariant
def BTree.bstInsert (x : Nat) : BTree Nat → BTree Nat
  | .leaf        => .node .leaf x .leaf
  | .node l y r  =>
      if x < y      then .node (l.bstInsert x) y r
      else if x > y then .node l y (r.bstInsert x)
      else .node l y r   -- x = y, already present

-- Test
def bst0 : BTree Nat := .leaf
def bst1 := bst0.bstInsert 5
def bst2 := bst1.bstInsert 3
def bst3 := bst2.bstInsert 7

#eval bst3.inorder   -- [3, 5, 7]
#eval bst3.bstLookup 3   -- true
#eval bst3.bstLookup 4   -- false

/- @@@
### 6.5  Mutual recursion

Some types are naturally defined *mutually*: each type refers to the other.
The `mutual` keyword allows this.

A classic example: a tree whose nodes have arbitrarily many children
(*rose tree*), where the children form a forest (a list of trees).
@@@ -/

mutual
  inductive RoseTree (α : Type) where
    | node : α → Forest α → RoseTree α

  inductive Forest (α : Type) where
    | nil  : Forest α
    | cons : RoseTree α → Forest α → Forest α
end

mutual
  def RoseTree.size : RoseTree α → Nat
    | .node _ f => 1 + f.size

  def Forest.size : Forest α → Nat
    | .nil      => 0
    | .cons t f => t.size + f.size
end

/- @@@
### Exercises

1. Prove that `BTree.size t = BTree.inorder t |>.length` for all `t`.
   (Hint: you will need a lemma about the length of concatenated lists.)

2. Define `BTree.map : (α → β) → BTree α → BTree β` and prove that
   `BTree.size (BTree.map f t) = BTree.size t`.

3. Prove that `IsBST bst3` holds.  (Hint: unfold the definition and use
   `decide` for the arithmetic comparisons, or prove it by `simp`.)

4. Prove: for a BST `t` satisfying `IsBST t`,
   `t.inorder` is sorted in strictly increasing order.
   State the sorted predicate first, then prove the theorem.
@@@ -/

-- Exercise stubs
def BTree.map (f : α → β) : BTree α → BTree β
  | .leaf        => .leaf
  | .node l x r  => .node (l.map f) (f x) (r.map f)

theorem BTree.map_size (f : α → β) (t : BTree α) :
    (t.map f).size = t.size := by
  induction t with
  | leaf         => rfl
  | node l x r ihl ihr => simp [BTree.map, BTree.size, ihl, ihr]

theorem BTree.inorder_length (t : BTree α) :
    t.inorder.length = t.size := by
  induction t with
  | leaf         => rfl
  | node l x r ihl ihr =>
    simp [BTree.inorder, BTree.size]
    simp [List.length_append, ihl, ihr]
    omega

end Week06
