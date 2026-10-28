#check Empty.rec
#check PUnit.rec
#check Bool.rec

/- @@@
Bool.rec.{u} {motive : Bool → Sort u} (false : motive false) (true : motive true) (t : Bool) : motive t
-/

#check Nat.rec

/-
Nat.rec.{u}
  {motive : Nat → Sort u}
  (zero : motive Nat.zero)
  (succ : (n : Nat) → motive n → motive n.succ)
  (t : Nat) :
  motive t
-/

-- every single data type comes with its own induction principle

inductive natTree where
| empty
| node (left right : natTree)

#check natTree.rec

/-- @@@
natTree.rec.{u} {motive : natTree → Sort u} (empty : motive natTree.empty)
  (node : (left right : natTree) → motive left → motive right → motive (left.node right)) (t : natTree) : motive t
@@@ -/
