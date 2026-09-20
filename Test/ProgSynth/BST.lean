-- Synquid BST tests (demo/BST-Insert.sq, test/current/BST-Delete.sq,
-- test/current/BST-Member.sq), translated: synthesize `insert`,
-- `delete`, `member`.
-- TODO: failing until function synthesis over inductive domains lands.
import Lynth

/-- Binary search tree. -/
inductive BST where
  | empty : BST
  | node : Nat → BST → BST → BST

namespace BST

/-- In-order keys (Synquid's `keys`/`telems` measure). -/
def keys : BST → List Nat
  | .empty => []
  | .node x l r => keys l ++ [x] ++ keys r

/-- Search ordering (Synquid's refinements on the `Node` constructor). -/
def bst : BST → Bool
  | .empty => true
  | .node x l r =>
    bst l && bst r && (keys l).all (· < x) && (keys r).all (x < ·)

/-- Insert: keep the ordering, add the key (`keys t + [x]`, set semantics). -/
def insert
    : { ins : Nat → BST → BST //
        ∀ x t, bst t = true →
          bst (ins x t) = true ∧ keys (ins x t) = (keys t).insert x } := by
  lynth

/-- Delete: keep the ordering, remove the key (`keys t - [x]`). -/
def delete
    : { del : BST → Nat → BST //
        ∀ t x, bst t = true →
          bst (del t x) = true ∧ keys (del t x) = (keys t).erase x } := by
  lynth

/-- Membership: the returned Bool is exactly `x`'s membership in `t`. -/
def member
    : { f : Nat → BST → Bool //
        ∀ x t, bst t = true → f x t = decide (x ∈ keys t) } := by
  lynth

end BST

/-- info: 'BST.insert' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BST.insert
/-- info: 'BST.delete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BST.delete
/-- info: 'BST.member' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BST.member
