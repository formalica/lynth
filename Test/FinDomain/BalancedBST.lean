-- Finite-domain pilot: balanced binary search tree over a fixed
-- key set, asked via `lynth` + Subtype (like SortPerm).
-- Given the keys [50, 30, 70, 20, 40, 60, 80], build a tree that is
-- BOTH a binary search tree AND balanced (AVL height condition).
-- NOTE: `lynth` should infer finiteness: the tree uses exactly the 7
-- given keys, so there are finitely many shapes (Catalan(6) shapes x
-- 7! orderings) and brute-force enumeration applies.
-- NOTE: `lynth` should also infer that the node values of the output
-- are exactly the input keys, only rearranged (`keysOf.Perm input`)
-- — so it must NOT brute-force the values of the output nodes; the
-- only open choice is the tree shape (which key goes where), and the
-- BST + balance constraints prune that shape search.
-- TODO: failing until custom-inductive synthesis lands in the pipeline.
import Lynth

/-- Binary tree with `Nat` keys at the nodes. -/
inductive BTree where
  | leaf : BTree
  | node : BTree → Nat → BTree → BTree

namespace BTree

/-- Collect all keys (in-order). -/
def keysOf : BTree → List Nat
  | leaf => []
  | node l k r => keysOf l ++ [k] ++ keysOf r

/-- Strictly increasing in-order keys = binary search tree. -/
def bst : BTree → Bool
  | leaf => true
  | node l k r =>
    bst l ∧ bst r ∧
    (keysOf l).all (· < k) ∧ (keysOf r).all (k < ·)

/-- Height of a tree. -/
def height : BTree → Nat
  | leaf => 0
  | node l _ r => 1 + Nat.max (height l) (height r)

/-- AVL balance condition: left/right heights differ by at most 1
at every node. -/
def balanced : BTree → Bool
  | leaf => true
  | node l _ r =>
    balanced l ∧ balanced r ∧
    Nat.abs (height l - height r) ≤ 1

end BTree

/-- The problem instance: fixed key set. -/
def input : List Nat := [50, 30, 70, 20, 40, 60, 80]

/-- Target property: same key multiset, BST, balanced. -/
def treeValid (t : BTree) : Prop :=
  t.keysOf.Perm input ∧ t.bst = true ∧ t.balanced = true

/-- The goal `lynth` must fill: a computable balanced BST over the
instance keys. -/
def treeSol : { t : BTree // treeValid t } := by
  lynth

/-- Etalon: the canonical complete BST over the keys. -/
def etalon : BTree :=
  .node (.node (.node .leaf 20 .leaf) 30 (.node .leaf 40 .leaf)) 50
    (.node (.node .leaf 60 .leaf) 70 (.node .leaf 80 .leaf))

-- The value computed by `lynth`:
#eval (treeSol : BTree)

-- The etalon:
#eval etalon

-- Runtime checks: same keys, BST, balanced.
#guard (treeSol : BTree).keysOf.Perm input
#guard (treeSol : BTree).bst = true
#guard (treeSol : BTree).balanced = true

/-- info: 'treeSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms treeSol
