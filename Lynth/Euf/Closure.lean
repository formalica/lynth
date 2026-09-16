

/-!
Congruence-free equality closure (union-find over `Eq` hypotheses).

This is the first half of the EUF procedure (cf. Z3's `dyn_ack`,
`smt_cg_table`, congruence-closure core): maintain equivalence classes
of terms from `Eq` hypotheses and prove new equalities by `Eq.trans` /
`Eq.symm` chains. Congruence over applications (`a = b → f a = f b`)
lands next; the union-find core here is shared.
-/
namespace Lynth.Euf

/-- Union-find over `Nat`-indexed nodes. -/
structure UnionFind where
  parent : Array Nat
  deriving Repr

/-- Fresh union-find with `n` singleton nodes. -/
def UnionFind.mk' (n : Nat) : UnionFind :=
  { parent := Array.range n }

/-- Find with path compression, bounded by fuel (always terminates). -/
def UnionFind.find (uf : UnionFind) (x : Nat) (fuel : Nat := uf.parent.size + 1) : Nat :=
  match fuel with
  | 0 => x
  | fuel + 1 =>
    let p := uf.parent[x]!
    if p == x then x else uf.find p fuel

/-- Union two nodes. -/
def UnionFind.union (uf : UnionFind) (x y : Nat) : UnionFind :=
  let rx := uf.find x
  let ry := uf.find y
  if rx == ry then uf
  else { parent := uf.parent.set! rx ry }

/-- Representative query (fuel-bounded, total). -/
def UnionFind.repr (uf : UnionFind) (x : Nat) : Nat :=
  uf.find x

end Lynth.Euf
