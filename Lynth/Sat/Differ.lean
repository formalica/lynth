import Lynth.Sat.FinVal

/-!
Generic difference bridge: inequality over finite values.

No puzzle-specific content: cells are linearized indices `0..n-1`,
values are `0..k-1`. The constraint "cells `u`, `v` differ" compiles
to `k` binary clauses; input-dependent variants (graph edges, Sudoku
givens, tour adjacency) guard each clause family by a stuck `Bool`
via `condClauses`. Proved once with core axioms only; instantiated
for every inequality in every finite puzzle — usual goals and meta
solver-functions alike.
-/
namespace Lynth.Sat.Differ

open Lynth.Sat
open Lynth.Sat.Gates
open Lynth.Sat.FinVal

/-- Binary difference clause at one value. -/
def diffClause (k u v c : Nat) : Clause :=
  [-Int.ofNat (idxVar k u c), -Int.ofNat (idxVar k v c)]

/-- Difference CNF over explicit cell pairs (closed, usual goals). -/
def diffCNF (k : Nat) (pairs : List (Nat × Nat)) : CNF :=
  pairs.flatMap fun p =>
    (List.finRange k).map fun c => diffClause k p.1 p.2 c.val

/-- Guarded difference family for one pair (parameterized, meta
solver-functions): emitted iff the stuck guard holds. -/
def condDiffPair (k u v : Nat) (guard : Bool) : CNF :=
  condClauses guard (diffCNF k [(u, v)])

/-- Guarded difference CNF over many pairs with per-pair guards. -/
def condDiffCNF (k : Nat) (guards : List (Nat × Nat × Bool)) : CNF :=
  guards.flatMap fun g => condDiffPair k g.1 g.2.1 g.2.2

/-- Soundness (single value): a satisfied difference clause rules out
both cells reading true at that value. -/
theorem diffClause_sound (m : Assignment) (k u v c : Nat)
    (h : checkSat [diffClause k u v c] m = true)
    (hu : evalLit m (Int.ofNat (idxVar k u c)) = some true)
    (hv : evalLit m (Int.ofNat (idxVar k v c)) = some true) :
    False := by
  unfold diffClause at h
  have hd := checkSat_pair_eval m
    (-Int.ofNat (idxVar k u c)) (-Int.ofNat (idxVar k v c)) h
  rcases hd with h1 | h2
  · rw [evalLit_neg, hu] at h1
    simp at h1
  · rw [evalLit_neg, hv] at h2
    simp at h2

/-- Soundness (decoded): satisfied difference families decode to
genuinely different values. -/
theorem diff_sound (n k : Nat) (hk : 0 < k) (m : Assignment)
    (u v : Fin n) (c : Fin k)
    (h : checkSat [diffClause k u.val v.val c.val] m = true)
    (hu : checkSat [[Int.ofNat (idxVar k u.val
      (decodeVal n k hk m u).val)]] m = true)
    (hv : checkSat [[Int.ofNat (idxVar k v.val
      (decodeVal n k hk m v).val)]] m = true)
    (hc : (decodeVal n k hk m u).val = c.val ∧
      (decodeVal n k hk m v).val = c.val) :
    False := by
  have huE := (checkSat_single m _).mp hu
  have hvE := (checkSat_single m _).mp hv
  rw [hc.1] at huE
  rw [hc.2] at hvE
  exact diffClause_sound m k u.val v.val c.val h huE hvE

/-- Completeness (single clause): distinct values satisfy the clause
under the canonical model. -/
theorem diffClause_complete (n k : Nat) (_hk : 0 < k)
    (f : Fin n → Fin k) (u v : Fin n) (c : Fin k)
    (hne : f u ≠ f v) :
    checkSat [diffClause k u.val v.val c.val] (modelOf n k f) = true := by
  unfold diffClause
  -- at least one endpoint differs from `c`
  by_cases hu : f u = c
  · have hv : f v ≠ c := fun h => hne (hu.trans h.symm)
    have hev : evalLit (modelOf n k f)
        (-Int.ofNat (idxVar k v.val c.val)) = some true := by
      have hne_b : decide (f v = c) = false := by simp [hv]
      have he : evalLit (modelOf n k f) ((idxVar k v.val c.val : Nat) : Lit)
          = some (decide (f v = c)) := by
        simpa using modelOf_eval n k _hk f v c
      simp [evalLit_neg, he, hne_b]
    exact checkSat_pair_of_true_right _ _ _ hev
  · have heu : evalLit (modelOf n k f)
        (-Int.ofNat (idxVar k u.val c.val)) = some true := by
      have hne_b : decide (f u = c) = false := by simp [hu]
      have he : evalLit (modelOf n k f) ((idxVar k u.val c.val : Nat) : Lit)
          = some (decide (f u = c)) := by
        simpa using modelOf_eval n k _hk f u c
      simp [evalLit_neg, he, hne_b]
    exact checkSat_pair_of_true_left _ _ _ heu

end Lynth.Sat.Differ
