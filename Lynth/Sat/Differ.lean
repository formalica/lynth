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

/-- Equality clauses at one value: `xu ↔ xv` (both directions). -/
def eqClausePair (k u v c : Nat) : CNF :=
  [[-Int.ofNat (idxVar k u c), Int.ofNat (idxVar k v c)],
   [-Int.ofNat (idxVar k v c), Int.ofNat (idxVar k u c)]]

/-- Equality CNF over explicit cell pairs (closed, usual goals). -/
def eqCNF (k : Nat) (pairs : List (Nat × Nat)) : CNF :=
  pairs.flatMap fun p =>
    (List.finRange k).flatMap fun c => eqClausePair k p.1 p.2 c.val

/-- Guarded equality family for one pair (parameterized, meta
solver-functions): emitted iff the stuck guard holds. -/
def condEqPair (k u v : Nat) (guard : Bool) : CNF :=
  condClauses guard (eqCNF k [(u, v)])

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

/-- Equality modus ponens: a held equivalence pair transfers truth. -/
theorem eqClause_imp (m : Assignment) (k u v c : Nat)
    (h : checkSat (eqClausePair k u v c) m = true)
    (hu : evalLit m (Int.ofNat (idxVar k u c)) = some true) :
    evalLit m (Int.ofNat (idxVar k v c)) = some true := by
  have hm : [-Int.ofNat (idxVar k u c), Int.ofNat (idxVar k v c)] ∈
      eqClausePair k u v c :=
    List.mem_cons_self
  have hc := checkSat_mem m _ _ hm h
  have hd := checkSat_pair_eval m
    (-Int.ofNat (idxVar k u c)) (Int.ofNat (idxVar k v c)) hc
  rcases hd with h1 | h2
  · rw [evalLit_neg, hu] at h1
    simp at h1
  · exact h2

/-- Equality soundness (decoded): held families decode to equal values. -/
theorem eq_sound_decode (n k : Nat) (hk : 0 < k) (m : Assignment)
    (u v : Fin n)
    (hrowU : checkSat (oneHotRowCNF (rowLits k u.val)) m = true)
    (hrowV : checkSat (oneHotRowCNF (rowLits k v.val)) m = true)
    (h : ∀ c : Fin k,
      checkSat (eqClausePair k u.val v.val c.val) m = true) :
    decodeVal n k hk m u = decodeVal n k hk m v := by
  have hu := decodeVal_of_row n k hk m u hrowU
  have hv := decodeVal_of_row n k hk m v hrowV
  have huE := (checkSat_single m _).mp hu
  have hvE := (checkSat_single m _).mp hv
  -- transfer `u`'s decoded value across to `v`'s row
  have htr : evalLit m
      (Int.ofNat (idxVar k v.val (decodeVal n k hk m u).val)) = some true := by
    have h1 := h (decodeVal n k hk m u)
    have h2 := eqClause_imp m k u.val v.val
      (decodeVal n k hk m u).val h1 huE
    -- `h2` is stated with `(decodeVal .. u).val`; `hvE` with `v`'s:
    -- both mention the same index expression after unfolding
    exact h2
  have huniq := rowLit_unique m k v.val hrowV
    (decodeVal n k hk m u) (decodeVal n k hk m v) htr hvE
  exact Fin.ext huniq

/-- Equality completeness (single): equal values satisfy the pair. -/
theorem eqClause_complete (n k : Nat) (_hk : 0 < k)
    (f : Fin n → Fin k) (u v : Fin n) (c : Fin k)
    (heq : f u = f v) :
    checkSat (eqClausePair k u.val v.val c.val) (modelOf n k f)
      = true := by
  unfold eqClausePair
  by_cases hu : f u = c
  · have hvu : f v = c := heq.symm.trans hu
    have heu : evalLit (modelOf n k f)
        (Int.ofNat (idxVar k u.val c.val)) = some true := by
      have hye : decide (f u = c) = true := by simp [hu]
      have he : evalLit (modelOf n k f) (Int.ofNat (idxVar k u.val c.val))
          = some (decide (f u = c)) := modelOf_eval n k _hk f u c
      simp only [he, hye]
    have hev : evalLit (modelOf n k f)
        (Int.ofNat (idxVar k v.val c.val)) = some true := by
      have hye : decide (f v = c) = true := by simp [hvu]
      have he : evalLit (modelOf n k f) (Int.ofNat (idxVar k v.val c.val))
          = some (decide (f v = c)) := modelOf_eval n k _hk f v c
      simp only [he, hye]
    -- both positives true: both implication clauses hold
    have c1 : checkSat
        [[-Int.ofNat (idxVar k u.val c.val),
          Int.ofNat (idxVar k v.val c.val)]] (modelOf n k f) = true :=
      checkSat_pair_of_true_right _ _ _ hev
    have c2 : checkSat
        [[-Int.ofNat (idxVar k v.val c.val),
          Int.ofNat (idxVar k u.val c.val)]] (modelOf n k f) = true :=
      checkSat_pair_of_true_right _ _ _ heu
    show checkSat
      [[-Int.ofNat (idxVar k u.val c.val),
        Int.ofNat (idxVar k v.val c.val)],
       [-Int.ofNat (idxVar k v.val c.val),
        Int.ofNat (idxVar k u.val c.val)]] (modelOf n k f) = true
    apply checkSat_of_all_single
    intro cl hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact c1
    · exact c2
  · have heu : evalLit (modelOf n k f)
        (-Int.ofNat (idxVar k u.val c.val)) = some true := by
      have hne_b : decide (f u = c) = false := by simp [hu]
      have he : evalLit (modelOf n k f)
          ((idxVar k u.val c.val : Nat) : Lit)
          = some (decide (f u = c)) := by
        simpa using modelOf_eval n k _hk f u c
      simp [evalLit_neg, he, hne_b]
    have hev : evalLit (modelOf n k f)
        (-Int.ofNat (idxVar k v.val c.val)) = some true := by
      have hvN : f v ≠ c := fun hh => hu (heq.trans hh)
      have hne_b : decide (f v = c) = false := by simp [hvN]
      have he : evalLit (modelOf n k f)
          ((idxVar k v.val c.val : Nat) : Lit)
          = some (decide (f v = c)) := by
        simpa using modelOf_eval n k _hk f v c
      simp [evalLit_neg, he, hne_b]
    -- both negated: first clause via left, second via left
    have c1 : checkSat
        [[-Int.ofNat (idxVar k u.val c.val),
          Int.ofNat (idxVar k v.val c.val)]] (modelOf n k f) = true :=
      checkSat_pair_of_true_left _ _ _ heu
    have c2 : checkSat
        [[-Int.ofNat (idxVar k v.val c.val),
          Int.ofNat (idxVar k u.val c.val)]] (modelOf n k f) = true :=
      checkSat_pair_of_true_left _ _ _ hev
    show checkSat
      [[-Int.ofNat (idxVar k u.val c.val),
        Int.ofNat (idxVar k v.val c.val)],
       [-Int.ofNat (idxVar k v.val c.val),
        Int.ofNat (idxVar k u.val c.val)]] (modelOf n k f) = true
    apply checkSat_of_all_single
    intro cl hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact c1
    · exact c2

theorem diff_sound_decode (n k : Nat) (hk : 0 < k) (m : Assignment)
    (u v : Fin n)
    (hrowU : checkSat (oneHotRowCNF (rowLits k u.val)) m = true)
    (hrowV : checkSat (oneHotRowCNF (rowLits k v.val)) m = true)
    (h : ∀ c : Fin k,
      checkSat [diffClause k u.val v.val c.val] m = true) :
    decodeVal n k hk m u ≠ decodeVal n k hk m v := by
  intro hcon
  have hvv : (decodeVal n k hk m u).val = (decodeVal n k hk m v).val :=
    congrArg Fin.val hcon
  have hu := decodeVal_of_row n k hk m u hrowU
  have hv := decodeVal_of_row n k hk m v hrowV
  have huE := (checkSat_single m _).mp hu
  have hvE := (checkSat_single m _).mp hv
  rw [hvv] at huE
  exact diffClause_sound m k u.val v.val _ (h _) huE hvE

/-- Difference completeness (family): distinct values satisfy the row. -/
theorem diffCNF_complete (n k : Nat) (_hk : 0 < k)
    (f : Fin n → Fin k) (u v : Fin n)
    (hne : f u ≠ f v) :
    checkSat (diffCNF k [(u.val, v.val)]) (modelOf n k f) = true := by
  apply checkSat_flatMap
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  subst hx
  apply checkSat_of_all_single
  intro cl hc
  obtain ⟨c, hcm, hfc⟩ := List.mem_map.mp hc
  subst hfc
  exact diffClause_complete n k _hk f u v c hne

/-- Equality completeness (family): equal values satisfy the rows. -/
theorem eqCNF_complete (n k : Nat) (hk : 0 < k)
    (f : Fin n → Fin k) (u v : Fin n)
    (heq : f u = f v) :
    checkSat (eqCNF k [(u.val, v.val)]) (modelOf n k f) = true := by
  apply checkSat_flatMap
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  subst hx
  apply checkSat_of_all_single
  intro cl hc
  obtain ⟨d, _, hfd⟩ := List.mem_flatMap.mp hc
  -- `cl` is one of the pair's two implication clauses
  have hpair := eqClause_complete n k hk f u v d heq
  have hm : cl ∈ eqClausePair k u.val v.val d.val := hfd
  exact checkSat_mem _ _ _ hm hpair

end Lynth.Sat.Differ
