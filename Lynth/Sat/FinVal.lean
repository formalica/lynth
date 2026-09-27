import Lynth.Sat.Gates

/-!
Generic finite-value layer: one-hot cells for `Fin k` values.

No puzzle-specific content: `cell` ranges over `0..n-1` (any finite
index set linearized), `val` over `0..k-1`. Every finite function
`Fin n → Fin k`, every finite relation, every coloring/map/register
instance is a special case by instantiation — the lemmas below are
proved once, applied everywhere.

- `idxVar`: 1-based SAT variable for `(cell, val)`.
- `rowLits` / `cellsCNF`: one-hot rows for all cells.
- `decodeVal`: read a value off a model (first true, default `0`).
- `modelOf`: build a model from a function.
- Correctness: decode reads true / model evaluates, all with core
  axioms only.
-/
namespace Lynth.Sat.FinVal

open Lynth.Sat
open Lynth.Sat.Gates

/-- 1-based SAT variable for `(cell, val)` with `k` values per cell. -/
def idxVar (k cell val : Nat) : Nat := cell * k + val + 1

/-- Row literals for one cell. -/
def rowLits (k cell : Nat) : List Lit :=
  (List.finRange k).map fun c => Int.ofNat (idxVar k cell c.val)

/-- One-hot CNF for `n` cells of `k` values each. -/
def cellsCNF (n k : Nat) : CNF :=
  (List.finRange n).flatMap fun v => oneHotRowCNF (rowLits k v.val)

/-- `idxVar` is injective in the value (fixed `k`, `cell`):
strip the outer `+1`, cancel the common atom. -/
theorem idxVar_inj (k cell : Nat) (c1 c2 : Nat)
    (h : idxVar k cell c1 = idxVar k cell c2) : c1 = c2 := by
  unfold idxVar at h
  exact Nat.add_left_cancel (Nat.add_right_cancel h)

/-- Value rows have no duplicate literals. -/
theorem rowLits_nodup (k cell : Nat) : (rowLits k cell).Nodup := by
  unfold rowLits
  apply List.Nodup.map_on _ (List.nodup_finRange k)
  intro a _ b _ hab
  have h1 : idxVar k cell a.val = idxVar k cell b.val :=
    Int.ofNat_inj.mp hab
  have h2 : a.val = b.val := idxVar_inj k cell _ _ h1
  exact Fin.ext h2

/-- Read cell `v`'s value off a model: first true in its row,
defaulting to `0` (needs `0 < k`). -/
def decodeVal (n k : Nat) (hk : 0 < k) (m : Assignment) (v : Fin n) :
    Fin k :=
  match _hm : (List.finRange k).find?
      (fun c => checkSat [[Int.ofNat (idxVar k v.val c.val)]] m) with
  | some c => ⟨c.val, c.isLt⟩
  | none => ⟨0, hk⟩

/-- Decode reads a true literal: the decoded value's row-lit holds
whenever some value's does. -/
theorem decodeVal_true (n k : Nat) (hk : 0 < k) (m : Assignment)
    (v : Fin n)
    (hexists : ∃ c : Fin k,
      checkSat [[Int.ofNat (idxVar k v.val c.val)]] m = true) :
    checkSat [[Int.ofNat (idxVar k v.val (decodeVal n k hk m v).val)]]
      m = true := by
  match hm : (List.finRange k).find?
      (fun c => checkSat [[Int.ofNat (idxVar k v.val c.val)]] m) with
  | some c =>
    have hpc : (fun c => checkSat [[Int.ofNat (idxVar k v.val c.val)]] m) c
        = true :=
      (List.find?_eq_some_iff_append.mp hm).1
    have hdec : decodeVal n k hk m v = ⟨c.val, c.isLt⟩ := by
      unfold decodeVal
      rw [hm]
    rw [hdec]
    exact hpc
  | none =>
    obtain ⟨c, hc⟩ := hexists
    have hall := List.find?_eq_none.mp hm
    have hmem : c ∈ List.finRange k := List.mem_finRange c
    exact absurd hc (hall c hmem)

/-- Every satisfied cell-block yields a decoded true literal. -/
theorem decodeVal_of_row (n k : Nat) (hk : 0 < k) (m : Assignment)
    (v : Fin n)
    (hrow : checkSat (oneHotRowCNF (rowLits k v.val)) m = true) :
    checkSat [[Int.ofNat (idxVar k v.val (decodeVal n k hk m v).val)]]
      m = true := by
  apply decodeVal_true
  obtain ⟨cu, hcuM, hcuT⟩ := (oneHotRow_correct m _ hrow).1
  unfold rowLits at hcuM
  obtain ⟨c, hcm, hfc⟩ := List.mem_map.mp hcuM
  subst hfc
  exact ⟨c, (checkSat_single m _).mpr hcuT⟩

/-- Model from a function: cell `(v,c)` true iff `f v = c`. -/
def modelOf (n k : Nat) (f : Fin n → Fin k) : Assignment :=
  (List.finRange n).flatMap fun v =>
    (List.finRange k).map fun c => some (decide (f v = c))

/-- FlatMap length with uniform chunk size (generic lifter). -/
theorem length_flatMap_const (l : List α) (f : α → List β) (k : Nat)
    (h : ∀ x ∈ l, (f x).length = k) :
    (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have e1 : ((x :: xs).flatMap f).length
        = (f x).length + ((xs.flatMap f).length) := by
      simp [List.flatMap_cons, List.length_append]
    have hx : x ∈ x :: xs := List.mem_cons.mpr (Or.inl rfl)
    rw [e1, h x hx, ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]
    simp only [List.length_cons]
    ring

/-- Model length. -/
theorem modelOf_length (n k : Nat) (f : Fin n → Fin k) :
    (modelOf n k f).length = n * k := by
  unfold modelOf
  rw [length_flatMap_const _ _ k
    (fun v _ => by simp [List.length_map, List.length_finRange])]
  simp [List.length_finRange]

/-- Lookup as `getD` (proof-free): avoids the dependent-dite motive
issues that block direct `rw` on `lookup`/`getElem` indices. -/
theorem lookup_eq_getD (a : Assignment) (v : Nat) (h0 : 0 < v) :
    lookup a v = a.getD (v - 1) none := by
  unfold lookup List.getD
  by_cases h : v ≤ a.length
  · have hc : 0 < v ∧ v ≤ a.length := ⟨h0, h⟩
    simp [hc]
    have h1 : v - 1 < a.length := by omega
    have heq := List.getElem?_eq_getElem (l := a) (i := v - 1) h1
    simp [heq]
  · have hc : ¬ (0 < v ∧ v ≤ a.length) := by omega
    simp [hc]
    have hle : a.length ≤ v - 1 := by omega
    have hnone := List.getElem?_eq_none (l := a) (i := v - 1) hle
    simp [hnone]

/-- Model lookup at a row literal (completeness direction).
Proof: split the flat model at vertex `v`'s chunk via take/drop,
resolve the lookup condition by `simp` (not `rw [dif_pos]`, which
fails the dependent motive since the proof mentions the model),
then read positionally inside the chunk. -/
theorem modelOf_eval (n k : Nat) (_hk : 0 < k) (f : Fin n → Fin k)
    (v : Fin n) (c : Fin k) :
    evalLit (modelOf n k f)
      (Int.ofNat (idxVar k v.val c.val))
      = some (decide (f v = c)) := by
  have hvar : varOf (Int.ofNat (idxVar k v.val c.val))
      = idxVar k v.val c.val := by
    unfold varOf
    simp
  have hpos : (0 : Lit) < Int.ofNat (idxVar k v.val c.val) := by
    unfold idxVar
    change (0 : Int) < _
    exact Int.natCast_pos.mpr (by omega)
  have hlen : (modelOf n k f).length = n * k :=
    modelOf_length n k f
  have hbound : v.val * k + c.val < n * k := by
    have hc := c.2
    have hv := v.2
    have hb1 : v.val * k + c.val < v.val * k + k := by omega
    have hb2 : v.val * k + k ≤ n * k := by
      have h1 : v.val + 1 ≤ n := v.2
      have h2 : (v.val + 1) * k ≤ n * k := Nat.mul_le_mul_right k h1
      have h3 : v.val * k + k = (v.val + 1) * k := by ring
      omega
    omega
  have hpre : (((List.finRange n).take v.val).flatMap fun w =>
      (List.finRange k).map fun d => some (decide (f w = d))).length
      = v.val * k := by
    rw [length_flatMap_const _ _ k
      (fun w _ => by simp [List.length_map, List.length_finRange])]
    have htl : ((List.finRange n).take v.val).length = v.val := by
      simp [List.length_take, List.length_finRange]
    rw [htl]
  have hsplit : modelOf n k f
      = (((List.finRange n).take v.val).flatMap fun w =>
          (List.finRange k).map fun d => some (decide (f w = d))) ++
        (((List.finRange n).drop v.val).flatMap fun w =>
          (List.finRange k).map fun d => some (decide (f w = d))) := by
    unfold modelOf
    have htd := List.take_append_drop v.val (List.finRange n)
    nth_rewrite 1 [← htd]
    rw [List.flatMap_append]
  have hhead : (List.finRange n).drop v.val
      = v :: (List.finRange n).drop (v.val + 1) := by
    have h1 : v.val < (List.finRange n).length := by
      rw [List.length_finRange]
      exact v.2
    have h2 := List.drop_eq_getElem_cons h1
    have h3 : (List.finRange n)[v.val]'h1 = v := by
      simp
    rw [h3] at h2
    exact h2
  have hcond : 0 < idxVar k v.val c.val ∧
      idxVar k v.val c.val ≤ (modelOf n k f).length := by
    refine ⟨?_, ?_⟩
    · unfold idxVar
      exact Nat.succ_pos _
    · rw [hlen]
      have : idxVar k v.val c.val = v.val * k + c.val + 1 := rfl
      omega
  -- lookup fact via proof-free `getD`/`getElem?` path (direct `rw`
  -- on `getElem` indices fails the dependent motive since the index
  -- proof mentions the rewritten term)
  have hlk : lookup (modelOf n k f) (idxVar k v.val c.val)
      = some (decide (f v = c)) := by
    have h1 : 0 < idxVar k v.val c.val := by
      unfold idxVar
      exact Nat.succ_pos _
    rw [lookup_eq_getD _ _ h1, hsplit]
    simp only [List.getD_eq_getElem?_getD]
    have hle : v.val * k ≤ v.val * k + c.val := Nat.le_add_right _ _
    have hidx : v.val * k + c.val - v.val * k = c.val := by omega
    have hvar_eq : idxVar k v.val c.val - 1 = v.val * k + c.val := by
      unfold idxVar
      omega
    rw [hvar_eq]
    have hleft : (((List.finRange n).take v.val).flatMap fun w =>
        (List.finRange k).map fun d => some (decide (f w = d))).length
        = v.val * k := hpre
    rw [List.getElem?_append_right (by rw [hleft]; omega)]
    rw [hleft] at *
    rw [hidx]
    rw [hhead, List.flatMap_cons]
    have hrow_len : (((List.finRange k).map fun d =>
        some (decide (f v = d)))).length = k := by
      simp [List.length_map, List.length_finRange]
    have hc_lt : c.val < (((List.finRange k).map fun d =>
        some (decide (f v = d)))).length := by
      rw [hrow_len]
      exact c.2
    rw [List.getElem?_append_left hc_lt]
    rw [List.getElem?_map]
    have hlt : c.val < (List.finRange k).length := by
      simp [List.length_finRange, c.2]
    have hget := List.getElem?_eq_getElem (l := List.finRange k)
      (i := c.val) hlt
    have hfc : (List.finRange k)[c.val]'hlt = c := by simp
    rw [hget, hfc]
    simp
  unfold evalLit
  rw [hvar, hlk]
  simp only [ite_true, hpos]

end Lynth.Sat.FinVal
