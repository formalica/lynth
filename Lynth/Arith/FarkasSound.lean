-- Soundness of Farkas combinations (the mathematics behind
-- `Fourier.checkCert`): nonnegative weights combining satisfiable
-- `≤`-rows to `0 < 0` is impossible. This is the reconstruction core
-- for arithmetic refutations; the remaining step (reflecting runtime
-- `LeC` systems into this finite form) is tracked in `docs/Z3-NOTES.md`.
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lynth.Arith.Fourier

namespace Lynth.Arith.FarkasSound

open Finset
open scoped BigOperators
open Lynth.Arith.Fourier

/-- Farkas combination soundness: if every row holds under `v`, no
nonnegative weighting can combine them to a positive constant with a
vanishing left-hand side. -/
theorem farkas_sound {n m : Nat} (A : Fin m → Fin n → Rat)
    (b : Fin m → Rat) (w : Fin m → Rat) (v : Fin n → Rat)
    (hw : ∀ i, 0 ≤ w i)
    (hsys : ∀ i, ∑ j, A i j * v j + b i ≤ 0)
    (hcomb : ∀ j, ∑ i, w i * A i j = 0)
    (hpos : 0 < ∑ i, w i * b i) : False := by
  -- each weighted row is nonpositive
  have hrow : ∀ i ∈ (univ : Finset (Fin m)),
      w i * (∑ j, A i j * v j + b i) ≤ 0 := by
    intro i _
    have h := mul_le_mul_of_nonneg_left (hsys i) (hw i)
    rwa [mul_zero] at h
  have hsum : ∑ i, w i * (∑ j, A i j * v j + b i) ≤ 0 := by
    have h := sum_le_sum hrow
    rwa [sum_const_zero] at h
  -- per-row expansion
  have h1 : ∀ i, w i * (∑ j, A i j * v j + b i)
      = (∑ j, w i * (A i j * v j)) + w i * b i := by
    intro i
    rw [mul_add, mul_sum]
  -- per-column factorisation
  have hper : ∀ j, (∑ i, w i * A i j) * v j
      = ∑ i, w i * (A i j * v j) := by
    intro j
    rw [sum_mul]
    apply sum_congr rfl
    intro i _
    exact mul_assoc _ _ _
  -- recombine and swap sums
  have hexpand : ∑ i, w i * (∑ j, A i j * v j + b i)
      = ∑ j, (∑ i, w i * A i j) * v j + ∑ i, w i * b i := by
    have e1 : (∑ i, w i * (∑ j, A i j * v j + b i))
        = ∑ i, ((∑ j, w i * (A i j * v j)) + w i * b i) :=
      sum_congr rfl fun i _ => h1 i
    have e2 : (∑ i, ((∑ j, w i * (A i j * v j)) + w i * b i))
        = (∑ i, ∑ j, w i * (A i j * v j)) + ∑ i, w i * b i :=
      sum_add_distrib
    have e3 : (∑ i, ∑ j, w i * (A i j * v j))
        = ∑ j, ∑ i, w i * (A i j * v j) := sum_comm
    have e4 : (∑ j, ∑ i, w i * (A i j * v j))
        = ∑ j, (∑ i, w i * A i j) * v j :=
      sum_congr rfl fun j _ => (hper j).symm
    rw [e1, e2, e3, e4]
  -- the left-hand side vanishes by `hcomb`
  have hzero : ∑ j, (∑ i, w i * A i j) * v j = 0 :=
    sum_eq_zero fun j _ => by rw [hcomb j, zero_mul]
  have hcon : ∑ i, w i * b i ≤ 0 := by
    have h := hexpand ▸ hsum
    rwa [hzero, zero_add] at h
  exact absurd (lt_of_lt_of_le hpos hcon) (lt_irrefl _)

/-- Weighted coefficient sum (range form; decidable checker core). -/
def wsum (sys : List LeC) (w : List Rat) (j : Nat) : Rat :=
  ∑ i ∈ Finset.range sys.length, (w.getD i 0) * coeffAt (sys.getD i default) j

/-- Weighted constant sum. -/
def wconst (sys : List LeC) (w : List Rat) : Rat :=
  ∑ i ∈ Finset.range sys.length, (w.getD i 0) * (sys.getD i default).const

/-- Certificate validation: `w` is a genuine Farkas refutation of `sys`
iff weights are nonnegative, the weighted LHS vanishes, and the
weighted constant is positive (`0 < 0` derived). Decidable: this is the
checker the reconstruction theorem consumes in `checkCert_sound`. -/
def checkCert (sys : List LeC) (w : List Rat) : Bool :=
  ((w.length == sys.length) &&
  ((w.all fun k => decide (0 ≤ k)) &&
  (((List.range (nVars sys)).all fun j => wsum sys w j == 0) &&
  (decide ((0 : Rat) < wconst sys w)))))

/-- Denotation of a runtime constraint under `v : Nat → Rat`. -/
def evalLeC (c : LeC) (v : Nat → Rat) : Prop :=
  (∑ j ∈ Finset.range c.coeffs.length, coeffAt c j * v j) + c.const ≤ 0

/-- Denotation of a system: every constraint holds. -/
def denoteSys (sys : List LeC) (v : Nat → Rat) : Prop :=
  ∀ c ∈ sys, evalLeC c v

/-- Every member's width fits under `nVars`. -/
theorem foldl_max_ge (l : List LeC) (acc : Nat) :
    acc ≤ l.foldl (fun m d => Nat.max m d.coeffs.length) acc := by
  induction l generalizing acc with
  | nil => exact Nat.le_refl _
  | cons _ _ ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem mem_le_nVars (l : List LeC) (acc : Nat) (c : LeC) (hc : c ∈ l) :
    c.coeffs.length ≤ l.foldl (fun m d => Nat.max m d.coeffs.length) acc := by
  induction l generalizing acc with
  | nil => simp at hc
  | cons h t ih =>
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at hc
    cases hc with
    | inl heq =>
      rw [heq]
      exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge _ _)
    | inr hmem => exact ih _ hmem

/-- `getD` beyond the length is the default. -/
theorem getD_eq_default_of_le {α : Type} [Inhabited α] (l : List α) (d : α)
    (i : Nat) (h : l.length ≤ i) : l.getD i d = d := by
  induction l generalizing i with
  | nil => simp [List.getD_nil]
  | cons h t ih =>
    cases i with
    | zero => simp at h
    | succ k =>
      simp only [List.getD_cons_succ] at *
      simp only [List.length_cons, Nat.succ_le_succ] at h
      exact ih k (Nat.le_of_succ_le_succ h)

/-- Coefficients past the end are zero. -/
theorem coeffAt_eq_zero_of_le (c : LeC) (j : Nat)
    (h : c.coeffs.length ≤ j) : coeffAt c j = 0 :=
  getD_eq_default_of_le _ _ _ h

/-- Range sums over `getD` agree with univ sums. -/
theorem sum_range_getD_univ {m : Nat} (F : Nat → Rat) :
    (∑ i ∈ Finset.range m, F i) = ∑ i : Fin m, F i.1 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Fin.sum_univ_castSucc]
    have e1 : (∑ i : Fin k, F i.1) = ∑ i : Fin k, F (Fin.castSucc i).1 :=
      Finset.sum_congr rfl fun i _ => rfl
    have e2 : F k = F (Fin.last k).1 := rfl
    rw [e1, e2]

/-- Soundness of validated certificates: a passing `checkCert` means
the denoted system is unsatisfiable. The finite witnesses are read off
the runtime lists (`getD` with defaults past the end). -/
theorem checkCert_sound (sys : List LeC) (w : List Rat) (v : Nat → Rat)
    (hlen : w.length = sys.length)
    (hcert : checkCert sys w = true)
    (hsys : denoteSys sys v) : False := by
  -- unpack the checker conjunctions (definitional unfolding + `&&` split)
  have hunfold : checkCert sys w =
      (((w.length == sys.length) &&
      ((w.all fun k => decide (0 ≤ k)) &&
      (((List.range (nVars sys)).all fun j => wsum sys w j == 0) &&
      (decide ((0 : Rat) < wconst sys w)))))) := rfl
  rw [hunfold, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcert
  have hall : (w.all fun k => decide (0 ≤ k)) = true := hcert.2.1
  have hlhs : ((List.range (nVars sys)).all fun j => wsum sys w j == 0) = true :=
    hcert.2.2.1
  have hconst : (decide ((0 : Rat) < wconst sys w)) = true := hcert.2.2.2
  have hall' : ∀ k ∈ w, (0 : Rat) ≤ k := by
    intro k hk
    have h := (List.all_eq_true.mp hall) k hk
    exact of_decide_eq_true h
  have hlhs' : ∀ j ∈ Finset.range (nVars sys), wsum sys w j = 0 := by
    intro j hj
    have h := (List.all_eq_true.mp hlhs) j hj
    exact beq_iff_eq.mp h
  have hconst' : (0 : Rat) < wconst sys w := of_decide_eq_true hconst
  -- finite witnesses, inlined (keeps higher-order unification Miller-safe)
  have hw : ∀ i : Fin sys.length, 0 ≤ w.getD i.1 0 := by
    intro i
    by_cases h : i.1 < w.length
    · have e : w[i.1]'h = w.getD i.1 (0 : Rat) := List.getElem_eq_getD _
      rw [← e]
      exact hall' _ (List.getElem_mem _)
    · exfalso
      rw [hlen] at h
      exact h i.2
  have hsys' : ∀ i : Fin sys.length,
      (∑ j : Fin (nVars sys),
        coeffAt (sys.getD i.1 default) j.1 * v j.1)
      + (sys.getD i.1 default).const ≤ 0 := by
    intro i
    have hmem : sys.getD i.1 default ∈ sys := by
      have h : i.1 < sys.length := i.2
      have e : sys[i.1]'h = sys.getD i.1 default := List.getElem_eq_getD _
      rw [← e]
      exact List.getElem_mem _
    have h0 := hsys _ hmem
    -- extend the denotation sum from `coeffs.length` to `n`
    have hlen_c : (sys.getD i.1 default).coeffs.length ≤ nVars sys :=
      mem_le_nVars sys 0 _ hmem
    have hext : (∑ j ∈ Finset.range
        (sys.getD i.1 default).coeffs.length,
        coeffAt (sys.getD i.1 default) j * v j)
        = ∑ j ∈ Finset.range (nVars sys),
        coeffAt (sys.getD i.1 default) j * v j :=
      Finset.sum_subset
        (by intro x hx
            simp only [Finset.mem_range] at hx ⊢
            exact Nat.lt_of_lt_of_le hx hlen_c)
        (fun j _ hj => by
          have hj' : (sys.getD i.1 default).coeffs.length ≤ j := by
            simp only [Finset.mem_range, Nat.not_lt] at hj ⊢
            exact hj
          have hz : coeffAt (sys.getD i.1 default) j = 0 :=
            coeffAt_eq_zero_of_le _ _ hj'
          rw [hz, zero_mul])
    have h1 : (∑ j : Fin (nVars sys),
        coeffAt (sys.getD i.1 default) j.1 * v j.1)
        = ∑ j ∈ Finset.range (nVars sys),
          coeffAt (sys.getD i.1 default) j * v j :=
      (sum_range_getD_univ
        (F := fun j => coeffAt (sys.getD i.1 default) j * v j)).symm
    simp only [evalLeC, denoteSys] at h0
    rw [hext, ← h1] at h0
    exact h0
  have hcomb : ∀ j : Fin (nVars sys),
      ∑ i : Fin sys.length,
        w.getD i.1 0 * coeffAt (sys.getD i.1 default) j.1 = 0 := by
    intro j
    have hj : j.1 ∈ Finset.range (nVars sys) :=
      Finset.mem_range.mpr j.2
    have h0 := hlhs' j.1 hj
    simp only [wsum] at h0
    have e : (∑ i ∈ Finset.range sys.length,
        w.getD i 0 * coeffAt (sys.getD i default) j.1)
        = ∑ i : Fin sys.length,
          w.getD i.1 0 * coeffAt (sys.getD i.1 default) j.1 :=
      sum_range_getD_univ
        (F := fun i => w.getD i 0 * coeffAt (sys.getD i default) j.1)
    rw [e] at h0
    exact h0
  have hpos : 0 < ∑ i : Fin sys.length,
      w.getD i.1 0 * (sys.getD i.1 default).const := by
    have e : wconst sys w
        = ∑ i : Fin sys.length,
          w.getD i.1 0 * (sys.getD i.1 default).const :=
      sum_range_getD_univ
        (F := fun i => w.getD i 0 * (sys.getD i default).const)
    rw [e] at hconst'
    exact hconst'
  exact farkas_sound
    (fun i j => coeffAt (sys.getD i.1 default) j.1)
    (fun i => (sys.getD i.1 default).const)
    (fun i => w.getD i.1 0) (fun j => v j.1)
    hw hsys' hcomb hpos

end Lynth.Arith.FarkasSound
