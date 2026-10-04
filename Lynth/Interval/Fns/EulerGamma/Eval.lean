import Lynth.Interval.Fns.EulerGamma.Bound
import Lynth.Interval.Fns.Log
import Lynth.Interval.Fns.Exp

/-!
# Euler–Mascheroni via Brent–McMillan B3: interval evaluator

Computes `γ` the way FLINT does (`mp_real/const_euler.c`): for an integer
parameter `m ≥ 1` with `x = m²`,

```
γ ≈ A_N/B_N − K/B_N² − log m
A_N = Σ_{k<N} H_k·x^k/(k!)²,  B_N = Σ_{k<N} x^k/(k!)²,
K   = (1/4m)·Σ_{k<2m} ((2k)!)³/((k!)⁴·(16m)^{2k}),
```

with rigorous error from the proved theorems in `EulerGamma.Bound`
(`eulerMascheroni_bmk`: `24·e^{−8m}`) and `EulerGamma.SeriesBounds`
(`bmA_tail`, `bmB_tail`: truncation).  `A_N`, `B_N` come from one joint
fold sharing the term recurrence `t_{k+1} = t_k·m²/(k+1)²` (our kernel's
analogue of FLINT's dual-number single splitting); `K` from its own
short fold.  Every rounded operation is sound by the `Ival` lemmas, so
no global rounding analysis is needed — the analytic radius is added on
top with `Ival.widen`.
-/

namespace Lynth.Interval.Fns

open Lynth.Interval Dy
open scoped Nat

/-- point membership for `ℕ` literals. -/
theorem mem_pt_nat (n : Nat) : ((n : ℕ) : ℝ) ∈ Ival.pt (Dy.ofNat n) := by
  have h := Ival.mem_pt (Dy.ofNat n)
  simpa [toReal_def, toRat_ofNat] using h

/-- point membership for `1`. -/
theorem mem_pt_one : (1 : ℝ) ∈ Ival.pt (Dy.ofNat 1) := by
  have h := mem_pt_nat 1
  simpa using h

/-- point membership for `0`. -/
theorem mem_pt_zero : (0 : ℝ) ∈ Ival.pt Dy.zero := by
  have h := Ival.mem_pt Dy.zero
  simpa [toReal_def, toRat_zero] using h

/-- B3 parameter from working precision `p` (mantissa bits):
`24·e^{−8m}` lands far below `2^{−p}`. -/
def eulerM (p : Nat) : Nat := p / 8 + 6

/-- truncation count (`m < N + 1`, as the tail lemmas need). -/
def eulerN (p : Nat) : Nat := 5 * eulerM p + 10

theorem eulerM_ge (p : Nat) : 1 ≤ eulerM p := by unfold eulerM; omega

theorem eulerN_ge (p : Nat) : 1 ≤ eulerN p := by
  unfold eulerN; have := eulerM_ge p; omega

theorem eulerM_lt_eulerN (p : Nat) : (eulerM p : ℝ) < (eulerN p : ℝ) + 1 := by
  have h : eulerM p + 1 ≤ eulerN p := by unfold eulerN; have := eulerM_ge p; omega
  have h2 : ((eulerM p : ℝ) + 1) ≤ ((eulerN p : ℕ) : ℝ) := by
    exact_mod_cast h
  linarith

/-! ### Joint `A`/`B` fold -/

/-- fold state: term, harmonic number, and both partial sums. -/
structure BMState where
  t : Ival
  h : Ival
  sa : Ival
  sb : Ival

/-- one step at index `k` (all operations rounded at precision `w`). -/
def bmStep (w m k : Nat) (s : BMState) : BMState :=
  { t := Ival.div w (Ival.mul w s.t (Ival.pt (Dy.ofNat (m * m))))
      (Ival.pt (Dy.ofNat ((k + 1) * (k + 1))))
    h := Ival.add w s.h
      (Ival.div w (Ival.pt (Dy.ofNat 1)) (Ival.pt (Dy.ofNat (k + 1))))
    sa := Ival.add w s.sa (Ival.mul w s.h s.t)
    sb := Ival.add w s.sb s.t }

/-- `n` steps from `(t₀, H₀, A₀, B₀) = (1, 0, 0, 0)`. -/
def bmFold (w m : Nat) : Nat → BMState
  | 0 => ⟨Ival.pt (Dy.ofNat 1), Ival.pt Dy.zero, Ival.pt Dy.zero, Ival.pt Dy.zero⟩
  | n + 1 => bmStep w m n (bmFold w m n)

/-- real term identity for the step, in the same shape as the fold. -/
theorem bmT_succ (m n : Nat) :
    bmBterm (((m : ℝ) ^ 2)) (n + 1)
    = bmBterm (((m : ℝ) ^ 2)) n * ((m * m : ℕ) : ℝ)
      / ((((n + 1) * (n + 1) : ℕ)) : ℝ) := by
  simp only [bmBterm, Nat.factorial_succ]
  have h1 : ((n ! : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : ((n : ℝ) + 1) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  push_cast
  field_simp
  ring

/-- real harmonic identity for the step. -/
theorem bmH_succ (n : Nat) :
    ((harmonic (n + 1) : ℚ) : ℝ)
      = ((harmonic n : ℚ) : ℝ) + 1 / (((n + 1 : ℕ)) : ℝ) := by
  rw [harmonic_succ]; push_cast; rw [one_div]

/-- the fold encloses the true partial sums. -/
theorem mem_bmFold (w m n : Nat) :
    bmBterm (((m : ℝ) ^ 2)) n ∈ (bmFold w m n).t
    ∧ ((harmonic n : ℚ) : ℝ) ∈ (bmFold w m n).h
    ∧ (∑ j ∈ Finset.range n, ((harmonic j : ℚ) : ℝ) * bmBterm (((m : ℝ) ^ 2)) j)
      ∈ (bmFold w m n).sa
    ∧ (∑ j ∈ Finset.range n, bmBterm (((m : ℝ) ^ 2)) j)
      ∈ (bmFold w m n).sb := by
  induction n with
  | zero =>
    have h0t : bmBterm (((m : ℝ) ^ 2)) 0 = 1 := by simp [bmBterm]
    simp only [bmFold, Finset.range_zero, Finset.sum_empty]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h0t]; exact mem_pt_one
    · have h := mem_pt_zero
      simpa [harmonic_zero] using h
    · simpa using mem_pt_zero
    · simpa using mem_pt_zero
  | succ n ih =>
    obtain ⟨iht, ihh, ihsa, ihsb⟩ := ih
    simp only [bmFold, bmStep]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- term step
      rw [bmT_succ]
      exact Ival.mem_div (Ival.mem_mul iht (mem_pt_nat (m * m)))
        (mem_pt_nat ((n + 1) * (n + 1)))
    · -- harmonic step
      rw [bmH_succ]
      exact Ival.mem_add ihh (Ival.mem_div mem_pt_one (mem_pt_nat (n + 1)))
    · -- A sum step
      rw [Finset.sum_range_succ]
      exact Ival.mem_add ihsa (Ival.mem_mul ihh iht)
    · -- B sum step
      rw [Finset.sum_range_succ]
      exact Ival.mem_add ihsb iht

/-! ### `K` fold -/

/-- `K` fold state: current term and partial sum. -/
structure BMKState where
  u : Ival
  sk : Ival

/-- one step at index `k`:
`u_{k+1} = u_k·(2k+1)³(2k+2)³/((k+1)⁴(16m)²)`. -/
def bmKStep (w m k : Nat) (s : BMKState) : BMKState :=
  let num := (2 * k + 1) ^ 3 * (2 * k + 2) ^ 3
  let den := (k + 1) ^ 4 * (16 * m) ^ 2
  { u := Ival.div w (Ival.mul w s.u (Ival.pt (Dy.ofNat num)))
      (Ival.pt (Dy.ofNat den))
    sk := Ival.add w s.sk s.u }

/-- `n` steps from `(u₀, K₀) = (1, 0)`; run for `n = 2m`. -/
def bmKFold (w m : Nat) : Nat → BMKState
  | 0 => ⟨Ival.pt (Dy.ofNat 1), Ival.pt Dy.zero⟩
  | n + 1 => bmKStep w m n (bmKFold w m n)

/-- real ratio identity for the `K` step, in the same shape as the fold. -/
theorem bmU_succ (m n : Nat) (hm : 1 ≤ m) :
    bmKterm ((m : ℝ)) (n + 1)
    = bmKterm ((m : ℝ)) n
      * ((((2 * n + 1) ^ 3 * (2 * n + 2) ^ 3 : ℕ)) : ℝ)
      / ((((n + 1) ^ 4 * (16 * m) ^ 2 : ℕ)) : ℝ) := by
  simp only [bmKterm, Nat.factorial_succ]
  have e2 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
  rw [e2]
  simp only [Nat.factorial_succ]
  have h1 : ((2 * n)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : ((n ! : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : ((n : ℝ) + 1) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have h4 : (2 * (n : ℝ) + 2) ≠ 0 := by exact_mod_cast (by omega : 2 * n + 2 ≠ 0)
  have h5 : (2 * (n : ℝ) + 1) ≠ 0 := by exact_mod_cast (by omega : 2 * n + 1 ≠ 0)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have ep : (16 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hm0
  have epm : (16 * (m : ℝ)) ^ (2 * n) ≠ 0 := pow_ne_zero _ ep
  push_cast
  field_simp
  ring

/-- the `K` fold encloses the true partial sums. -/
theorem mem_bmKFold (w m n : Nat) (hm : 1 ≤ m) :
    bmKterm ((m : ℝ)) n ∈ (bmKFold w m n).u
    ∧ (∑ j ∈ Finset.range n, bmKterm ((m : ℝ)) j) ∈ (bmKFold w m n).sk := by
  induction n with
  | zero =>
    have h0u : bmKterm ((m : ℝ)) 0 = 1 := by simp [bmKterm]
    simp only [bmKFold, Finset.range_zero, Finset.sum_empty]
    refine ⟨?_, ?_⟩
    · rw [h0u]; exact mem_pt_one
    · simpa using mem_pt_zero
  | succ n ih =>
    obtain ⟨ihu, ihsk⟩ := ih
    simp only [bmKFold, bmKStep]
    refine ⟨?_, ?_⟩
    · rw [bmU_succ m n hm]
      exact Ival.mem_div
        (Ival.mem_mul ihu (mem_pt_nat ((2 * n + 1) ^ 3 * (2 * n + 2) ^ 3)))
        (mem_pt_nat ((n + 1) ^ 4 * (16 * m) ^ 2))
    · rw [Finset.sum_range_succ]
      exact Ival.mem_add ihsk ihu

/-! ### Radius and combination -/

/-- exact-`ℚ` analytic radius from Dy upper bounds of `A_N`, `B_N`, `K`
and of `exp(−8m)`: truncation pieces plus the B3 bound. -/
def eulerRadQ (m N : Nat) (ahi bhi khi ehi : ℚ) : ℚ :=
  let xq : ℚ := (m : ℚ) ^ 2
  let tB : ℚ := xq ^ N / ((N ! : ℚ)) ^ 2
  let qq : ℚ := xq / (((N : ℚ) + 1) ^ 2)
  let eB : ℚ := tB / (1 - qq)
  let eA : ℚ := tB * ((harmonic N : ℚ) / (1 - qq) + qq / (((N : ℚ) + 1) * (1 - qq) ^ 2))
  24 * ehi + eA + ahi * eB + khi * eB * (2 * bhi + eB)

/-- the enclosure: midpoint from the folds, widened by the radius
(`top` on the impossible path where a bound is missing). -/
def eulerBMIval (c : Ctx) : Ival :=
  let w := c.prec + 8
  let m := eulerM c.prec
  let N := eulerN c.prec
  let s := bmFold w m N
  let sk := bmKFold w m (2 * m)
  let r := Ival.div w s.sa s.sb
  let kk := Ival.div w (Ival.div w sk.sk (Ival.pt (Dy.ofNat (4 * m))))
    (Ival.mul w s.sb s.sb)
  let l := logIval c (Ival.pt (Dy.ofNat m))
  let mid := Ival.sub w (Ival.sub w r kk) l
  match s.sa.hi, s.sb.hi, sk.sk.hi,
      (expIval c (Ival.pt (Dy.ofInt (-8 * (m : Int))))).hi with
  | some ahi, some bhi, some khi, some ehi =>
    Ival.widen w mid (Dy.ofRatU w (eulerRadQ m N ahi.toRat bhi.toRat khi.toRat ehi.toRat))
  | _, _, _, _ => Ival.top

/-- partial sums of `B` stay above `1` (terms nonneg, first term `1`). -/
theorem one_le_bmPSumB (x : ℝ) (hx : 0 ≤ x) (N : Nat) (hN : 1 ≤ N) :
    1 ≤ ∑ j ∈ Finset.range N, bmBterm x j := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have h1 : bmBterm x 0 = 1 := by simp [bmBterm]
  have hnn : ∀ j ∈ Finset.range (n + 1), 0 ≤ bmBterm x j := by
    intro j _
    unfold bmBterm
    apply div_nonneg (pow_nonneg hx _)
    positivity
  have hle := Finset.single_le_sum (fun i hi => hnn i hi)
    (Finset.mem_range.mpr (by omega : 0 < n + 1))
  rwa [h1] at hle

theorem mem_eulerBMIval {c : Ctx} (hc : c.Valid) :
    Real.eulerMascheroniConstant ∈ eulerBMIval c := by
  -- parameters and their arithmetic
  have hm0 : 1 ≤ eulerM c.prec := eulerM_ge _
  have hN10 : 1 ≤ eulerN c.prec := eulerN_ge _
  have hNm0 : ((eulerM c.prec : ℕ) : ℝ) < ((eulerN c.prec : ℕ) : ℝ) + 1 :=
    eulerM_lt_eulerN _
  set w := c.prec + 8 with hw
  set m := eulerM c.prec with hmdef
  set N := eulerN c.prec with hNdef
  have hm : 1 ≤ m := by rw [hmdef]; exact hm0
  have hN1 : 1 ≤ N := by rw [hNdef]; exact hN10
  have hNm : (m : ℝ) < (N : ℝ) + 1 := by rw [hmdef, hNdef]; exact hNm0
  -- fold memberships (exact-real partial sums)
  obtain ⟨_, _, hsa, hsb⟩ := mem_bmFold w m N
  obtain ⟨_, hksk⟩ := mem_bmKFold w m (2 * m) hm
  -- real abbreviations
  set AN : ℝ := ∑ j ∈ Finset.range N, bmAterm (((m : ℝ) ^ 2)) j with hAN
  set BN : ℝ := ∑ j ∈ Finset.range N, bmBterm (((m : ℝ) ^ 2)) j with hBN
  set KN : ℝ := (∑ j ∈ Finset.range (2 * m), bmKterm ((m : ℝ)) j)
    / ((4 * m : ℕ) : ℝ) with hKN
  set L : ℝ := Real.log (m : ℝ) with hL
  have hBN1 : 1 ≤ BN := by
    rw [hBN]
    exact one_le_bmPSumB _ (by positivity) _ hN1
  have hBN0 : BN ≠ 0 := ne_of_gt (by linarith [hBN1])
  -- the exact-real approximation enclosed by `mid`
  set v : ℝ := AN / BN - KN / (BN * BN) - L with hv
  have hlog : L ∈ logIval c (Ival.pt (Dy.ofNat m)) := by
    rw [hL]; exact mem_logIval hc (mem_pt_nat m)
  have hvmid : v ∈ (let s := bmFold w m N
      let sk := bmKFold w m (2 * m)
      Ival.sub w (Ival.sub w (Ival.div w s.sa s.sb)
        (Ival.div w (Ival.div w sk.sk (Ival.pt (Dy.ofNat (4 * m))))
          (Ival.mul w s.sb s.sb)))
        (logIval c (Ival.pt (Dy.ofNat m)))) := by
    rw [hv, hAN, hBN, hKN]
    exact Ival.mem_sub (Ival.mem_sub
      (Ival.mem_div hsa hsb)
      (Ival.mem_div (Ival.mem_div hksk (mem_pt_nat (4 * m)))
        (Ival.mem_mul hsb hsb))) hlog
  -- unfold the enclosure and split on bound availability
  unfold eulerBMIval
  simp only [hw, hmdef, hNdef] at hvmid ⊢
  split
  · rename_i ahi bhi khi ehi ha hb hc2 hd
    -- upper bounds from the enclosures
    have hAhi : AN ≤ ahi.toReal := by rw [hAN]; exact hsa.2 ahi ha
    have hBhi : BN ≤ bhi.toReal := by rw [hBN]; exact hsb.2 bhi hb
    have hSKle : (∑ j ∈ Finset.range (2 * m), bmKterm ((m : ℝ)) j) ≤ khi.toReal := by
      exact hksk.2 khi hc2
    have hKNSnn : 0 ≤ (∑ j ∈ Finset.range (2 * m), bmKterm ((m : ℝ)) j) :=
      Finset.sum_nonneg fun j _ => by
        unfold bmKterm
        apply div_nonneg (by positivity)
        apply mul_nonneg (by positivity)
        apply pow_nonneg (by positivity)
    have h4m1 : (1 : ℝ) ≤ ((4 * m : ℕ) : ℝ) := by
      have h : (1 : ℕ) ≤ 4 * m := by omega
      exact_mod_cast h
    have hKhi : KN ≤ khi.toReal := by
      rw [hKN]
      exact le_trans (div_le_self hKNSnn h4m1) hSKle
    have hKNnn : 0 ≤ KN := by
      rw [hKN]
      exact div_nonneg hKNSnn (by positivity)
    have hexp : Real.exp (-8 * (m : ℝ)) ≤ ehi.toReal := by
      have hpt : ((Dy.ofInt (-8 * (m : Int))).toReal) = -8 * (m : ℝ) := by
        simp [toReal_def, toRat_ofInt]
      have h := mem_expIval c (Ival.mem_pt (Dy.ofInt (-8 * (m : Int))))
      rw [hpt] at h
      exact h.2 ehi hd
    -- tail bounds (folded, as stated)
    have hTA := bmA_tail m N hNm hN1
    have hTB := bmB_tail m N hNm
    have hq1 : (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2) < 1 := q_lt_one m N hNm
    have h1mq : (0 : ℝ) < 1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2) := by linarith [hq1]
    have hANnn : 0 ≤ AN := by
      rw [hAN]
      exact Finset.sum_nonneg fun j _ => by
        apply mul_nonneg
        · exact_mod_cast harmonic_nonneg' j
        · apply div_nonneg (pow_nonneg (by positivity) _) (by positivity)
    have hBge : BN ≤ bmB (((m : ℝ) ^ 2)) := by
      have hx0 : (0 : ℝ) ≤ ((m : ℝ) ^ 2) := by positivity
      have hnn : 0 ≤ ∑' k, bmBterm (((m : ℝ) ^ 2)) (k + N) :=
        tsum_nonneg (fun k => bmBterm_nonneg _ hx0 _)
      have hsplit := (bmB_summable (((m : ℝ) ^ 2))).sum_add_tsum_nat_add N
      have eb1 : BN = ∑ k ∈ Finset.range N, bmBterm (((m : ℝ) ^ 2)) k := by
        rw [hBN]
      have eb2 : bmB (((m : ℝ) ^ 2)) = ∑' k, bmBterm (((m : ℝ) ^ 2)) k := rfl
      rw [eb1, eb2]
      linarith [hsplit, hnn]
    have hB1 : 1 ≤ bmB (((m : ℝ) ^ 2)) := le_trans hBN1 hBge
    have hB0 : bmB (((m : ℝ) ^ 2)) ≠ 0 := ne_of_gt (by linarith [hB1])
    -- radius equation: ℚ formula cast to ℝ
    have hRad : ((eulerRadQ m N ahi.toRat bhi.toRat khi.toRat ehi.toRat : ℚ) : ℝ)
        = 24 * ehi.toReal
          + bmBterm (((m : ℝ) ^ 2)) N
            * ((harmonic N : ℝ) / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2))
              + (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)
                / ((((N : ℝ) + 1) * (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) ^ 2)))
          + ahi.toReal
            * (bmBterm (((m : ℝ) ^ 2)) N
              / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)))
          + khi.toReal * (bmBterm (((m : ℝ) ^ 2)) N
              / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)))
            * (2 * bhi.toReal
              + bmBterm (((m : ℝ) ^ 2)) N
                / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2))) := by
      unfold eulerRadQ
      simp only [Dy.toReal_def, bmBterm]
      push_cast
      ring
    -- the pieces
    have eA : |bmA (((m : ℝ) ^ 2)) - AN|
        ≤ bmBterm ((m : ℝ) ^ 2) N
          * ((harmonic N : ℝ) / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) + (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2) / (((N : ℝ) + 1) * (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) ^ 2)) := by
      rw [hAN]; exact hTA
    have eB : |bmB (((m : ℝ) ^ 2)) - BN|
        ≤ bmBterm (((m : ℝ) ^ 2)) N / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) := by
      rw [hBN]; exact hTB
    have e24 : (24 : ℝ) * Real.exp (-8 * (m : ℝ)) ≤ 24 * ehi.toReal :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    -- `bmK m = KN`: the finite sum is exact
    have hKK : bmK m = KN := by
      rw [hKN]
      simp only [bmK]
      simp only [bmKterm]
      push_cast
      ring
    have hmain := eulerMascheroni_bmk m hm
    -- main bound in subtraction form
    have e1 : |Real.eulerMascheroniConstant - (bmA (((m : ℝ) ^ 2)) / bmB (((m : ℝ) ^ 2))
        - KN / (bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) - L)|
        ≤ 24 * Real.exp (-8 * (m : ℝ)) := by
      rw [← hKK, hL]
      have h := hmain
      have e : (Real.eulerMascheroniConstant
          - (bmA (((m : ℝ) ^ 2)) / bmB (((m : ℝ) ^ 2))
            - bmK m / (bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) - Real.log ((m : ℕ) : ℝ)))
          = (Real.eulerMascheroniConstant - bmA (((m : ℝ) ^ 2)) / bmB (((m : ℝ) ^ 2))
            + bmK m / (bmB (((m : ℝ) ^ 2))) ^ 2 + Real.log ((m : ℕ) : ℝ)) := by
        ring
      rw [e]
      exact h
    -- quotient splitting identities
    have hQ : bmA (((m : ℝ) ^ 2)) / bmB (((m : ℝ) ^ 2)) - AN / BN
        = (bmA (((m : ℝ) ^ 2)) - AN) / bmB (((m : ℝ) ^ 2))
          + AN * (BN - bmB (((m : ℝ) ^ 2))) / (bmB (((m : ℝ) ^ 2)) * BN) := by
      have hBB : bmB (((m : ℝ) ^ 2)) * BN ≠ 0 := mul_ne_zero hB0 hBN0
      field_simp
      ring
    have hKid : KN / (bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) - KN / (BN * BN)
        = KN * (BN - bmB (((m : ℝ) ^ 2))) * (BN + bmB (((m : ℝ) ^ 2)))
          / ((bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) * (BN * BN)) := by
      have hBB : bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2)) ≠ 0 :=
        mul_ne_zero hB0 hB0
      have hNN : BN * BN ≠ 0 := mul_ne_zero hBN0 hBN0
      field_simp
      ring
    -- piece bounds
    have hqA : |bmA (((m : ℝ) ^ 2)) / bmB (((m : ℝ) ^ 2)) - AN / BN|
        ≤ bmBterm ((m : ℝ) ^ 2) N
          * ((harmonic N : ℝ) / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) + (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2) / (((N : ℝ) + 1) * (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) ^ 2))
          + ahi.toReal * (bmBterm ((m : ℝ) ^ 2) N
              / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2))) := by
      rw [hQ]
      refine (abs_add_le _ _).trans ?_
      refine add_le_add ?_ ?_
      · -- |(A−AN)/B| ≤ eA-part
        have hBl : (0 : ℝ) ≤ bmB (((m : ℝ) ^ 2)) := by linarith [hB1]
        rw [abs_div, abs_of_nonneg hBl, div_eq_mul_one_div]
        have h1B : (1 : ℝ) / bmB (((m : ℝ) ^ 2)) ≤ 1 := by
          rw [div_le_one (by linarith [hB1] : (0 : ℝ) < bmB (((m : ℝ) ^ 2)))]
          linarith [hB1]
        have hApartnn : 0 ≤ bmBterm ((m : ℝ) ^ 2) N
          * ((harmonic N : ℝ) / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) + (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2) / (((N : ℝ) + 1) * (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) ^ 2)) := by
          apply mul_nonneg _ _
          · unfold bmBterm
            apply div_nonneg (pow_nonneg (by positivity) _) (by positivity)
          · apply add_nonneg
            · apply div_nonneg _ h1mq.le
              · exact_mod_cast harmonic_nonneg' N
            · apply div_nonneg _ _
              · apply div_nonneg (by positivity) (by positivity)
              · apply mul_nonneg (by positivity) (sq_nonneg _)
        have h1Bnn : (0 : ℝ) ≤ 1 / bmB (((m : ℝ) ^ 2)) :=
          div_nonneg zero_le_one hBl
        have hmul := mul_le_mul eA h1B h1Bnn hApartnn
        simpa only [mul_one] using hmul
      · -- |AN·(BN−B)/(B·BN)| ≤ Ahi·eB-part
        have hBl : (0 : ℝ) ≤ bmB (((m : ℝ) ^ 2)) := by linarith [hB1]
        have hBNl : (0 : ℝ) ≤ BN := by linarith [hBN1]
        have hBp : (0 : ℝ) < bmB (((m : ℝ) ^ 2)) := by linarith [hB1]
        have hBNp : (0 : ℝ) < BN := by linarith [hBN1]
        have hBB : (0 : ℝ) < bmB (((m : ℝ) ^ 2)) * BN := mul_pos hBp hBNp
        rw [abs_div, abs_mul, div_eq_mul_one_div, abs_of_nonneg hBB.le]
        have hden : (1 : ℝ) / (bmB (((m : ℝ) ^ 2)) * BN) ≤ 1 := by
          rw [div_le_one hBB]
          have hmul := mul_le_mul hB1 hBN1 zero_le_one hBl
          simpa only [mul_one] using hmul
        have hahi_nn : (0 : ℝ) ≤ ahi.toReal := hANnn.trans hAhi
        have heBnn : (0 : ℝ) ≤ bmBterm (((m : ℝ) ^ 2)) N
            / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) :=
          div_nonneg (by unfold bmBterm; positivity) h1mq.le
        have hnum : |AN| * |BN - bmB (((m : ℝ) ^ 2))|
            ≤ ahi.toReal * (bmBterm (((m : ℝ) ^ 2)) N
                / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2))) := by
          have h1 : |AN| ≤ ahi.toReal := by
            rw [abs_of_nonneg hANnn]; exact hAhi
          have h2 : |BN - bmB (((m : ℝ) ^ 2))|
              ≤ bmBterm (((m : ℝ) ^ 2)) N
                / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) := by
            rw [abs_sub_comm]; exact eB
          exact mul_le_mul h1 h2 (abs_nonneg _) hahi_nn
        have hdennn : (0 : ℝ) ≤ 1 / (bmB (((m : ℝ) ^ 2)) * BN) :=
          div_nonneg zero_le_one hBB.le
        have hmul := mul_le_mul hnum hden hdennn (mul_nonneg hahi_nn heBnn)
        simpa only [mul_one] using hmul
    have hqK : |KN / (bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) - KN / (BN * BN)|
        ≤ khi.toReal * (bmBterm (((m : ℝ) ^ 2)) N
            / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)))
          * (2 * bhi.toReal
            + bmBterm (((m : ℝ) ^ 2)) N
              / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2))) := by
      rw [hKid, abs_div, abs_mul, abs_mul, div_eq_mul_one_div]
      have hBl : (0 : ℝ) ≤ bmB (((m : ℝ) ^ 2)) := by linarith [hB1]
      have hBNl : (0 : ℝ) ≤ BN := by linarith [hBN1]
      have hBp : (0 : ℝ) < bmB (((m : ℝ) ^ 2)) := by linarith [hB1]
      have hBNp : (0 : ℝ) < BN := by linarith [hBN1]
      have hden0 : (0 : ℝ)
          < (bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) * (BN * BN) :=
        mul_pos (mul_pos hBp hBp) (mul_pos hBNp hBNp)
      rw [abs_of_nonneg hden0.le]
      have hden : (1 : ℝ)
          / ((bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) * (BN * BN)) ≤ 1 := by
        rw [div_le_one hden0]
        have h1 : (1 : ℝ) ≤ bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2)) := by
          have hmul := mul_le_mul hB1 hB1 zero_le_one hBl
          simpa only [mul_one] using hmul
        have h2 : (1 : ℝ) ≤ BN * BN := by
          have hmul := mul_le_mul hBN1 hBN1 zero_le_one hBNl
          simpa only [mul_one] using hmul
        have hBBnn : (0 : ℝ) ≤ bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2)) :=
          zero_le_one.trans h1
        have hmul := mul_le_mul h1 h2 zero_le_one hBBnn
        simpa only [mul_one] using hmul
      have hK1 : |KN| ≤ khi.toReal := by
        rw [abs_of_nonneg hKNnn]; exact hKhi
      have hD : |BN - bmB (((m : ℝ) ^ 2))|
          ≤ bmBterm (((m : ℝ) ^ 2)) N
            / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) := by
        rw [abs_sub_comm]; exact eB
      have hS : |BN + bmB (((m : ℝ) ^ 2))| ≤ 2 * bhi.toReal
          + bmBterm (((m : ℝ) ^ 2)) N
            / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) := by
        have hBB : bmB (((m : ℝ) ^ 2)) ≤ bhi.toReal
            + bmBterm (((m : ℝ) ^ 2)) N
              / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) := by
          have hle : bmB (((m : ℝ) ^ 2)) - BN
              ≤ bmBterm (((m : ℝ) ^ 2)) N
                / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) :=
            le_trans (le_abs_self _) eB
          linarith [hle, hBhi]
        have h1 : |BN + bmB (((m : ℝ) ^ 2))| = BN + bmB (((m : ℝ) ^ 2)) :=
          abs_of_nonneg (by linarith [hBN1, hB1])
        rw [h1]; linarith [hBhi]
      have hkinn : (0 : ℝ) ≤ khi.toReal := le_trans hKNnn hKhi
      have heBnn : (0 : ℝ) ≤ bmBterm (((m : ℝ) ^ 2)) N
          / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) := by
        have htBnn : (0 : ℝ) ≤ bmBterm (((m : ℝ) ^ 2)) N := by
          have h : bmBterm (((m : ℝ) ^ 2)) N
              = ((((m : ℝ) ^ 2) ^ N / ((N ! : ℝ)) ^ 2)) := rfl
          rw [h]; positivity
        exact div_nonneg htBnn h1mq.le
      have h2Bnn : (0 : ℝ) ≤ 2 * bhi.toReal
          + bmBterm (((m : ℝ) ^ 2)) N
            / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) := by
        have hbnn : (0 : ℝ) ≤ bhi.toReal := zero_le_one.trans (hBN1.trans hBhi)
        exact add_nonneg (mul_nonneg (by norm_num) hbnn) heBnn
      have hRHSnn : (0 : ℝ) ≤ (khi.toReal * (bmBterm (((m : ℝ) ^ 2)) N
            / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2))))
          * (2 * bhi.toReal
            + bmBterm (((m : ℝ) ^ 2)) N
              / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2))) :=
        mul_nonneg (mul_nonneg hkinn heBnn) h2Bnn
      have hXY : |KN| * |BN - bmB (((m : ℝ) ^ 2))|
          ≤ khi.toReal * (bmBterm (((m : ℝ) ^ 2)) N
            / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2))) :=
        mul_le_mul hK1 hD (abs_nonneg _) hkinn
      have hXYZ : (|KN| * |BN - bmB (((m : ℝ) ^ 2))|) * |BN + bmB (((m : ℝ) ^ 2))|
          ≤ (khi.toReal * (bmBterm (((m : ℝ) ^ 2)) N
              / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2))))
            * (2 * bhi.toReal
              + bmBterm (((m : ℝ) ^ 2)) N
                / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2))) :=
        mul_le_mul hXY hS (abs_nonneg _) (mul_nonneg hkinn heBnn)
      have hDnn : (0 : ℝ) ≤ 1
          / ((bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) * (BN * BN)) :=
        div_nonneg zero_le_one hden0.le
      have hmul := mul_le_mul hXYZ hden hDnn hRHSnn
      simpa only [mul_one] using hmul
    -- triangle assembly
    have hdiff : Real.eulerMascheroniConstant - v
        = (Real.eulerMascheroniConstant
            - (bmA (((m : ℝ) ^ 2)) / bmB (((m : ℝ) ^ 2))
              - KN / (bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) - L))
          + (bmA (((m : ℝ) ^ 2)) / bmB (((m : ℝ) ^ 2)) - AN / BN)
          - (KN / (bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) - KN / (BN * BN)) := by
      rw [hv]; ring
    have hR : |Real.eulerMascheroniConstant - v|
        ≤ (eulerRadQ m N ahi.toRat bhi.toRat khi.toRat ehi.toRat : ℝ) := by
      rw [hRad]
      calc |Real.eulerMascheroniConstant - v|
          = |(Real.eulerMascheroniConstant
              - (bmA (((m : ℝ) ^ 2)) / bmB (((m : ℝ) ^ 2))
                - KN / (bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) - L))
              + (bmA (((m : ℝ) ^ 2)) / bmB (((m : ℝ) ^ 2)) - AN / BN)
              - (KN / (bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) - KN / (BN * BN))| :=
            congrArg _ hdiff
        _ ≤ |(Real.eulerMascheroniConstant
              - (bmA (((m : ℝ) ^ 2)) / bmB (((m : ℝ) ^ 2))
                - KN / (bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) - L))
              + (bmA (((m : ℝ) ^ 2)) / bmB (((m : ℝ) ^ 2)) - AN / BN)|
              + |KN / (bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) - KN / (BN * BN)| := by
            rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
        _ ≤ (|Real.eulerMascheroniConstant
              - (bmA (((m : ℝ) ^ 2)) / bmB (((m : ℝ) ^ 2))
                - KN / (bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) - L)|
              + |bmA (((m : ℝ) ^ 2)) / bmB (((m : ℝ) ^ 2)) - AN / BN|)
              + |KN / (bmB (((m : ℝ) ^ 2)) * bmB (((m : ℝ) ^ 2))) - KN / (BN * BN)| :=
            add_le_add (abs_add_le _ _) le_rfl
        _ ≤ 24 * ehi.toReal
          + bmBterm (((m : ℝ) ^ 2)) N
            * ((harmonic N : ℝ) / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2))
              + (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)
                / ((((N : ℝ) + 1) * (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) ^ 2)))
          + ahi.toReal
            * (bmBterm (((m : ℝ) ^ 2)) N
              / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)))
          + khi.toReal * (bmBterm (((m : ℝ) ^ 2)) N
              / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)))
            * (2 * bhi.toReal
              + bmBterm (((m : ℝ) ^ 2)) N
                / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2))) := by
          have h2 := add_le_add (add_le_add (le_trans e1 e24) hqA) hqK
          simpa only [add_assoc] using h2
    have hle : (eulerRadQ m N ahi.toRat bhi.toRat khi.toRat ehi.toRat : ℝ)
        ≤ (Dy.ofRatU w (eulerRadQ m N ahi.toRat bhi.toRat khi.toRat ehi.toRat)).toReal := by
      rw [Dy.toReal_def]
      exact_mod_cast Dy.le_ofRatU w _
    exact Ival.mem_widen hvmid (le_trans hR hle)
  · exact Ival.mem_top _

end Lynth.Interval.Fns
