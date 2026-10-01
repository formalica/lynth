import Lynth.Interval.Fns.Elem
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Gamma function

Rigorous interval enclosure of `Real.Gamma` following FLINT/Arb
(`arb_hypgeom_gamma`, Fredrik Johansson): argument shifting with the
recurrence `Γ(x+1) = x·Γ(x)` until `z = x + r ≥ T`, Stirling expansion of
`log Γ(z)` with an explicit remainder bound, then `Γ(z) = exp (log Γ z)`
divided by the rising factorial.  Nonpositive arguments go through Euler's
reflection formula `Γ(x)·Γ(1-x) = π / sin(πx)`; general intervals are split
at `0` and the pieces joined with `hull`.

The per-function proof obligations that follow from Mathlib facts
(recurrence chaining, reflection, interval composition) are proved here.
The one analytic input — the Stirling expansion with remainder on
`[8, ∞)` — is isolated as the temporary axiom `stirling_logGamma`
(see its docstring).  It is used at every runtime evaluation, so proving
it once (however long that takes) fixes the soundness of all Gamma
goals; nothing else in this file depends on unproved analysis.

Speed notes (runtime matters more than proof length here):
* the hot loop is Horner in `z⁻²` (`stirlingAcc`, structural recursion on a
  `Nat` fuel) plus a short rising-factorial fold; no `ℚ` or well-founded
  recursion in the hot path, so both native and kernel checking stay fast;
* `N` (number of Stirling terms) is chosen adaptively by `chooseN`
  (pure computation, no proofs needed — any `N` is sound);
* Bernoulli numbers never enter the computation: `stirlingCoeff` stores
  the quotients `B_{2k}/(2k(2k-1))` directly as `ℚ` literals.
-/

namespace Lynth.Interval.Fns

open Lynth.Interval Dy

/-! ### Stirling coefficients -/

/-- Stirling coefficient `B_{2k} / (2k * (2k-1))` as an exact rational
(`k = 1..24`, `0` beyond — `chooseN` never returns more than `24`). -/
def stirlingCoeff : Nat → ℚ
  | 1 => 1 / 12
  | 2 => -1 / 360
  | 3 => 1 / 1260
  | 4 => -1 / 1680
  | 5 => 1 / 1188
  | 6 => -691 / 360360
  | 7 => 1 / 156
  | 8 => -3617 / 122400
  | 9 => 43867 / 244188
  | 10 => -174611 / 125400
  | 11 => 77683 / 5796
  | 12 => -236364091 / 1506960
  | 13 => 657931 / 300
  | 14 => -3392780147 / 93960
  | 15 => 1723168255201 / 2492028
  | 16 => -7709321041217 / 505920
  | 17 => 151628697551 / 396
  | 18 => -26315271553053477373 / 2418179400
  | 19 => 154210205991661 / 444
  | 20 => -261082718496449122051 / 21106800
  | 21 => 1520097643918070802691 / 3109932
  | 22 => -2530297234481911294093 / 118680
  | 23 => 25932657025822267968607 / 25380
  | 24 => -5609403368997817686249127547 / 104700960
  | _ => 0

/-- Stirling summand `c_k / z^(2k-1)` (for `k ≥ 1`). -/
noncomputable def stirlingTerm (z : ℝ) (k : ℕ) : ℝ := (stirlingCoeff k : ℝ) / z ^ (2 * k - 1)

/--
Temporary axiom: Stirling expansion of `log Γ` on `[8, ∞)` with an explicit
remainder bound.  This is the real case of FLINT's
`acb_gamma_stirling_bound` (`2|B_{2n}|Γ(2n+k-1)/(Γ(k+1)Γ(2n+1))·|z|·c^{2n+k}`
with `k = 0` and phase factor `c = 1/|z|`, i.e. `2|B_{2n}|/((2n)(2n-1)z^{2n-1})`).

Why it is true: the classical Stieltjes enveloping estimate for the
Stirling series at real `z > 0` (see e.g. Olver, *Asymptotics and Special
Functions*, Ch. 8, or DlMF §5.11): the remainder after `N - 1` terms is at
most twice the first neglected term in absolute value.  The hypothesis
`8 ≤ z` keeps us far from the regime where the optimal-truncation
constant could matter.

How to prove it (once): Euler–Maclaurin summation applied to `log` on
`[1, z]` (Bernoulli-number form with integral remainder), transferred from
`log (n!)` to `log Γ` via `Real.Gamma_nat_eq_factorial` and Bohr–Mollerup
uniqueness, then the integral remainder estimated on `[8, ∞)`.  None of
the Euler–Maclaurin machinery exists in Mathlib yet, so this is a genuine
formalization project — but its statement is exactly what the interval
kernel needs, and every Gamma evaluation bottoms out here.
-/
axiom stirling_logGamma (z : ℝ) (hz : 8 ≤ z) (N : ℕ) (hN : 1 ≤ N) (hN24 : N ≤ 24) :
  ∃ R : ℝ, Real.log (Real.Gamma z)
      = (z - 1 / 2) * Real.log z - z + Real.log (Real.sqrt (2 * Real.pi))
        + (∑ k ∈ Finset.range (N - 1), stirlingTerm z (k + 1)) + R
    ∧ |R| ≤ 2 * |(stirlingCoeff N : ℝ)| / z ^ (2 * N - 1)

/-! ### Argument shift -/

/-- least `r` with `a + r ≥ T`. -/
def gammaShift (a : Dy) (T : Nat) : Nat :=
  if Dy.leB (Dy.ofNat T) a then 0
  else Int.toNat (Int.ceil ((T : ℚ) - a.toRat))

theorem gammaShift_spec (a : Dy) (T : Nat) :
    (T : ℝ) ≤ a.toReal + ((gammaShift a T : ℕ) : ℝ) := by
  unfold gammaShift
  split
  · rename_i h
    have hle : (Dy.ofNat T).toRat ≤ a.toRat := (leB_iff _ _).1 h
    have hT : ((Dy.ofNat T).toRat : ℝ) = (T : ℝ) := by
      simp [toRat_ofNat]
    simp only [Nat.cast_zero, add_zero]
    rw [← hT, toReal_def]
    exact_mod_cast hle
  · rename_i h
    have hlt : a.toRat < (Dy.ofNat T).toRat := lt_of_not_ge (fun h' => h ((leB_iff _ _).2 h'))
    have hT : ((Dy.ofNat T).toRat : ℝ) = (T : ℝ) := by
      simp [toRat_ofNat]
    have hpos : (0 : ℚ) < (T : ℚ) - a.toRat := by
      have : a.toRat < (T : ℚ) := by simpa [toRat_ofNat] using hlt
      linarith
    have hc : (T : ℚ) - a.toRat ≤ (Int.ceil ((T : ℚ) - a.toRat) : ℚ) := Int.le_ceil _
    have hltQ : (0 : ℚ) < (Int.ceil ((T : ℚ) - a.toRat) : ℚ) := lt_of_lt_of_le hpos hc
    have hnn : 0 ≤ Int.ceil ((T : ℚ) - a.toRat) := by
      by_contra hcon
      push Not at hcon
      have hneg : (Int.ceil ((T : ℚ) - a.toRat) : ℚ) < 0 := by exact_mod_cast hcon
      linarith
    have e : ((Int.toNat (Int.ceil ((T : ℚ) - a.toRat)) : ℕ) : ℚ)
        = (Int.ceil ((T : ℚ) - a.toRat) : ℚ) := by
      have e2 : ((Int.toNat (Int.ceil ((T : ℚ) - a.toRat)) : ℕ) : ℤ)
          = Int.ceil ((T : ℚ) - a.toRat) := Int.toNat_of_nonneg hnn
      exact_mod_cast e2
    have hq : (T : ℚ) ≤ a.toRat + ((Int.toNat (Int.ceil ((T : ℚ) - a.toRat)) : ℕ) : ℚ) := by
      rw [e]; linarith
    rw [toReal_def]
    exact_mod_cast hq

/-! ### Rising factorial -/

/-- `x * (x+1) * … * (x+r-1)` (real). -/
def risingReal (x : ℝ) : Nat → ℝ
  | 0 => 1
  | r + 1 => risingReal x r * (x + (r : ℝ))

/-- interval rising factorial. -/
def risingIval (w : Nat) (X : Ival) : Nat → Ival
  | 0 => Ival.one
  | r + 1 => Ival.mul w (risingIval w X r) (Ival.add w X (Ival.ofRat w (r : ℚ)))

theorem mem_risingIval {w : Nat} {x : ℝ} {X : Ival} (hx : x ∈ X) (r : Nat) :
    risingReal x r ∈ risingIval w X r := by
  induction r with
  | zero => simpa [risingReal, risingIval] using Ival.mem_one
  | succ r ih =>
    simp only [risingReal, risingIval]
    have hr : (x + (r : ℝ)) ∈ Ival.add w X (Ival.ofRat w (r : ℚ)) :=
      Ival.mem_add hx (by simpa using Ival.mem_ofRat w (r : ℚ))
    exact Ival.mem_mul ih hr

/-- helper: a zero factor kills the product. -/
theorem risingReal_eq_zero_of {x : ℝ} {r i : Nat} (hi : i < r) (hxi : x + (i : ℝ) = 0) :
    risingReal x r = 0 := by
  induction r with
  | zero => omega
  | succ r ih =>
    simp only [risingReal]
    by_cases h : i < r
    · rw [ih h, zero_mul]
    · have hir : i = r := by omega
      subst hir
      rw [hxi, mul_zero]

/-- recurrence in division form — valid at poles too, because Mathlib's
`Γ` is `0` at nonpositive integers while `_/0 = 0`. -/
theorem gamma_eq_gamma_add_div_rising (x : ℝ) (r : Nat) :
    Real.Gamma x = Real.Gamma (x + (r : ℝ)) / risingReal x r := by
  induction r with
  | zero => simp [risingReal]
  | succ r ih =>
    have hcast : x + ((r + 1 : ℕ) : ℝ) = (x + (r : ℝ)) + 1 := by push_cast; ring
    rw [hcast]
    by_cases h : x + (r : ℝ) = 0
    · have hx : x = -((r : ℕ) : ℝ) := by linarith
      have hzero : risingReal x (r + 1) = 0 := by
        simp only [risingReal]
        rw [h, mul_zero]
      rw [hzero, hx, Real.Gamma_neg_nat_eq_zero]
      have h1 : (-((r : ℕ) : ℝ) + (r : ℝ)) + 1 = 1 := by ring
      rw [h1, Real.Gamma_one, div_zero]
    · have hadd := Real.Gamma_add_one h
      have hR : risingReal x (r + 1) = (x + (r : ℝ)) * risingReal x r := by
        simp [risingReal, mul_comm]
      rw [hadd, hR, mul_div_mul_left _ _ h, ih]

/-! ### Stirling partial sums (Horner in `z⁻²`) -/

/-- `c_{M-j} + W2 * (c_{M-j+1} + …)`: Horner accumulator, `j` levels. -/
def stirlingAcc (w : Nat) (W2 : Ival) (M : Nat) : Nat → Ival
  | 0 => Ival.zero
  | j + 1 =>
    Ival.add w (Ival.ofRat w (stirlingCoeff (M - j)))
      (Ival.mul w W2 (stirlingAcc w W2 M j))

/-- real value of the accumulator. -/
def stirlingAccReal (t : ℝ) (M j : Nat) : ℝ :=
  ∑ i ∈ Finset.range j, (stirlingCoeff (M - j + 1 + i) : ℝ) * t ^ i

theorem mem_stirlingAcc {w : Nat} {W2 : Ival} {M j : Nat} {t : ℝ}
    (ht : t ∈ W2) (hj : j ≤ M) : stirlingAccReal t M j ∈ stirlingAcc w W2 M j := by
  induction j with
  | zero => simpa [stirlingAccReal, stirlingAcc] using Ival.mem_zero
  | succ j ih =>
    have hj' : j ≤ M := by omega
    have h0 : M - (j + 1) + 1 + 0 = M - j := by omega
    have hXY : (∑ i ∈ Finset.range j, (stirlingCoeff (M - j + (i + 1)) : ℝ) * t ^ (i + 1))
        = ∑ i ∈ Finset.range j, t * ((stirlingCoeff (M - j + 1 + i) : ℝ) * t ^ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have eix : M - j + (i + 1) = M - j + 1 + i := by omega
      rw [eix, pow_succ']
      ring
    have hS : stirlingAccReal t M (j + 1)
        = (stirlingCoeff (M - j) : ℝ) + t * stirlingAccReal t M j := by
      simp only [stirlingAccReal, Finset.sum_range_succ', h0, pow_zero, mul_one]
      rw [Finset.mul_sum, hXY]
      exact add_comm _ _
    rw [hS]
    simp only [stirlingAcc]
    exact Ival.mem_add (by simpa using Ival.mem_ofRat w (stirlingCoeff (M - j)))
      (Ival.mem_mul ht (ih hj'))

/-- `z⁻¹ * (c * (z⁻¹ * z⁻¹)^i) = c * (z^(2i+1))⁻¹`. -/
theorem zinv_sq_pow' (z c : ℝ) (i : Nat) :
    z⁻¹ * (c * (z⁻¹ * z⁻¹) ^ i) = c * (z ^ (2 * i + 1))⁻¹ := by
  induction i with
  | zero => simp [mul_comm]
  | succ i ih =>
    have p1 : z⁻¹ * (c * (z⁻¹ * z⁻¹) ^ (i + 1))
        = (z⁻¹ * (c * (z⁻¹ * z⁻¹) ^ i)) * (z⁻¹ * z⁻¹) := by
      rw [pow_succ']; ring
    have e : 2 * (i + 1) + 1 = (2 * i + 1) + 2 := by omega
    rw [p1, ih, e]
    have p2 : c * (z ^ (2 * i + 1))⁻¹ * (z⁻¹ * z⁻¹)
        = c * (z ^ (2 * i + 1) * (z * z))⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev]; ring
    have p3 : z ^ (2 * i + 1) * (z * z) = z ^ ((2 * i + 1) + 2) := by
      conv_rhs => rw [pow_add, pow_two]
    rw [p2, p3]

/-- the Horner value times `z⁻¹` is the axiom's partial sum. -/
theorem stirling_sum_eq {z : ℝ} (N : Nat) :
    (∑ k ∈ Finset.range (N - 1), stirlingTerm z (k + 1))
      = z⁻¹ * stirlingAccReal (z⁻¹ * z⁻¹) (N - 1) (N - 1) := by
  simp only [stirlingAccReal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  have e : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have eN : N - 1 - (N - 1) + 1 + k = k + 1 := by omega
  simp only [stirlingTerm, e, eN, div_eq_mul_inv]
  exact (zinv_sq_pow' z _ k).symm

/-! ### Stirling main term and tail -/

/-- `(z-½) * log z - z + log √(2π)`. -/
def stirlingMain (c : Ctx) (w : Nat) (Z : Ival) : Ival :=
  let logZ := logIval c Z
  let sqrt2pi := Ival.sqrt w (Ival.mul w (Ival.ofRat w 2) c.pi)
  let logSqrt2pi := logIval c sqrt2pi
  let half := Ival.ofRat w (1 / 2)
  Ival.sub w (Ival.add w (Ival.mul w (Ival.sub w Z half) logZ) logSqrt2pi) Z

theorem mem_stirlingMain {c : Ctx} (hc : c.Valid) {z : ℝ} {Z : Ival} (hx : z ∈ Z) :
    (z - 1 / 2) * Real.log z - z + Real.log (Real.sqrt (2 * Real.pi))
      ∈ stirlingMain c w Z := by
  unfold stirlingMain
  simp only
  have hhalf : ((1 / 2 : ℚ) : ℝ) ∈ Ival.ofRat w (1 / 2) := Ival.mem_ofRat _ _
  have h2m : ((2 : ℚ) : ℝ) ∈ Ival.ofRat w 2 := Ival.mem_ofRat _ _
  have e1 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by simp
  have e2 : ((2 : ℚ) : ℝ) = 2 := by simp
  rw [e1] at hhalf
  rw [e2] at h2m
  have hsqrt : Real.sqrt (2 * Real.pi)
      ∈ Ival.sqrt w (Ival.mul w (Ival.ofRat w 2) c.pi) :=
    Ival.mem_sqrt (Ival.mem_mul h2m hc.pi_mem)
  have h : ((z - 1 / 2) * Real.log z + Real.log (Real.sqrt (2 * Real.pi))) - z
      ∈ Ival.sub w (Ival.add w (Ival.mul w (Ival.sub w Z (Ival.ofRat w (1 / 2)))
        (logIval c Z)) (logIval c (Ival.sqrt w (Ival.mul w (Ival.ofRat w 2) c.pi)))) Z :=
    Ival.mem_sub
      (Ival.mem_add
        (Ival.mem_mul
          (Ival.mem_sub hx hhalf)
          (mem_logIval hc hx))
        (mem_logIval hc hsqrt))
      hx
  have eassoc : (z - 1 / 2) * Real.log z - z + Real.log (Real.sqrt (2 * Real.pi))
      = ((z - 1 / 2) * Real.log z + Real.log (Real.sqrt (2 * Real.pi))) - z := by ring
  rw [eassoc]
  exact h

/-- interval containing the real remainder bound `2|c_N| / z^(2N-1)`. -/
def stirlingTailIval (w : Nat) (Z : Ival) (N : Nat) : Ival :=
  Ival.div w (Ival.ofRat w (2 * |stirlingCoeff N|)) (Ival.npow w Z (2 * N - 1))

theorem mem_stirlingTailIval {w : Nat} {Z : Ival} {N : Nat} {z : ℝ}
    (hx : z ∈ Z) :
    2 * |(stirlingCoeff N : ℝ)| / z ^ (2 * N - 1) ∈ stirlingTailIval w Z N := by
  unfold stirlingTailIval
  have hnum : ((2 * |stirlingCoeff N| : ℚ) : ℝ) = 2 * |(stirlingCoeff N : ℝ)| := by
    rw [Rat.cast_mul, Rat.cast_abs, Rat.cast_ofNat]
  have hmem : ((2 * |stirlingCoeff N| : ℚ) : ℝ) ∈ Ival.ofRat w (2 * |stirlingCoeff N|) :=
    Ival.mem_ofRat _ _
  rw [hnum] at hmem
  exact Ival.mem_div hmem (Ival.mem_npow hx _)

/-- `log Γ` on `Z ∋ z ≥ 8`: main + Horner sum widened by the tail. -/
def logGammaIval (c : Ctx) (w : Nat) (Z : Ival) (N : Nat) : Ival :=
  let Zinv := Ival.inv w Z
  let W2 := Ival.mul w Zinv Zinv
  let S := Ival.mul w Zinv (stirlingAcc w W2 (N - 1) (N - 1))
  let M := stirlingMain c w Z
  Ival.widenMag w (Ival.add w M S) (Ival.magHi (stirlingTailIval w Z N))

theorem mem_logGammaIval {c : Ctx} (hc : c.Valid) {w : Nat} {Z : Ival} {N : Nat} {zz : ℝ}
    (hx : zz ∈ Z) (hz : 8 ≤ zz) (hN1 : 1 ≤ N) (hN24 : N ≤ 24) :
    Real.log (Real.Gamma zz) ∈ logGammaIval c w Z N := by
  obtain ⟨R, hR, hRb⟩ := stirling_logGamma zz hz N hN1 hN24
  have hzi : zz⁻¹ ∈ Ival.inv w Z := Ival.mem_inv hx
  have hW2 : zz⁻¹ * zz⁻¹ ∈ Ival.mul w (Ival.inv w Z) (Ival.inv w Z) :=
    Ival.mem_mul hzi hzi
  have hS : (∑ k ∈ Finset.range (N - 1), stirlingTerm zz (k + 1))
      ∈ Ival.mul w (Ival.inv w Z)
        (stirlingAcc w (Ival.mul w (Ival.inv w Z) (Ival.inv w Z)) (N - 1) (N - 1)) := by
    rw [stirling_sum_eq]
    exact Ival.mem_mul hzi (mem_stirlingAcc hW2 le_rfl)
  have hM : (zz - 1 / 2) * Real.log zz - zz + Real.log (Real.sqrt (2 * Real.pi))
      ∈ stirlingMain c w Z := mem_stirlingMain (c := c) (w := w) hc hx
  have hMS : ((zz - 1 / 2) * Real.log zz - zz + Real.log (Real.sqrt (2 * Real.pi)))
      + (∑ k ∈ Finset.range (N - 1), stirlingTerm zz (k + 1))
      ∈ Ival.add w (stirlingMain c w Z)
        (Ival.mul w (Ival.inv w Z)
          (stirlingAcc w (Ival.mul w (Ival.inv w Z) (Ival.inv w Z)) (N - 1) (N - 1))) :=
    Ival.mem_add hM hS
  have hT : 2 * |(stirlingCoeff N : ℝ)| / zz ^ (2 * N - 1)
      ∈ stirlingTailIval w Z N := mem_stirlingTailIval (w := w) (N := N) hx
  unfold logGammaIval
  simp only
  apply Ival.mem_widenMag hMS
  intro m hm
  have hB : 2 * |(stirlingCoeff N : ℝ)| / zz ^ (2 * N - 1) ≤ m.toReal :=
    le_trans (le_abs_self _) (Ival.abs_le_magHi hT hm)
  -- `|R| ≤ bound ≤ m`, and `logΓ - (main + S) = R`
  have hReq : Real.log (Real.Gamma zz)
      - (((zz - 1 / 2) * Real.log zz - zz + Real.log (Real.sqrt (2 * Real.pi)))
        + (∑ k ∈ Finset.range (N - 1), stirlingTerm zz (k + 1))) = R := by
    linarith [hR]
  rw [hReq]
  have hBnn : 0 ≤ 2 * |(stirlingCoeff N : ℝ)| / zz ^ (2 * N - 1) := by positivity
  have := abs_le.1 hRb
  linarith

/-! ### Adaptive parameter choice (pure computation, no proofs needed) -/

/-- is the tail bound at the threshold point already below `2^{-(w+8)}`? -/
def tailSmall (w T N : Nat) : Bool :=
  match Ival.magHi (stirlingTailIval w (Ival.pt (Dy.ofNat T)) N) with
  | some m => Dy.leB m ⟨1, -((w + 8 : Nat) : Int)⟩
  | none => false

/-- smallest `N ∈ [1, 24]` with a small tail bound (`24` if none qualifies).
Any `N` in range is sound; this just controls tightness. -/
def chooseN (w T : Nat) : Nat := go (w + 64) 1
where go : Nat → Nat → Nat
  | 0, N => min N 24
  | fuel + 1, N => if 24 ≤ N then 24 else if tailSmall w T N then N else go fuel (N + 1)

theorem chooseN_go_ge_one {w T : Nat} : ∀ fuel N, 1 ≤ N → 1 ≤ chooseN.go w T fuel N
  | 0, _, h => by simp [chooseN.go, h]
  | fuel + 1, _, h => by
    unfold chooseN.go
    split
    · omega
    · split
      · exact h
      · exact chooseN_go_ge_one fuel _ (by omega)

theorem chooseN_go_le {w T : Nat} : ∀ fuel N, chooseN.go w T fuel N ≤ 24
  | 0, N => by simp [chooseN.go]
  | fuel + 1, N => by
    unfold chooseN.go
    split
    · rfl
    · rename_i h24
      split
      · omega
      · exact chooseN_go_le fuel _

theorem chooseN_ge_one {w T : Nat} : 1 ≤ chooseN w T :=
  chooseN_go_ge_one _ _ le_rfl

theorem chooseN_le {w T : Nat} : chooseN w T ≤ 24 :=
  chooseN_go_le _ _

/-! ### Positive side: shift + Stirling + rising -/

/-- `Γ` for any interval `X` (tight when `X` is positive and narrow):
shift `r` so `Z = X + r ≥ T`, Stirling `log Γ` on `Z`, `exp`, divide by
the rising factorial. -/
def gammaPosIval (c : Ctx) (X : Ival) : Ival :=
  let w := c.prec + 16
  let T := Nat.max 10 (w / 8)
  match X.lo with
  | none => Ival.top
  | some a =>
    let r := gammaShift a T
    let Z := Ival.add w X (Ival.pt (Dy.ofNat r))
    let N := chooseN w T
    Ival.div w (expIval c (logGammaIval c w Z N)) (risingIval w X r)

theorem mem_gammaPosIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival}
    (hx : x ∈ X) : Real.Gamma x ∈ gammaPosIval c X := by
  unfold gammaPosIval
  simp only
  split
  · exact Ival.mem_top _
  · rename_i a ha
    set w := c.prec + 16
    set T := Nat.max 10 (w / 8)
    set r := gammaShift a T
    set N := chooseN w T
    have hax := hx.1 a ha
    have hr : (T : ℝ) ≤ a.toReal + ((r : ℕ) : ℝ) := gammaShift_spec a T
    have hzT : (T : ℝ) ≤ x + ((r : ℕ) : ℝ) := by
      have := add_le_add_right hax (((r : ℕ) : ℝ))
      linarith
    have h10 : (10 : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast Nat.le_max_left 10 (w / 8)
    have h8 : 8 ≤ x + ((r : ℕ) : ℝ) := by linarith
    have hZ : x + ((r : ℕ) : ℝ) ∈ Ival.add w X (Ival.pt (Dy.ofNat r)) :=
      Ival.mem_add hx (Ival.mem_pt_nat r)
    have hL := mem_logGammaIval (w := w) (N := chooseN w T) hc hZ h8
      chooseN_ge_one chooseN_le
    have hpos : 0 < Real.Gamma (x + ((r : ℕ) : ℝ)) :=
      Real.Gamma_pos_of_pos (by linarith)
    have hG : Real.Gamma (x + ((r : ℕ) : ℝ)) ∈ expIval c (logGammaIval c w
        (Ival.add w X (Ival.pt (Dy.ofNat r))) N) := by
      rw [← Real.exp_log hpos]
      exact mem_expIval c hL
    have hRr := mem_risingIval (w := w) hx r
    have e := gamma_eq_gamma_add_div_rising x r
    rw [e]
    exact Ival.mem_div hG hRr

/-! ### Reflection for `hi < 1` -/

/-- `Γ` via `Γ(x) = (π / sin(πx)) / Γ(1-x)`. -/
def gammaReflIval (c : Ctx) (X : Ival) : Ival :=
  let w := c.prec + 16
  let S := sinIval c (Ival.mul w c.pi X)
  let G := gammaPosIval c (Ival.sub w Ival.one X)
  Ival.div w (Ival.div w c.pi S) G

theorem mem_gammaReflIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival}
    (hx : x ∈ X) (hne : Real.Gamma (1 - x) ≠ 0) :
    Real.Gamma x ∈ gammaReflIval c X := by
  have hsin : Real.sin (Real.pi * x)
      ∈ sinIval c (Ival.mul (c.prec + 16) c.pi X) :=
    mem_sinIval hc (Ival.mem_mul hc.pi_mem hx)
  have hG : Real.Gamma (1 - x)
      ∈ gammaPosIval c (Ival.sub (c.prec + 16) Ival.one X) :=
    mem_gammaPosIval hc (Ival.mem_sub Ival.mem_one hx)
  have hrefl := Real.Gamma_mul_Gamma_one_sub x
  have e : Real.Gamma x
      = (Real.pi / Real.sin (Real.pi * x)) / Real.Gamma (1 - x) :=
    (eq_div_iff hne).mpr hrefl
  unfold gammaReflIval
  simp only
  rw [e]
  exact Ival.mem_div (Ival.mem_div hc.pi_mem hsin) hG

/-! ### Top-level dispatch: split at `0` -/

/-- `X.hi < 1`? -/
def hiLtOne (X : Ival) : Bool :=
  match X.hi with | some b => Dy.ltB b Dy.one | none => false

theorem hiLtOne_mem {x : ℝ} {X : Ival} (hx : x ∈ X) (h : hiLtOne X = true) : x < 1 := by
  unfold hiLtOne at h
  split at h
  · rename_i b hb
    have hxb := hx.2 b hb
    have hlt := toReal_lt_of_ltB h
    have h1 : (Dy.one).toReal = 1 := by simp [toReal_def]
    linarith
  · simp at h

/-- `X ∩ (-∞, 0]`. -/
def negPart (X : Ival) : Ival :=
  ⟨X.lo, some (match X.hi with | some b => Dy.min b Dy.zero | none => Dy.zero)⟩

/-- `X ∩ [0, ∞)`. -/
def posPart (X : Ival) : Ival :=
  ⟨some (match X.lo with | some a => Dy.max a Dy.zero | none => Dy.zero), X.hi⟩

theorem mem_negPart {x : ℝ} {X : Ival} (hx : x ∈ X) (hx0 : x ≤ 0) : x ∈ negPart X := by
  obtain ⟨hx1, hx2⟩ := hx
  unfold negPart
  refine ⟨hx1, ?_⟩
  intro h hh
  cases hhi : X.hi with
  | none => simp [hhi] at hh; subst hh; simp [toReal_def]; exact hx0
  | some b =>
    simp only [hhi, Option.some.injEq] at hh
    subst hh
    have hxb := hx2 b hhi
    have hz : (Dy.zero).toReal = 0 := by simp [toReal_def]
    rcases toRat_min_eq_or b Dy.zero with e | e
    · rw [e]; exact hxb
    · rw [e, hz]; exact hx0

theorem mem_posPart {x : ℝ} {X : Ival} (hx : x ∈ X) (h0x : 0 ≤ x) : x ∈ posPart X := by
  obtain ⟨hx1, hx2⟩ := hx
  unfold posPart
  refine ⟨?_, hx2⟩
  intro a ha
  cases hlo : X.lo with
  | none => simp [hlo] at ha; subst ha; simp [toReal_def]; exact h0x
  | some v =>
    simp only [hlo, Option.some.injEq] at ha
    subst ha
    have hxv := hx1 v hlo
    have hz : (Dy.zero).toReal = 0 := by simp [toReal_def]
    rcases toRat_max_eq_or v Dy.zero with e | e
    · rw [e]; exact hxv
    · rw [e, hz]; exact h0x

/-- `Γ` on any interval: positive fast path, reflection below `1`,
hull of the two pieces across `0` otherwise. -/
def gammaIval (c : Ctx) (X : Ival) : Ival :=
  if X.pos then gammaPosIval c X
  else if hiLtOne X then gammaReflIval c X
  else Ival.hull (gammaReflIval c (negPart X)) (gammaPosIval c (posPart X))

theorem mem_gammaIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival}
    (hx : x ∈ X) : Real.Gamma x ∈ gammaIval c X := by
  unfold gammaIval
  split
  · exact mem_gammaPosIval hc hx
  · rename_i hpos
    split
    · rename_i h1
      have hx1 := hiLtOne_mem hx h1
      have hne : Real.Gamma (1 - x) ≠ 0 :=
        ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
      exact mem_gammaReflIval hc hx hne
    · rename_i h1
      rcases le_total x 0 with hx0 | h0x
      · have hne : Real.Gamma (1 - x) ≠ 0 :=
          ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
        exact Ival.mem_hull_left (mem_gammaReflIval hc (mem_negPart hx hx0) hne)
      · exact Ival.mem_hull_right (mem_gammaPosIval hc (mem_posPart hx h0x))

@[lynth_fn] def gammaR : Fn1 .real .real where
  name := "gamma"
  graph x y := y = Real.Gamma x
  exu := exu_eq _
  ev := gammaIval
  sound := fun _ _ _ _ hc hy hx => by obtain rfl := hy; exact mem_gammaIval hc hx
  cost := 500

end Lynth.Interval.Fns
