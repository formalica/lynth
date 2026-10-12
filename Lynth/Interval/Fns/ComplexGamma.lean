import Lynth.Interval.Fns.ComplexElem
import Lynth.Interval.Fns.Gamma

/-!
# Complex Gamma function via Stirling expansion over rectangles.

Mirror of `Lynth/Interval/Fns/Gamma.lean` with `Ival` replaced by `CBox`
and `|·|` by `‖·‖`: argument shifting with `Γ(s+1) = s·Γ(s)` until
`8 ≤ (z+r).re`, Stirling expansion of `log Γ` with explicit remainder,
then `exp` divided by the complex rising factorial.  Arguments with
`Re < 1` go through Euler's reflection formula
(`Complex.Gamma_mul_Gamma_one_sub`); general boxes are split at `Re = 0`
and joined with `CBox.hull`.

The one analytic input — the complex Stirling expansion with remainder —
is stated below as a mirror of `/tmp/complex/gamma_handoff.lean` (same
contract as the batch-2 `arg`/`sqrt` mirrors: keep the statement
byte-identical, paste the prover's proof back).  Everything else is proved
inline from Mathlib facts plus the already-built `CBox`/`logBox`/`expBox`/
`sinBox` membership lemmas.  Poles are handled exactly as in the real
case: Mathlib's `Γ` is `0` at nonpositive integers while `_/0 = 0`, so the
shift-division identity holds everywhere (`gammaCx_eq_gamma_add_div_rising`).
-/

namespace Complex

/-- COMPLEX STIRLING (log-Gamma with explicit remainder).
Mirror of `/tmp/complex/gamma_handoff.lean` for the external prover. -/
theorem stirling_logGamma (w : ℂ) (hw : 8 ≤ w.re) (N : ℕ) (hN : 1 ≤ N) :
    ∃ R : ℂ, Complex.log (Complex.Gamma w)
        = (w - 1 / 2) * Complex.log w - w + Complex.log (Real.sqrt (2 * Real.pi))
          + (∑ k ∈ Finset.range (N - 1),
              ((bernoulli (2 * (k + 1)) : ℚ) : ℂ) / ((2 * ((k + 1) : ℂ)) * (2 * ((k + 1) : ℂ) - 1) * w ^ (2 * (k + 1) - 1))) + R
      ∧ ‖R‖ ≤ 2 * |(((bernoulli (2 * N) : ℚ)) : ℝ) / ((2 * ((N : ℝ))) * (2 * ((N : ℝ)) - 1))| / (‖w‖ ^ (2 * N - 1)) := by
  sorry

end Complex

namespace Lynth.Interval.Fns

open Lynth.Interval Dy

/-! ### Complex rising factorial -/

/-- `x·(x+1)·…·(x+r-1)` over `ℂ`. -/
noncomputable def risingCx (x : ℂ) : Nat → ℂ
  | 0 => 1
  | r + 1 => risingCx x r * (x + (r : ℂ))

def risingC (w : Nat) (X : CBox) : Nat → CBox
  | 0 => ⟨Ival.one, Ival.zero⟩
  | r + 1 => CBox.mul w (risingC w X r)
      (CBox.add w X (CBox.ofReal (Ival.ofRat w (r : ℚ))))

/-- `(r : ℂ)` as a real-embedded rational bound. -/
theorem natCastC_mem_ofRat (w : Nat) (r : Nat) :
    ((r : ℕ) : ℂ) ∈ CBox.ofReal (Ival.ofRat w (r : ℚ)) := by
  have h := CBox.mem_ofReal (Ival.mem_ofRat w (r : ℚ))
  rwa [Rat.cast_natCast, Complex.ofReal_natCast] at h

theorem mem_risingC {w : Nat} {x : ℂ} {X : CBox} (hx : x ∈ X) (r : Nat) :
    risingCx x r ∈ risingC w X r := by
  induction r with
  | zero =>
    simp only [risingCx, risingC]
    exact ⟨by rw [Complex.one_re]; exact Ival.mem_one,
      by rw [Complex.one_im]; exact Ival.mem_zero⟩
  | succ r ih =>
    simp only [risingCx, risingC]
    exact CBox.mem_mul ih (CBox.mem_add hx (natCastC_mem_ofRat w r))

/-- recurrence in division form — valid at poles too, because Mathlib's
`Γ` is `0` at nonpositive integers while `_/0 = 0`
(mirror of `gamma_eq_gamma_add_div_rising`). -/
theorem gammaCx_eq_gamma_add_div_rising (x : ℂ) (r : Nat) :
    Complex.Gamma x = Complex.Gamma (x + (r : ℂ)) / risingCx x r := by
  induction r with
  | zero => simp [risingCx]
  | succ r ih =>
    have hcast : x + (((r + 1 : ℕ) : ℕ) : ℂ) = (x + (r : ℂ)) + 1 := by push_cast; ring
    rw [hcast]
    by_cases h : x + (r : ℂ) = 0
    · have hx : x = -((r : ℕ) : ℂ) := by linear_combination h
      have hzero : risingCx x (r + 1) = 0 := by
        simp only [risingCx]
        rw [h, mul_zero]
      rw [hzero, hx, Complex.Gamma_neg_nat_eq_zero]
      have h1 : (-((r : ℕ) : ℂ) + (r : ℂ)) + 1 = 1 := by ring
      rw [h1, Complex.Gamma_one, div_zero]
    · have hadd := Complex.Gamma_add_one _ h
      have hR : risingCx x (r + 1) = (x + (r : ℂ)) * risingCx x r := by
        simp [risingCx, mul_comm]
      rw [hadd, hR, mul_div_mul_left _ _ h, ih]

/-- `Γ` is nonzero away from the poles. -/
theorem gamma_ne_zero_of_pos_re {s : ℂ} (h : 0 < s.re) :
    Complex.Gamma s ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hm
  have hr := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hr
  have hnn : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-! ### Complex Stirling partial sums (Horner in `z⁻²`) -/

/-- `c_{M-j} + W2 * (c_{M-j+1} + …)`: Horner accumulator, `j` levels,
same coefficients as the real `stirlingAcc`. -/
def stirlingAccC (w : Nat) (W2 : CBox) (B : List ℚ) (M : Nat) : Nat → CBox
  | 0 => ⟨Ival.zero, Ival.zero⟩
  | j + 1 =>
    CBox.add w (CBox.ofReal (Ival.ofRat w (if M - j ≤ 24 then stirlingTable (M - j)
      else stirlingQuot (B.getD (2 * (M - j)) 0) (M - j))))
      (CBox.mul w W2 (stirlingAccC w W2 B M j))

/-- complex value of the accumulator. -/
noncomputable def stirlingAccCReal (t : ℂ) (M j : Nat) : ℂ :=
  ∑ i ∈ Finset.range j, (((stirlingCoeff (M - j + 1 + i) : ℝ)) : ℂ) * t ^ i

theorem mem_stirlingAccC {w : Nat} {W2 : CBox} {M N : Nat} {t : ℂ}
    (ht : t ∈ W2) (hMN : M + 1 ≤ N) {j : Nat} (hj : j ≤ M) :
    stirlingAccCReal t M j ∈ stirlingAccC w W2 (bernoulliList (2 * N)) M j := by
  induction j with
  | zero =>
    simp only [stirlingAccCReal, Finset.range_zero, Finset.sum_empty, stirlingAccC]
    exact ⟨by rw [Complex.zero_re]; exact Ival.mem_zero,
      by rw [Complex.zero_im]; exact Ival.mem_zero⟩
  | succ j ih =>
    have hj' : j ≤ M := by omega
    have hk1 : 1 ≤ M - j := by omega
    have hstab : (bernoulliList (2 * N)).getD (2 * (M - j)) (0 : ℚ)
        = (bernoulliList (2 * (M - j))).getD (2 * (M - j)) (0 : ℚ) :=
      bernoulliList_getD_stable le_rfl (by omega)
    have hXY : (∑ i ∈ Finset.range j, (((stirlingCoeff (M - j + (i + 1)) : ℝ)) : ℂ) * t ^ (i + 1))
        = ∑ i ∈ Finset.range j, t * (((stirlingCoeff (M - j + 1 + i) : ℝ)) : ℂ) * t ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      have eix : M - j + (i + 1) = M - j + 1 + i := by omega
      rw [eix, pow_succ']
      ring
    have h0 : M - (j + 1) + 1 + 0 = M - j := by omega
    have hS : stirlingAccCReal t M (j + 1)
        = (((stirlingCoeff (M - j) : ℝ)) : ℂ) + t * stirlingAccCReal t M j := by
      simp only [stirlingAccCReal, Finset.sum_range_succ', h0, pow_zero, mul_one]
      rw [Finset.mul_sum, hXY]
      ring
    rw [hS]
    simp only [stirlingAccC]
    by_cases h24 : M - j ≤ 24
    · have eS : stirlingCoeff (M - j) = stirlingTable (M - j) := by
        unfold stirlingCoeff; rw [ite_eq_left h24]
      rw [eS, ite_eq_left h24]
      exact CBox.mem_add (CBox.mem_ofReal (Ival.mem_ofRat _ _))
        (CBox.mem_mul ht (ih hj'))
    · have eS : stirlingCoeff (M - j) = stirlingGen (M - j) := by
        unfold stirlingCoeff; rw [ite_eq_right h24]
      rw [eS]
      unfold stirlingGen bernoulliQ
      rw [ite_eq_right h24, hstab]
      exact CBox.mem_add (CBox.mem_ofReal (Ival.mem_ofRat _ _))
        (CBox.mem_mul ht (ih hj'))

/-- every hybrid coefficient is the Bernoulli quotient, as a complex cast. -/
theorem stirlingCoeff_cplx_eq (k : ℕ) (hk : 1 ≤ k) :
    (((stirlingCoeff k : ℝ)) : ℂ)
      = (((bernoulli (2 * k) : ℚ)) : ℂ) / ((2 * ((k : ℂ))) * (2 * ((k : ℂ)) - 1)) := by
  rw [stirlingCoeff_eq k hk]
  unfold stirlingQuot
  norm_cast

/-- Stirling summand `c_k / z^(2k-1)` over `ℂ` (for `k ≥ 1`). -/
noncomputable def cTermC (z : ℂ) (k : ℕ) : ℂ :=
  (((stirlingCoeff k : ℝ)) : ℂ) / z ^ (2 * k - 1)

/-- the hybrid summand is the handoff's Bernoulli-quotient summand. -/
theorem cTermC_eq_bernoulli (z : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    cTermC z k = (((bernoulli (2 * k) : ℚ)) : ℂ)
      / ((2 * ((k : ℂ))) * (2 * ((k : ℂ)) - 1) * z ^ (2 * k - 1)) := by
  rw [cTermC, stirlingCoeff_cplx_eq k hk, div_div]

/-- `z⁻¹ * (c * (z⁻¹ * z⁻¹)^i) = c * (z^(2i+1))⁻¹` over `ℂ`. -/
theorem zinv_sq_powC (z c : ℂ) (i : Nat) :
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

/-- the Horner value times `z⁻¹` is the partial sum. -/
theorem stirling_sum_eqC {z : ℂ} (N : Nat) :
    (∑ k ∈ Finset.range (N - 1), cTermC z (k + 1))
      = z⁻¹ * stirlingAccCReal (z⁻¹ * z⁻¹) (N - 1) (N - 1) := by
  simp only [stirlingAccCReal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  have e : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have eN : N - 1 - (N - 1) + 1 + k = k + 1 := by omega
  simp only [cTermC, e, eN, div_eq_mul_inv]
  exact (zinv_sq_powC z _ k).symm

/-- the handoff's Bernoulli sum is the hybrid-coefficient sum. -/
theorem stirling_sum_bridge (z : ℂ) (N : Nat) :
    (∑ k ∈ Finset.range (N - 1),
        (((bernoulli (2 * (k + 1)) : ℚ)) : ℂ) / ((2 * ((k + 1) : ℂ)) * (2 * ((k + 1) : ℂ) - 1) * z ^ (2 * (k + 1) - 1)))
      = ∑ k ∈ Finset.range (N - 1), cTermC z (k + 1) := by
  apply Finset.sum_congr rfl
  intro k _
  have h := (cTermC_eq_bernoulli z (k + 1) (by omega)).symm
  rwa [Nat.cast_add, Nat.cast_one] at h

/-- the handoff's tail bound is the hybrid-coefficient tail bound. -/
theorem stirling_tail_bridge (N : ℕ) (hN : 1 ≤ N) (z : ℂ) :
    2 * |(((bernoulli (2 * N) : ℚ)) : ℝ) / ((2 * ((N : ℝ))) * (2 * ((N : ℝ)) - 1))| / (‖z‖ ^ (2 * N - 1))
      = 2 * |(stirlingCoeff N : ℝ)| / ‖z‖ ^ (2 * N - 1) := by
  rw [stirlingCoeff_eq N hN]
  unfold stirlingQuot
  norm_cast

/-! ### Stirling main term and tail -/

/-- `(z-½) * log z - z + log √(2π)` over rectangles. -/
def stirlingMainC (c : Ctx) (w : Nat) (Z : CBox) : CBox :=
  let logZ := logBox c Z
  let sqrt2pi := Ival.sqrt w (Ival.mul w (Ival.ofRat w 2) c.pi)
  let logSqrt2pi := CBox.ofReal (logIval c sqrt2pi)
  let half := CBox.ofReal (Ival.ofRat w (1 / 2))
  CBox.sub w (CBox.add w (CBox.mul w (CBox.sub w Z half) logZ) logSqrt2pi) Z

theorem mem_stirlingMainC {c : Ctx} (hc : c.Valid) {z : ℂ} {Z : CBox} (hx : z ∈ Z) :
    (z - 1 / 2) * Complex.log z - z + Complex.log (Real.sqrt (2 * Real.pi))
      ∈ stirlingMainC c w Z := by
  unfold stirlingMainC
  simp only
  have hhalf : ((1 / 2 : ℚ) : ℝ) ∈ Ival.ofRat w (1 / 2) := Ival.mem_ofRat _ _
  have h2m : ((2 : ℚ) : ℝ) ∈ Ival.ofRat w 2 := Ival.mem_ofRat _ _
  have e1 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by simp
  have e2 : ((2 : ℚ) : ℝ) = 2 := by simp
  rw [e1] at hhalf
  rw [e2] at h2m
  have hhalfC : ((1 / 2 : ℂ)) ∈ CBox.ofReal (Ival.ofRat w (1 / 2)) := by
    have h := CBox.mem_ofReal hhalf
    rwa [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  have hsqrt : Real.sqrt (2 * Real.pi)
      ∈ Ival.sqrt w (Ival.mul w (Ival.ofRat w 2) c.pi) :=
    Ival.mem_sqrt (Ival.mem_mul h2m hc.pi_mem)
  have hlog2pi : Complex.log ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
      ∈ CBox.ofReal (logIval c (Ival.sqrt w (Ival.mul w (Ival.ofRat w 2) c.pi))) := by
    rw [← Complex.ofReal_log (Real.sqrt_nonneg _)]
    exact CBox.mem_ofReal (mem_logIval hc hsqrt)
  have h : ((z - 1 / 2) * Complex.log z + Complex.log ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)) - z
      ∈ CBox.sub w (CBox.add w (CBox.mul w (CBox.sub w Z (CBox.ofReal (Ival.ofRat w (1 / 2))))
        (logBox c Z)) (CBox.ofReal (logIval c (Ival.sqrt w (Ival.mul w (Ival.ofRat w 2) c.pi))))) Z :=
    CBox.mem_sub
      (CBox.mem_add
        (CBox.mem_mul
          (CBox.mem_sub hx hhalfC)
          (mem_logBox c hc hx))
        hlog2pi)
      hx
  have ecast : Complex.log (Real.sqrt (2 * Real.pi))
      = Complex.log ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := rfl
  have eassoc : (z - 1 / 2) * Complex.log z - z + Complex.log (Real.sqrt (2 * Real.pi))
      = ((z - 1 / 2) * Complex.log z + Complex.log ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)) - z := by
    rw [ecast]; ring
  rw [eassoc]
  exact h

/-- interval containing the remainder bound `2|c_N| / ‖z‖^(2N-1)`. -/
def stirlingTailC (w : Nat) (Z : CBox) (N : Nat) : Ival :=
  Ival.div w (Ival.ofRat w (2 * |stirlingCoeff N|)) (Ival.npow w (CBox.norm w Z) (2 * N - 1))

theorem mem_stirlingTailC {w : Nat} {Z : CBox} {N : Nat} {z : ℂ}
    (hx : z ∈ Z) :
    2 * |(stirlingCoeff N : ℝ)| / ‖z‖ ^ (2 * N - 1) ∈ stirlingTailC w Z N := by
  unfold stirlingTailC
  have hnum : ((2 * |stirlingCoeff N| : ℚ) : ℝ) = 2 * |(stirlingCoeff N : ℝ)| := by
    rw [Rat.cast_mul, Rat.cast_abs, Rat.cast_ofNat]
  have hmem : ((2 * |stirlingCoeff N| : ℚ) : ℝ) ∈ Ival.ofRat w (2 * |stirlingCoeff N|) :=
    Ival.mem_ofRat _ _
  rw [hnum] at hmem
  exact Ival.mem_div hmem (Ival.mem_npow (CBox.mem_norm hx) _)

/-- widen both components by a norm bound. -/
def widenCBox (w : Nat) (B : CBox) (t : Option Dy) : CBox :=
  match t with
  | some m => ⟨Ival.widen w B.re m, Ival.widen w B.im m⟩
  | none => CBox.top

theorem mem_widenCBox {w : Nat} {z v : ℂ} {B : CBox} {t : Option Dy} (hv : v ∈ B)
    (h : ∀ m, t = some m → ‖z - v‖ ≤ m.toReal) : z ∈ widenCBox w B t := by
  unfold widenCBox
  cases t with
  | some m =>
    simp only
    refine ⟨Ival.mem_widen hv.1 ?_, Ival.mem_widen hv.2 ?_⟩
    · have h1 := Complex.abs_re_le_norm (z - v)
      rw [Complex.sub_re] at h1
      exact le_trans h1 (h m rfl)
    · have h1 := Complex.abs_im_le_norm (z - v)
      rw [Complex.sub_im] at h1
      exact le_trans h1 (h m rfl)
  | none => exact CBox.mem_top _

/-- `log Γ` on `Z ∋ z` with `8 ≤ z.re`: main + Horner sum widened by the tail.
`B` is the shared Bernoulli list (`bernoulliList (2N)`). -/
def logGammaC (c : Ctx) (w : Nat) (Z : CBox) (N : Nat) (B : List ℚ) : CBox :=
  let Zinv := CBox.inv w Z
  let W2 := CBox.mul w Zinv Zinv
  let S := CBox.mul w Zinv (stirlingAccC w W2 B (N - 1) (N - 1))
  let M := stirlingMainC c w Z
  widenCBox w (CBox.add w M S) (Ival.magHi (stirlingTailC w Z N))

theorem mem_logGammaC {c : Ctx} (hc : c.Valid) {w : Nat} {Z : CBox} {N : Nat} {z : ℂ}
    (hx : z ∈ Z) (hz : 8 ≤ z.re) (hN1 : 1 ≤ N) :
    Complex.log (Complex.Gamma z) ∈ logGammaC c w Z N (bernoulliList (2 * N)) := by
  obtain ⟨R, hR, hRb⟩ := Complex.stirling_logGamma z hz N hN1
  have hMN : N - 1 + 1 ≤ N := by omega
  have hzi : z⁻¹ ∈ CBox.inv w Z := CBox.mem_inv hx
  have hW2 : z⁻¹ * z⁻¹ ∈ CBox.mul w (CBox.inv w Z) (CBox.inv w Z) :=
    CBox.mem_mul hzi hzi
  rw [stirling_sum_bridge z N] at hR
  rw [stirling_tail_bridge N hN1 z] at hRb
  have hS : (∑ k ∈ Finset.range (N - 1), cTermC z (k + 1))
      ∈ CBox.mul w (CBox.inv w Z)
        (stirlingAccC w (CBox.mul w (CBox.inv w Z) (CBox.inv w Z))
          (bernoulliList (2 * N)) (N - 1) (N - 1)) := by
    rw [stirling_sum_eqC]
    exact CBox.mem_mul hzi (mem_stirlingAccC hW2 hMN le_rfl)
  have hM : (z - 1 / 2) * Complex.log z - z + Complex.log (Real.sqrt (2 * Real.pi))
      ∈ stirlingMainC c w Z := mem_stirlingMainC (c := c) (w := w) hc hx
  have hMS : ((z - 1 / 2) * Complex.log z - z + Complex.log (Real.sqrt (2 * Real.pi)))
      + (∑ k ∈ Finset.range (N - 1), cTermC z (k + 1))
      ∈ CBox.add w (stirlingMainC c w Z)
        (CBox.mul w (CBox.inv w Z)
          (stirlingAccC w (CBox.mul w (CBox.inv w Z) (CBox.inv w Z))
            (bernoulliList (2 * N)) (N - 1) (N - 1))) :=
    CBox.mem_add hM hS
  have hT : 2 * |(stirlingCoeff N : ℝ)| / ‖z‖ ^ (2 * N - 1)
      ∈ stirlingTailC w Z N := mem_stirlingTailC (w := w) (N := N) hx
  unfold logGammaC
  simp only
  apply mem_widenCBox hMS
  intro m hm
  have hB : 2 * |(stirlingCoeff N : ℝ)| / ‖z‖ ^ (2 * N - 1) ≤ m.toReal :=
    le_trans (le_abs_self _) (Ival.abs_le_magHi hT hm)
  have hReq : Complex.log (Complex.Gamma z)
      - (((z - 1 / 2) * Complex.log z - z + Complex.log (Real.sqrt (2 * Real.pi)))
        + (∑ k ∈ Finset.range (N - 1), cTermC z (k + 1))) = R := by
    linear_combination hR
  rw [hReq]
  exact le_trans hRb hB

/-! ### Shifted evaluation (`8 ≤ Re` after shift) -/

/-- `Γ` on boxes with known `Re` lower bound: shift, Stirling, unshift. -/
def gammaPosC (c : Ctx) (X : CBox) : CBox :=
  let w := c.prec + 16
  let T := Nat.max 10 (w / 8)
  match X.re.lo with
  | none => CBox.top
  | some a =>
    let r := gammaShift a T
    let Z := CBox.add w X (CBox.ofReal (Ival.ofRat w (r : ℚ)))
    let N := chooseN w T
    CBox.div w (expBox c (logGammaC c w Z N (bernoulliList (2 * N)))) (risingC w X r)

theorem mem_gammaPosC {c : Ctx} (hc : c.Valid) {z : ℂ} {X : CBox}
    (hx : z ∈ X) : Complex.Gamma z ∈ gammaPosC c X := by
  unfold gammaPosC
  simp only
  split
  · exact CBox.mem_top _
  · rename_i a ha
    set w := c.prec + 16 with hw_def
    set T := Nat.max 10 (w / 8) with hT_def
    set r := gammaShift a T with hr_def
    set N := chooseN w T with hN_def
    have hax : ((a.toRat : ℚ) : ℝ) ≤ z.re := mem_lo_le hx.1 ha
    have haR : a.toReal ≤ z.re := by rw [Dy.toReal_def]; exact hax
    have hr : (T : ℝ) ≤ a.toReal + ((r : ℕ) : ℝ) := gammaShift_spec a T
    have hre : (z + ((r : ℕ) : ℂ)).re = z.re + ((r : ℕ) : ℝ) := by simp
    have hzT : (T : ℝ) ≤ (z + ((r : ℕ) : ℂ)).re := by
      rw [hre]
      linarith
    have h10 : (10 : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast Nat.le_max_left 10 (w / 8)
    have h8 : 8 ≤ (z + ((r : ℕ) : ℂ)).re := by linarith
    have hZ : z + ((r : ℕ) : ℂ)
        ∈ CBox.add w X (CBox.ofReal (Ival.ofRat w (r : ℚ))) :=
      CBox.mem_add hx (natCastC_mem_ofRat w r)
    have hL := mem_logGammaC (w := w) (N := chooseN w T) hc hZ h8
      chooseN_ge_one
    have hpos : 0 < (z + ((r : ℕ) : ℂ)).re := by linarith
    have hne : Complex.Gamma (z + ((r : ℕ) : ℂ)) ≠ 0 :=
      gamma_ne_zero_of_pos_re hpos
    have hG : Complex.Gamma (z + ((r : ℕ) : ℂ)) ∈ expBox c (logGammaC c w
        (CBox.add w X (CBox.ofReal (Ival.ofRat w (r : ℚ)))) N (bernoulliList (2 * N))) := by
      rw [← Complex.exp_log hne]
      exact mem_expBox c hc hL
    have hRr := mem_risingC (w := w) hx r
    have e := gammaCx_eq_gamma_add_div_rising z r
    rw [e]
    exact CBox.mem_div hG hRr

/-! ### Reflection for `Re < 1` -/

/-- `Γ` via `Γ(s) = (π / sin(πs)) / Γ(1-s)`. -/
def gammaReflC (c : Ctx) (X : CBox) : CBox :=
  let w := c.prec + 16
  let S := sinBox c (CBox.mul w (CBox.ofReal c.pi) X)
  let G := gammaPosC c (CBox.sub w (CBox.ofReal Ival.one) X)
  CBox.div w (CBox.div w (CBox.ofReal c.pi) S) G

theorem mem_gammaReflC {c : Ctx} (hc : c.Valid) {z : ℂ} {X : CBox}
    (hx : z ∈ X) (hne : Complex.Gamma (1 - z) ≠ 0) :
    Complex.Gamma z ∈ gammaReflC c X := by
  have hpi : (Real.pi : ℂ) ∈ CBox.ofReal c.pi := CBox.mem_ofReal hc.pi_mem
  have h1c : (1 : ℂ) ∈ CBox.ofReal Ival.one := by
    rw [← Complex.ofReal_one]
    exact CBox.mem_ofReal Ival.mem_one
  have hmul : Real.pi * z ∈ CBox.mul (c.prec + 16) (CBox.ofReal c.pi) X :=
    CBox.mem_mul hpi hx
  have hsin : Complex.sin (Real.pi * z)
      ∈ sinBox c (CBox.mul (c.prec + 16) (CBox.ofReal c.pi) X) :=
    mem_sinBox c hc hmul
  have hG : Complex.Gamma (1 - z)
      ∈ gammaPosC c (CBox.sub (c.prec + 16) (CBox.ofReal Ival.one) X) :=
    mem_gammaPosC hc (CBox.mem_sub h1c hx)
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  have e : Complex.Gamma z
      = (Real.pi / Complex.sin (Real.pi * z)) / Complex.Gamma (1 - z) :=
    (eq_div_iff hne).mpr hrefl
  unfold gammaReflC
  simp only
  rw [e]
  exact CBox.mem_div (CBox.mem_div hpi hsin) hG

/-! ### Top-level dispatch: split `Re` at `0` -/

/-- hull of two rectangles. -/
def CBox.hull (A B : CBox) : CBox := ⟨Ival.hull A.re B.re, Ival.hull A.im B.im⟩

theorem CBox.mem_hull_left {z : ℂ} {A B : CBox} (hx : z ∈ A) : z ∈ CBox.hull A B :=
  ⟨Ival.mem_hull_left hx.1, Ival.mem_hull_left hx.2⟩

theorem CBox.mem_hull_right {z : ℂ} {A B : CBox} (hx : z ∈ B) : z ∈ CBox.hull A B :=
  ⟨Ival.mem_hull_right hx.1, Ival.mem_hull_right hx.2⟩

/-- `X ∩ (Re ≤ 0)`. -/
def negPartC (X : CBox) : CBox := ⟨negPart X.re, X.im⟩

/-- `X ∩ (Re ≥ 0)`. -/
def posPartC (X : CBox) : CBox := ⟨posPart X.re, X.im⟩

theorem mem_negPartC {z : ℂ} {X : CBox} (hx : z ∈ X) (hx0 : z.re ≤ 0) :
    z ∈ negPartC X :=
  ⟨mem_negPart hx.1 hx0, hx.2⟩

theorem mem_posPartC {z : ℂ} {X : CBox} (hx : z ∈ X) (h0x : 0 ≤ z.re) :
    z ∈ posPartC X :=
  ⟨mem_posPart hx.1 h0x, hx.2⟩

/-- `Γ` on any box: positive fast path, reflection below `Re = 1`,
hull of the two pieces across `Re = 0` otherwise. -/
def gammaCBox (c : Ctx) (X : CBox) : CBox :=
  if X.re.pos then gammaPosC c X
  else if hiLtOne X.re then gammaReflC c X
  else CBox.hull (gammaReflC c (negPartC X)) (gammaPosC c (posPartC X))

theorem mem_gammaCBox {c : Ctx} (hc : c.Valid) {z : ℂ} {X : CBox}
    (hx : z ∈ X) : Complex.Gamma z ∈ gammaCBox c X := by
  unfold gammaCBox
  split
  · exact mem_gammaPosC hc hx
  · rename_i hpos
    split
    · rename_i h1
      have hz1 := hiLtOne_mem hx.1 h1
      have hne : Complex.Gamma (1 - z) ≠ 0 := by
        apply gamma_ne_zero_of_pos_re
        have e : (1 - z).re = 1 - z.re := by simp
        rw [e]
        linarith
      exact mem_gammaReflC hc hx hne
    · rename_i h1
      rcases le_total z.re 0 with hx0 | h0x
      · have hne : Complex.Gamma (1 - z) ≠ 0 := by
          apply gamma_ne_zero_of_pos_re
          have e : (1 - z).re = 1 - z.re := by simp
          rw [e]
          linarith
        exact CBox.mem_hull_left (mem_gammaReflC hc (mem_negPartC hx hx0) hne)
      · exact CBox.mem_hull_right (mem_gammaPosC hc (mem_posPartC hx h0x))

@[lynth_cfn] def gammaC : Fn1 .cplx .cplx where
  name := "Complex.Gamma"
  graph x y := y = Complex.Gamma x
  exu := exu_eq _
  ev := gammaCBox
  sound := fun _ _ _ _ hc hy hx => by obtain rfl := hy; exact mem_gammaCBox hc hx
  cost := 500

end Lynth.Interval.Fns
