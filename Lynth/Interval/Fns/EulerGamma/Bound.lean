import Lynth.Interval.Fns.EulerGamma.Proof.CrossTerms
import Lynth.Interval.Fns.EulerGamma.Proof.QIntegral
import Lynth.Interval.Fns.EulerGamma.Proof.GammaIdentity
import Lynth.Interval.Fns.EulerGamma.Proof.ChangeOfVariables
import Lynth.Interval.Fns.EulerGamma.Proof.BesselI0Integral
import Lynth.Interval.Fns.EulerGamma.Proof.Remainder.Bound

/-!
# Main theorem: FLINT's Brent–McMillan B3 error bound for Euler's constant

This file assembles the proof of `eulerMascheroni_bmk` from the supporting
development in `Lynth/Interval/Fns/EulerGamma/Proof/`.
-/

open Real MeasureTheory Set Finset

namespace BM

theorem EP_bound (m : ℕ) (hm : 1 ≤ m) :
    |PP (4 * m) - ∑ j ∈ range (4 * m), pp (4 * m) j| ≤ 10 * exp (-(4 * m : ℝ)) := by
  have := EP_bound_n (4 * m) (by omega)
  push_cast at this
  exact this

theorem PP_ge (n : ℕ) (hn : 4 ≤ n) : 1.7 ≤ PP n := PP_ge_n n hn

end BM

/-- HARD (MAIN): FLINT's B3 error bound. For integer `m ≥ 1`, with `x = m²`,
`γ − (A(x)/B(x) − K(m)/B(x)² − log m)` is at most `24·e^{−8m}`.
Suggested route: Brent–McMillan (1980) for the `A/B − ½log` part plus the
asymptotic expansion of the Bessel product for the `K` correction
(see the FLINT header for the exact splitting). -/
theorem eulerMascheroni_bmk (m : ℕ) (hm : 1 ≤ m) :
    |Real.eulerMascheroniConstant
      - bmA ((m : ℝ) ^ 2) / bmB ((m : ℝ) ^ 2)
      + bmK m / (bmB ((m : ℝ) ^ 2)) ^ 2
      + Real.log (m : ℝ)|
      ≤ 24 * Real.exp (-8 * (m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set n : ℕ := 4 * m with hn
  have hn4 : 4 ≤ n := by omega
  have hnR : (n : ℝ) = 4 * m := by simp [hn]
  set P := BM.PP n with hP
  set Q := BM.QQ n with hQ
  set I := bmB ((m : ℝ) ^ 2) with hI
  set Pn := ∑ j ∈ range n, BM.pp n j with hPn
  set Qn := ∑ l ∈ range n, (-1) ^ l * BM.pp n l with hQn
  set Sg := ∑ j ∈ range n, ∑ l ∈ range (n - j), BM.pp n j * ((-1) ^ l * BM.pp n l) with hSg
  set X := ∑ j ∈ range n, ∑ l ∈ Ico (n - j) n, BM.pp n j * ((-1) ^ l * BM.pp n l) with hX
  -- the product of truncations splits into the BM sum and the cross terms
  have hsplit : Pn * Qn = Sg + X := by
    rw [hPn, hQn, Finset.sum_mul, hSg, hX, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mul_sum, ← Finset.sum_range_add_sum_Ico _ (Nat.sub_le n j)]
  have hXb : |X| ≤ 2 * exp (-(n : ℝ)) := by
    have h := BM.cross_bound' n hn4
    refine le_trans ?_ h
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (BM.pp_nonneg _ _), abs_of_nonneg (BM.pp_nonneg _ _)]
  have hEP : |P - Pn| ≤ 10 * exp (-(n : ℝ)) := by
    have h := BM.EP_bound m hm; rw [← hn] at h; simpa [hnR] using h
  have hEQ : |Q - Qn| ≤ BM.pp n n := BM.EQ_bound n (by omega)
  have hpn : BM.pp n n ≤ exp (-(n : ℝ)) := BM.pp_self_le n hn4
  have hQ0 : 0 ≤ Q := BM.QQ_nonneg n
  have hQle : Q ≤ √π := BM.QQ_le n
  have hP17 : 1.7 ≤ P := BM.PP_ge n hn4
  have hPpos : 0 < P := by linarith
  have hpi : √π ≤ 1.8 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_lt_d2]
  -- the key identities
  have hγ := BM.gamma_identity (m : ℝ) hm0
  have hIeq : I = exp (2 * m) * P / (2 * π * √(m : ℝ)) := by
    rw [hI, BM.I_eq_PP m hm]
  have hK0 : BM.K0 m = exp (-(2 * m)) * Q / (2 * √(m : ℝ)) := by
    rw [BM.K0_eq_QQ m hm]
  have hK : bmK m = (1 / (4 * π * m)) * Sg := by rw [BM.bmK_eq m hm]
  have hsq : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hm0
  have hsq2 : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hm0.le
  have hIpos : 0 < I := by rw [hIeq]; positivity
  -- the error is `π (Sg - P Q) e^{-4m} / P²`
  have herr : Real.eulerMascheroniConstant - bmA ((m : ℝ) ^ 2) / I + bmK m / I ^ 2
      + Real.log (m : ℝ) = π * (Sg - P * Q) * exp (-(4 * m)) / P ^ 2 := by
    have e1 : Real.eulerMascheroniConstant - bmA ((m : ℝ) ^ 2) / I + bmK m / I ^ 2
        + Real.log (m : ℝ) = bmK m / I ^ 2 - BM.K0 m / I := by rw [hγ, ← hI]; ring
    rw [e1, hK, hK0, hIeq]
    set E := exp (2 * (m : ℝ)) with hE
    have hEpos : 0 < E := Real.exp_pos _
    have h1 : exp (-(2 * (m : ℝ))) = E⁻¹ := by rw [Real.exp_neg]
    have h2 : exp (-(4 * (m : ℝ))) = (E ^ 2)⁻¹ := by
      rw [Real.exp_neg, hE, ← Real.exp_nat_mul]; ring_nf
    rw [h1, h2]
    have hπ : (0:ℝ) < π := Real.pi_pos
    field_simp
    rw [hsq2]
    ring
  rw [herr]
  have hpi' : √π ≤ 1.7725 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_lt_d4]
  have hen : exp (-(n : ℝ)) ≤ 0.0184 := by
    have h4 : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    have : exp (-(n : ℝ)) ≤ exp (-4) := Real.exp_le_exp.mpr (by linarith)
    refine le_trans this ?_
    rw [Real.exp_neg, show (4:ℝ) = ((4:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
    have he := Real.exp_one_gt_d9
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    calc (0.0184 : ℝ)⁻¹ ≤ 2.7182818283 ^ 4 := by norm_num
      _ ≤ exp 1 ^ 4 := by gcongr
  have hen0 : 0 < exp (-(n : ℝ)) := Real.exp_pos _
  have hPn0 : 0 ≤ Pn := Finset.sum_nonneg (fun j _ => BM.pp_nonneg _ _)
  have hPnle : Pn ≤ P + 10 * exp (-(n : ℝ)) := by
    have := (abs_le.mp hEP).1; linarith
  -- bound on `Sg - P Q`
  have hdiff : Sg - P * Q = -((P - Pn) * Q) - Pn * (Q - Qn) - X := by
    have : Sg = Pn * Qn - X := by linarith
    rw [this]; ring
  have hb : |Sg - P * Q| ≤ exp (-(n : ℝ)) * (19.91 + P) := by
    rw [hdiff]
    have t1 : |(P - Pn) * Q| ≤ 10 * exp (-(n : ℝ)) * 1.7725 := by
      rw [abs_mul, abs_of_nonneg hQ0]
      exact mul_le_mul hEP (le_trans hQle hpi') hQ0 (by positivity)
    have t2 : |Pn * (Q - Qn)| ≤ (P + 10 * exp (-(n : ℝ))) * exp (-(n : ℝ)) := by
      rw [abs_mul, abs_of_nonneg hPn0]
      exact mul_le_mul hPnle (le_trans hEQ hpn) (abs_nonneg _) (by positivity)
    calc |-((P - Pn) * Q) - Pn * (Q - Qn) - X|
        ≤ |(P - Pn) * Q| + |Pn * (Q - Qn)| + |X| := by
          have := abs_sub (-((P - Pn) * Q) - Pn * (Q - Qn)) X
          have := abs_sub (-((P - Pn) * Q)) (Pn * (Q - Qn))
          rw [abs_neg] at this
          linarith
      _ ≤ 10 * exp (-(n : ℝ)) * 1.7725 + (P + 10 * exp (-(n : ℝ))) * exp (-(n : ℝ))
          + 2 * exp (-(n : ℝ)) := by linarith
      _ ≤ exp (-(n : ℝ)) * (19.91 + P) := by
          have : 10 * exp (-(n : ℝ)) * exp (-(n : ℝ)) ≤ 0.185 * exp (-(n : ℝ)) := by
            have := mul_le_mul_of_nonneg_left hen hen0.le
            linarith
          linarith
  have hπ3 : π < 3.1416 := Real.pi_lt_d4
  have hπ0 : 0 < π := Real.pi_pos
  have h8 : exp (-(n : ℝ)) * exp (-(4 * (m : ℝ))) = exp (-8 * (m : ℝ)) := by
    rw [← Real.exp_add, hnR]; ring_nf
  rw [abs_div, abs_mul, abs_mul, abs_of_pos hπ0, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by positivity : (0:ℝ) < P ^ 2), div_le_iff₀ (by positivity)]
  calc π * |Sg - P * Q| * exp (-(4 * (m : ℝ)))
      ≤ π * (exp (-(n : ℝ)) * (19.91 + P)) * exp (-(4 * (m : ℝ))) := by gcongr
    _ = π * (19.91 + P) * exp (-8 * (m : ℝ)) := by rw [← h8]; ring
    _ ≤ 24 * exp (-8 * (m : ℝ)) * P ^ 2 := by
        have he8 : 0 < exp (-8 * (m : ℝ)) := Real.exp_pos _
        have h1 : π * (19.91 + P) ≤ 3.1416 * (19.91 + P) := by
          apply mul_le_mul_of_nonneg_right hπ3.le; linarith
        have h2 : 3.1416 * (19.91 + P) ≤ 24 * P ^ 2 := by
          have : 1.7 * P ≤ P ^ 2 := by
            rw [sq]; exact mul_le_mul_of_nonneg_right hP17 hPpos.le
          linarith
        have := mul_le_mul_of_nonneg_left (h1.trans h2) he8.le
        linarith