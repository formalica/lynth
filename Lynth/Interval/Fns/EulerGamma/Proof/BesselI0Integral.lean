import Lynth.Interval.Fns.EulerGamma.Proof.Coefficients
import Lynth.Interval.Fns.EulerGamma.Proof.ChangeOfVariables

/-!
# `bmB (x²) = (1/π) ∫_0^π exp(2x cos θ) dθ = e^{2x} PP(4x) / (2π√x)`
-/

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace BM

lemma integral_cos_pow_even (k : ℕ) : ∫ θ in (0:ℝ)..π, cos θ ^ (2 * k) = π * cc k := by
  induction k with
  | zero => simp [cc_zero]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, integral_cos_pow, ih, cc_succ]
    simp only [Real.sin_pi, Real.sin_zero, mul_zero, sub_zero, zero_div, zero_add]
    push_cast
    field_simp

lemma integral_cos_pow_odd (k : ℕ) : ∫ θ in (0:ℝ)..π, cos θ ^ (2 * k + 1) = 0 := by
  induction k with
  | zero => simp [integral_cos]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, integral_cos_pow, ih]
    simp

lemma exp_hasSum (y : ℝ) : HasSum (fun n => y ^ n / (n.factorial : ℝ)) (exp y) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp y

lemma cc_mul_factorial (k : ℕ) :
    (2 : ℝ) ^ (2 * k) / ((2 * k).factorial : ℝ) * cc k = 1 / ((k.factorial : ℝ)) ^ 2 := by
  unfold cc
  rw [Nat.cast_choose ℝ (by omega : k ≤ 2 * k), show 2 * k - k = k by omega, pow_mul]
  have h1 : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have h2 : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  norm_num

lemma bmB_eq_integral (x : ℝ) : π * bmB (x ^ 2) = ∫ θ in (0:ℝ)..π, exp (2 * x * cos θ) := by
  have hb : ∀ n : ℕ, ∀ θ : ℝ, ‖(2 * x * cos θ) ^ n / (n.factorial : ℝ)‖
      ≤ |2 * x| ^ n / (n.factorial : ℝ) := by
    intro n θ
    rw [Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    have h1 : |2 * x * cos θ| ≤ |2 * x| := by
      rw [abs_mul]
      calc |2 * x| * |cos θ| ≤ |2 * x| * 1 := by gcongr; exact abs_cos_le_one θ
        _ = |2 * x| := mul_one _
    have : |2 * x * cos θ| ^ n ≤ |2 * x| ^ n := pow_le_pow_left₀ (abs_nonneg _) h1 n
    exact div_le_div_of_nonneg_right this (by positivity)
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun θ => (2 * x * cos θ) ^ n / (n.factorial : ℝ))
      (volume.restrict (uIoc 0 π)) := fun n =>
    (by fun_prop : Continuous fun θ => (2 * x * cos θ) ^ n / (n.factorial : ℝ)).aestronglyMeasurable
  have h2 : ∀ n : ℕ, ∀ᵐ θ ∂volume, θ ∈ uIoc 0 π →
      ‖(2 * x * cos θ) ^ n / (n.factorial : ℝ)‖ ≤ |2 * x| ^ n / (n.factorial : ℝ) :=
    fun n => Eventually.of_forall (fun θ _ => hb n θ)
  have h3 : ∀ᵐ θ ∂volume, θ ∈ uIoc 0 π →
      Summable (fun n : ℕ => |2 * x| ^ n / (n.factorial : ℝ)) :=
    Eventually.of_forall (fun θ _ => Real.summable_pow_div_factorial _)
  have h4 : IntervalIntegrable (fun _ => ∑' n : ℕ, |2 * x| ^ n / (n.factorial : ℝ)) volume 0 π :=
    _root_.intervalIntegrable_const
  have h5 : ∀ᵐ θ ∂volume, θ ∈ uIoc 0 π →
      HasSum (fun n : ℕ => (2 * x * cos θ) ^ n / (n.factorial : ℝ)) (exp (2 * x * cos θ)) :=
    Eventually.of_forall (fun θ _ => exp_hasSum _)
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun (n : ℕ) (_ : ℝ) => |2 * x| ^ n / (n.factorial : ℝ)) hmeas h2 h3 h4 h5
  have hterm : ∀ n, ∫ θ in (0:ℝ)..π, (2 * x * cos θ) ^ n / (n.factorial : ℝ)
      = (2 * x) ^ n / (n.factorial : ℝ) * ∫ θ in (0:ℝ)..π, cos θ ^ n := by
    intro n
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext θ; rw [mul_pow]; ring
  simp_rw [hterm] at hs
  have hodd : ∀ n ∉ Set.range (fun k : ℕ => 2 * k),
      (2 * x) ^ n / (n.factorial : ℝ) * ∫ θ in (0:ℝ)..π, cos θ ^ n = 0 := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact absurd ⟨k, by simp only; omega⟩ hn
      · exact ⟨k, hk⟩
    rw [integral_cos_pow_odd, mul_zero]
  rw [← (Function.Injective.hasSum_iff (fun a b h => by simpa using h) hodd)] at hs
  rw [← hs.tsum_eq, bmB, ← tsum_mul_left]
  congr 1; ext k
  simp only [Function.comp, integral_cos_pow_even, bmBterm]
  rw [mul_pow, pow_mul, pow_mul]
  have := cc_mul_factorial k
  rw [pow_mul] at this
  rw [show (2 ^ 2 : ℝ) ^ k * (x ^ 2) ^ k / ((2 * k).factorial : ℝ) * (π * cc k)
    = π * (x ^ 2) ^ k * ((2 ^ 2) ^ k / ((2 * k).factorial : ℝ) * cc k) by ring, this]
  ring

lemma PP_eq_real {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioo 0 (4 * x), exp (-t) * t ^ (-(1 / 2 : ℝ)) * (1 - t / (4 * x)) ^ (-(1 / 2 : ℝ)))
      = 2 * √x * exp (-(2 * x)) * ∫ θ in Ioo 0 π, exp (2 * x * cos θ) := by
  set f : ℝ → ℝ := fun θ => 2 * x * (1 - cos θ)
  have himg : f '' Ioo 0 π = Ioo 0 (4 * x) := by
    ext t
    simp only [mem_image, mem_Ioo, f]
    constructor
    · rintro ⟨θ, ⟨h0, hπ⟩, rfl⟩
      have h1 : cos θ < 1 := by
        rw [← Real.cos_zero]
        exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ.le h0
      have h2 : -1 < cos θ := by
        rw [← Real.cos_pi]
        exact Real.cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl hπ
      constructor <;> nlinarith
    · rintro ⟨h0, h1⟩
      have hy1 : 1 - t / (2 * x) < 1 := by
        have : 0 < t / (2 * x) := by positivity
        linarith
      have hy2 : -1 < 1 - t / (2 * x) := by
        have : t / (2 * x) < 2 := by rw [div_lt_iff₀ (by positivity)]; linarith
        linarith
      refine ⟨arccos (1 - t / (2 * x)), ⟨Real.arccos_pos.mpr hy1, Real.arccos_lt_pi.mpr hy2⟩, ?_⟩
      rw [Real.cos_arccos hy2.le hy1.le]; field_simp; ring
  have hinj : InjOn f (Ioo 0 π) := by
    intro a ha b hb h
    simp only [f] at h
    have : cos a = cos b := by
      have h2 : 2 * x ≠ 0 := by positivity
      have := mul_left_cancel₀ h2 h; linarith
    exact Real.injOn_cos ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩ this
  have hderiv : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivWithinAt f (2 * x * sin θ) (Ioo 0 π) θ := by
    intro θ _
    have := ((Real.hasDerivAt_cos θ).const_sub 1).const_mul (2 * x)
    convert this.hasDerivWithinAt using 1; ring
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun t => exp (-t) * t ^ (-(1 / 2 : ℝ)) * (1 - t / (4 * x)) ^ (-(1 / 2 : ℝ)))
  rw [himg] at key
  rw [key, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
  obtain ⟨h0, hπ⟩ := hθ
  have hS : 0 < sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have h1 : cos θ < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ.le h0
  have h2 : -1 < cos θ := by
    rw [← Real.cos_pi]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl hπ
  have hS2 : sin θ ^ 2 = 1 - cos θ ^ 2 := by have := Real.sin_sq_add_cos_sq θ; linarith
  have hf : 0 < f θ := by
    have : 0 < 1 - cos θ := by linarith
    simp only [f]; positivity
  have hg : 1 - f θ / (4 * x) = (1 + cos θ) / 2 := by simp only [f]; field_simp; ring
  rw [smul_eq_mul, abs_of_pos (by positivity), rpow_neg_half hf, hg,
    rpow_neg_half (by linarith)]
  set A := √(f θ)
  set B := √((1 + cos θ) / 2)
  have hA : 0 < A := Real.sqrt_pos.mpr hf
  have hB : 0 < B := Real.sqrt_pos.mpr (by linarith)
  have hsq : 0 < √x := Real.sqrt_pos.mpr hx
  have hAB : A * B = √x * sin θ := by
    have h1 : (A * B) ^ 2 = (√x * sin θ) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hf.le, Real.sq_sqrt (by linarith), Real.sq_sqrt hx.le,
        hS2]
      simp only [f]; ring
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h1
  have hsx : √x ^ 2 = x := Real.sq_sqrt hx.le
  have hexp : exp (-f θ) = exp (-(2 * x)) * exp (2 * x * cos θ) := by
    rw [← Real.exp_add]; congr 1; simp only [f]; ring
  rw [hexp]
  field_simp
  linear_combination (-√x) * hAB + (-sin θ) * hsx

theorem I_eq_PP (m : ℕ) (hm : 1 ≤ m) :
    bmB ((m : ℝ) ^ 2) = exp (2 * m) * PP (4 * m) / (2 * π * √(m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := bmB_eq_integral (m : ℝ)
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo] at h1
  have h2 := PP_eq_real hm0
  have hPP : PP (4 * m) = ∫ t in Ioo 0 (4 * (m : ℝ)),
      exp (-t) * t ^ (-(1 / 2 : ℝ)) * (1 - t / (4 * m)) ^ (-(1 / 2 : ℝ)) := by
    rw [PP]; push_cast; rfl
  rw [hPP, h2, ← h1]
  have hsq : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hm0
  have he : exp (2 * (m : ℝ)) * exp (-(2 * m)) = 1 := by rw [← Real.exp_add]; simp
  have hπ := Real.pi_pos
  rw [eq_div_iff (by positivity)]
  linear_combination (-(2 * π * √(m:ℝ) * bmB ((m:ℝ) ^ 2))) * he

end BM
