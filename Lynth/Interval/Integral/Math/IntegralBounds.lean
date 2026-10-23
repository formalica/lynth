module

import Mathlib

/-!
P0/P2: direct bounds, piece assembly, uncertain endpoints and improper tails.
Entirely standalone. Keep measurable/integrable assumptions explicit:
boundedness alone is not a proof of Lebesgue integrability.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter Topology

namespace Intgrl

theorem direct_enclosure {f : ℝ → ℝ} {a b lo hi : ℝ}
    (hab : a ≤ b) (hm : Measurable f)
    (hbound : ∀ t ∈ Set.Icc a b, f t ∈ Set.Icc lo hi) :
    IntervalIntegrable f volume a b ∧
      (∫ t in a..b, f t) ∈ Set.Icc ((b - a) * lo) ((b - a) * hi) := by
  have hI : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    refine Integrable.mono' (g := fun _ => max |lo| |hi|) (integrableOn_const (by simp)) hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    obtain ⟨h1, h2⟩ := hbound t ht
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := neg_abs_le lo; have := le_max_left |lo| |hi|; linarith
    · have := le_abs_self hi; have := le_max_right |lo| |hi|; linarith
  refine ⟨hI, ?_, ?_⟩
  · have := intervalIntegral.integral_mono_on hab intervalIntegrable_const hI
      (fun t ht => (hbound t ht).1)
    simpa [mul_comm] using this
  · have := intervalIntegral.integral_mono_on hab hI intervalIntegrable_const
      (fun t ht => (hbound t ht).2)
    simpa [mul_comm] using this

/-- Endpoint values have zero measure; this version permits piecewise analytic
branches such as floor(x) on an interval with integer endpoints. -/
theorem direct_enclosure_open {f : ℝ → ℝ} {a b lo hi : ℝ}
    (hab : a ≤ b) (hm : Measurable f)
    (hbound : ∀ t ∈ Set.Ioo a b, f t ∈ Set.Icc lo hi) :
    IntervalIntegrable f volume a b ∧
      (∫ t in a..b, f t) ∈ Set.Icc ((b - a) * lo) ((b - a) * hi) := by
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), f t ∈ Set.Icc lo hi := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have h1 : ∀ᵐ t ∂volume, t ≠ b := by simp [ae_iff, measure_singleton]
    have h2 : ∀ᵐ t ∂volume, t ≠ a := by simp [ae_iff, measure_singleton]
    filter_upwards [h1, h2] with t ht ht' htm
    exact hbound t ⟨lt_of_le_of_ne htm.1 (Ne.symm ht'), lt_of_le_of_ne htm.2 ht⟩
  have hint : IntegrableOn f (Set.Icc a b) volume := by
    refine Measure.integrableOn_of_bounded (M := max |lo| |hi|) ?_ hm.aestronglyMeasurable ?_
    · simp [Real.volume_Icc]
    · filter_upwards [hae] with t ht
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [le_max_left |lo| |hi|, neg_abs_le lo, ht.1]
      · linarith [le_max_right |lo| |hi|, le_abs_self hi, ht.2]
  have hii : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hint
  refine ⟨hii, ?_, ?_⟩
  · have := intervalIntegral.integral_mono_ae_restrict hab intervalIntegrable_const hii
      (f := fun _ => lo) (g := f) ?_
    · simpa [mul_comm] using this
    · filter_upwards [hae] with t ht; exact ht.1
  · have := intervalIntegral.integral_mono_ae_restrict hab hii intervalIntegrable_const
      (f := f) (g := fun _ => hi) ?_
    · simpa [mul_comm] using this
    · filter_upwards [hae] with t ht; exact ht.2

theorem partition_error {n : ℕ} {p : ℕ → ℝ} {f : ℝ → ℝ} {q e : ℕ → ℝ}
    (hp : ∀ k < n, p k ≤ p (k + 1))
    (hint : ∀ k < n, IntervalIntegrable f volume (p k) (p (k + 1)))
    (herr : ∀ k < n, |(∫ t in p k..p (k + 1), f t) - q k| ≤ e k) :
    IntervalIntegrable f volume (p 0) (p n) ∧
      |(∫ t in p 0..p n, f t) - ∑ k ∈ Finset.range n, q k|
        ≤ ∑ k ∈ Finset.range n, e k := by
  have _hp := hp
  suffices H : ∀ m ≤ n, IntervalIntegrable f volume (p 0) (p m) ∧
      |(∫ t in p 0..p m, f t) - ∑ k ∈ Finset.range m, q k|
        ≤ ∑ k ∈ Finset.range m, e k from H n le_rfl
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hi := hint m (by omega)
    refine ⟨h1.trans hi, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 hi, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have h3 := herr m (by omega)
    calc _ = |((∫ t in p 0..p m, f t) - ∑ k ∈ Finset.range m, q k) +
          ((∫ t in p m..p (m + 1), f t) - q m)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add h2 h3)

theorem uncertain_endpoints {f : ℝ → ℝ} {a b a₀ b₀ M εa εb : ℝ}
    (ha : |a - a₀| ≤ εa) (hb : |b - b₀| ≤ εb) (hM : 0 ≤ M)
    (hintA : IntervalIntegrable f volume a a₀)
    (hintMid : IntervalIntegrable f volume a₀ b₀)
    (hintB : IntervalIntegrable f volume b₀ b)
    (hboundA : ∀ t ∈ Set.uIcc a a₀, |f t| ≤ M)
    (hboundB : ∀ t ∈ Set.uIcc b b₀, |f t| ≤ M) :
    IntervalIntegrable f volume a b ∧
      |(∫ t in a..b, f t) - (∫ t in a₀..b₀, f t)| ≤ M * (εa + εb) := by
  refine ⟨(hintA.trans hintMid).trans hintB, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (hintA.trans hintMid) hintB,
    ← intervalIntegral.integral_add_adjacent_intervals hintA hintMid]
  have hA : |∫ t in a..a₀, f t| ≤ M * |a₀ - a| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a₀) (C := M) (f := f)
      (fun t ht => by simpa [Real.norm_eq_abs] using hboundA t (Set.uIoc_subset_uIcc ht))
    simpa [Real.norm_eq_abs] using this
  have hB : |∫ t in b₀..b, f t| ≤ M * |b - b₀| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := b₀) (b := b) (C := M) (f := f)
      (fun t ht => by
        simpa [Real.norm_eq_abs] using hboundB t (Set.uIcc_comm b₀ b ▸ Set.uIoc_subset_uIcc ht))
    simpa [Real.norm_eq_abs] using this
  rw [abs_sub_comm a₀ a] at hA
  calc _ = |(∫ t in a..a₀, f t) + ∫ t in b₀..b, f t| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ M * |a - a₀| + M * |b - b₀| := add_le_add hA hB
    _ ≤ M * εa + M * εb := add_le_add (mul_le_mul_of_nonneg_left ha hM) (mul_le_mul_of_nonneg_left hb hM)
    _ = _ := by ring

theorem halfline_truncation {f g : ℝ → ℝ} {a R T : ℝ}
    (haR : a ≤ R) (hm : Measurable f)
    (hfinite : IntervalIntegrable f volume a R)
    (hg : IntegrableOn g (Set.Ioi R) volume)
    (hmajorant : ∀ t ∈ Set.Ioi R, |f t| ≤ g t)
    (hT : (∫ t in Set.Ioi R, g t) ≤ T) :
    IntegrableOn f (Set.Ioi a) volume ∧
      |(∫ t in Set.Ioi a, f t) - (∫ t in a..R, f t)| ≤ T := by
  have hR : IntegrableOn f (Set.Ioi R) volume :=
    Integrable.mono' hg hm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => by
        simpa [Real.norm_eq_abs] using hmajorant t ht))
  have hI : IntegrableOn f (Set.Ioc a R) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le haR).1 hfinite
  have hU := Set.Ioc_union_Ioi_eq_Ioi haR
  refine ⟨hU ▸ hI.union hR, ?_⟩
  rw [← hU, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI hR,
    intervalIntegral.integral_of_le haR, add_sub_cancel_left]
  have := norm_integral_le_of_norm_le (f := f) hg
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => by
        simpa [Real.norm_eq_abs] using hmajorant t ht))
  rw [Real.norm_eq_abs] at this
  linarith

theorem power_endpoint {f : ℝ → ℝ} {b C α : ℝ}
    (hb : 0 < b) (hC : 0 ≤ C) (hα : -1 < α) (hm : Measurable f)
    (hbound : ∀ t ∈ Set.Ioo 0 b, |f t| ≤ C * t ^ α) :
    IntegrableOn f (Set.Ioo 0 b) volume ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ b →
        |(∫ t in Set.Ioo 0 ε, f t)| ≤ C * ε ^ (α + 1) / (α + 1) := by
  have _hC := hC
  have hpow : ∀ c, 0 ≤ c → IntegrableOn (fun t : ℝ => C * t ^ α) (Set.Ioo 0 c) volume := by
    intro c hc
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) hα).const_mul C
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hc] at this
    exact this
  have hdom : ∀ c, c ≤ b → ∀ᵐ t ∂(volume.restrict (Set.Ioo 0 c)), ‖f t‖ ≤ C * t ^ α := by
    intro c hc
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht => ?_)
    simpa [Real.norm_eq_abs] using hbound t ⟨ht.1, ht.2.trans_le hc⟩
  refine ⟨Integrable.mono' (hpow b hb.le) hm.aestronglyMeasurable (hdom b le_rfl), ?_⟩
  intro ε hε hεb
  have h1 := norm_integral_le_of_norm_le (f := f) (hpow ε hε.le) (hdom ε hεb)
  rw [Real.norm_eq_abs] at h1
  have h2 : ∫ t in Set.Ioo 0 ε, C * t ^ α = C * ε ^ (α + 1) / (α + 1) := by
    rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hε.le,
      integral_rpow (Or.inl hα), Real.zero_rpow (by linarith)]
    ring
  linarith

theorem gaussian_tail {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2))) (Set.Ioi R) volume ∧
      (∫ t in Set.Ioi R, Real.exp (-(t ^ 2))) ≤ Real.exp (-(R ^ 2)) / (2 * R) := by
  have hfi : IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2))) (Set.Ioi R) volume := by
    have := (integrable_exp_neg_mul_sq (b := 1) one_pos).integrableOn (s := Set.Ioi R)
    simpa using this
  have hderiv : ∀ x ∈ Set.Ici R, HasDerivAt (fun t => -Real.exp (-(t ^ 2)) / (2 * R))
      (x / R * Real.exp (-(x ^ 2))) x := by
    intro x _
    have := (((hasDerivAt_pow 2 x).neg).exp).neg.div_const (2 * R)
    convert this using 1
    simp only [Pi.neg_apply]
    field_simp
    ring
  have hlim : Tendsto (fun t => -Real.exp (-(t ^ 2)) / (2 * R)) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => Real.exp (-(t ^ 2))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      exact tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero)
    simpa using (this.neg).div_const (2 * R)
  have hnn : ∀ x ∈ Set.Ioi R, 0 ≤ x / R * Real.exp (-(x ^ 2)) := fun x hx =>
    mul_nonneg (div_nonneg (hR.trans hx).le hR.le) (Real.exp_pos _).le
  have hgi := integrableOn_Ioi_deriv_of_nonneg' hderiv hnn hlim
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnn hlim
  refine ⟨hfi, ?_⟩
  calc _ ≤ ∫ t in Set.Ioi R, t / R * Real.exp (-(t ^ 2)) := by
        refine setIntegral_mono_on hfi hgi measurableSet_Ioi fun t ht => ?_
        have : 1 ≤ t / R := by rw [le_div_iff₀ hR]; linarith [ht.out]
        nlinarith [Real.exp_pos (-(t ^ 2))]
    _ = _ := by rw [hval]; ring

/-- Together with gaussian_tail and the elementary k=1 tail, bounds polynomial Gaussians. -/
theorem gaussian_power_tail (k : ℕ) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2)) * t ^ k)
      (Set.Ioi R) volume ∧
      (∫ t in Set.Ioi R, Real.exp (-(t ^ 2)) * t ^ (k + 2)) =
        (R ^ (k + 1) * Real.exp (-(R ^ 2)) +
          ((k : ℝ) + 1) *
            (∫ t in Set.Ioi R, Real.exp (-(t ^ 2)) * t ^ k)) / 2 := by
  have hint : ∀ m : ℕ, IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2)) * t ^ m)
      (Set.Ioi R) volume := by
    intro m
    have := (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos
      (s := (m : ℝ)) (by have := m.cast_nonneg (α := ℝ); linarith)).mono_set
      (Set.Ioi_subset_Ioi hR.le)
    refine IntegrableOn.congr_fun this (fun t ht => ?_) measurableSet_Ioi
    simp only [Real.rpow_natCast, neg_mul, one_mul]
    ring
  refine ⟨hint k, ?_⟩
  -- integration by parts with u = t^(k+1), v = -exp(-t^2)/2
  have hu : ∀ x ∈ Set.Ioi R, HasDerivAt (fun t : ℝ => t ^ (k + 1))
      (((k : ℝ) + 1) * x ^ k) x := by
    intro x _
    simpa using hasDerivAt_pow (k + 1) x
  have hv : ∀ x ∈ Set.Ioi R, HasDerivAt (fun t : ℝ => -Real.exp (-(t ^ 2)) / 2)
      (x * Real.exp (-(x ^ 2))) x := by
    intro x _
    have := (((hasDerivAt_pow 2 x).neg).exp).neg.div_const 2
    convert this using 1
    simp only [Pi.neg_apply]
    push_cast
    ring
  have huv' : IntegrableOn ((fun t : ℝ => t ^ (k + 1)) * fun t => t * Real.exp (-(t ^ 2)))
      (Set.Ioi R) := by
    refine IntegrableOn.congr_fun (hint (k + 2)) (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]; ring
  have hu'v : IntegrableOn ((fun t : ℝ => ((k : ℝ) + 1) * t ^ k) *
      fun t => -Real.exp (-(t ^ 2)) / 2) (Set.Ioi R) := by
    refine IntegrableOn.congr_fun ((hint k).const_mul (-(((k : ℝ) + 1) / 2)))
      (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]; ring
  have hcont : Continuous (fun t : ℝ => t ^ (k + 1) * (-Real.exp (-(t ^ 2)) / 2)) := by
    fun_prop
  have h0 : Tendsto ((fun t : ℝ => t ^ (k + 1)) * fun t => -Real.exp (-(t ^ 2)) / 2)
      (𝓝[>] R) (𝓝 (R ^ (k + 1) * (-Real.exp (-(R ^ 2)) / 2))) :=
    (hcont.tendsto R).mono_left nhdsWithin_le_nhds
  have hinf : Tendsto ((fun t : ℝ => t ^ (k + 1)) * fun t => -Real.exp (-(t ^ 2)) / 2)
      atTop (𝓝 0) := by
    have hlim := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (k + 1))
    have hlim' : Tendsto (fun t : ℝ => t ^ (k + 1) * Real.exp (-(t ^ 2))) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ hlim
      · filter_upwards [eventually_ge_atTop 0] with t ht
        positivity
      · filter_upwards [eventually_ge_atTop 1] with t ht
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Real.exp_le_exp.2 (by nlinarith)
    have := (hlim'.neg).div_const 2
    simp only [neg_zero, zero_div] at this
    refine this.congr fun t => ?_
    simp only [Pi.mul_apply]; ring
  have := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  have e1 : ∫ t in Set.Ioi R, Real.exp (-(t ^ 2)) * t ^ (k + 2) =
      ∫ x in Set.Ioi R, x ^ (k + 1) * (x * Real.exp (-(x ^ 2))) := by
    congr 1; funext t; ring
  have e2 : ∫ x in Set.Ioi R, ((k : ℝ) + 1) * x ^ k * (-Real.exp (-(x ^ 2)) / 2) =
      -(((k : ℝ) + 1) / 2) * ∫ t in Set.Ioi R, Real.exp (-(t ^ 2)) * t ^ k := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  rw [e1, this, e2]
  ring

/-- auxiliary polynomial for `exp_power_tail` -/
def expTailPoly : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, t => t ^ (k + 1) + (k + 1) * expTailPoly k t

lemma expTailPoly_eq (k : ℕ) (t : ℝ) :
    expTailPoly k t = ∑ j ∈ Finset.range (k + 1),
      ((Nat.factorial k : ℝ) / (Nat.factorial j : ℝ)) * t ^ j := by
  induction k with
  | zero => simp [expTailPoly]
  | succ k ih =>
    rw [expTailPoly, ih, Finset.sum_range_succ _ (k + 1), Finset.mul_sum]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.factorial_succ]; push_cast; ring
    · have : (Nat.factorial (k + 1) : ℝ) ≠ 0 := by positivity
      field_simp

lemma expTailPoly_hasDerivAt (k : ℕ) (t : ℝ) :
    HasDerivAt (fun t => -Real.exp (-t) * expTailPoly k t) (Real.exp (-t) * t ^ k) t := by
  induction k generalizing t with
  | zero =>
    simp only [expTailPoly, mul_one, pow_zero]
    convert (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t) |>.neg using 1
    rfl
    ring
  | succ k ih =>
    have h1 : HasDerivAt (fun t => -Real.exp (-t) * t ^ (k + 1))
        (Real.exp (-t) * t ^ (k + 1) - Real.exp (-t) * ((k + 1) * t ^ k)) t := by
      have he : HasDerivAt (fun t => -Real.exp (-t)) (Real.exp (-t)) t := by
        convert (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t) |>.neg using 1
        rfl
        ring
      convert he.mul (hasDerivAt_pow (k + 1) t) using 1
      push_cast; ring
    have h2 := (ih t).const_mul ((k : ℝ) + 1)
    convert h1.add h2 using 1
    · funext s; simp only [expTailPoly, Pi.add_apply]; ring
    · ring

lemma expTailPoly_tendsto (k : ℕ) :
    Tendsto (fun t => -Real.exp (-t) * expTailPoly k t) atTop (𝓝 0) := by
  induction k with
  | zero => simpa [expTailPoly] using Real.tendsto_exp_neg_atTop_nhds_zero.neg
  | succ k ih =>
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (k + 1)).neg
    have h2 := ih.const_mul ((k : ℝ) + 1)
    have := h1.add h2
    simp only [neg_zero, mul_zero, add_zero] at this
    refine this.congr fun t => ?_
    simp only [expTailPoly]; ring

theorem exp_power_tail (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ k) (Set.Ioi R) volume ∧
      (∫ t in Set.Ioi R, Real.exp (-t) * t ^ k) =
        Real.exp (-R) *
          ∑ j ∈ Finset.range (k + 1),
            ((Nat.factorial k : ℝ) / (Nat.factorial j : ℝ)) * R ^ j := by
  have hd : ∀ x ∈ Set.Ici R, HasDerivAt (fun t => -Real.exp (-t) * expTailPoly k t)
      (Real.exp (-x) * x ^ k) x := fun x _ => expTailPoly_hasDerivAt k x
  have hnn : ∀ x ∈ Set.Ioi R, 0 ≤ Real.exp (-x) * x ^ k := fun x hx =>
    mul_nonneg (Real.exp_pos _).le (pow_nonneg (hR.trans hx.out.le) _)
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hnn (expTailPoly_tendsto k), ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hnn (expTailPoly_tendsto k), expTailPoly_eq]
  ring

theorem log_endpoint {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IntegrableOn Real.log (Set.Ioo 0 ε) volume ∧
      |(∫ t in Set.Ioo 0 ε, Real.log t)| = ε * (1 - Real.log ε) := by
  have hI := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := ε))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hε.le] at hI
  refine ⟨hI, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hε.le, integral_log]
  have hl : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  rw [abs_of_neg (by simp; nlinarith)]
  simp
  ring

theorem power_tail {C α R : ℝ} (hC : 0 ≤ C) (hα : 1 < α) (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => C * t ^ (-α)) (Set.Ioi R) volume ∧
      (∫ t in Set.Ioi R, C * t ^ (-α)) = C * R ^ (1 - α) / (α - 1) := by
  have _hC := hC
  refine ⟨(integrableOn_Ioi_rpow_of_lt (by linarith) hR).const_mul C, ?_⟩
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hR,
    show -α + 1 = 1 - α by ring]
  have : 1 - α ≠ 0 := by linarith
  have : α - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem sech_power_tail (k : ℕ) (hk : 0 < k) {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun t : ℝ => (Real.cosh t)⁻¹ ^ k) (Set.Ioi R) volume ∧
      (∫ t in Set.Ioi R, (Real.cosh t)⁻¹ ^ k) ≤
        (2 : ℝ) ^ k / (k : ℝ) * Real.exp (-(k : ℝ) * R) := by
  have _hR := hR
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hbound : ∀ t : ℝ, (Real.cosh t)⁻¹ ^ k ≤ 2 ^ k * Real.exp (-(k : ℝ) * t) := by
    intro t
    have hc : Real.exp t / 2 ≤ Real.cosh t := by
      rw [Real.cosh_eq]; have := Real.exp_pos (-t); linarith
    have hpos : 0 < Real.exp t / 2 := by positivity
    have h1 : (Real.cosh t)⁻¹ ≤ 2 * Real.exp (-t) := by
      rw [Real.exp_neg]
      calc (Real.cosh t)⁻¹ ≤ (Real.exp t / 2)⁻¹ := inv_anti₀ hpos hc
        _ = _ := by field_simp
    calc (Real.cosh t)⁻¹ ^ k ≤ (2 * Real.exp (-t)) ^ k :=
          pow_le_pow_left₀ (inv_nonneg.2 (Real.cosh_pos t).le) h1 k
      _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  have hgi : IntegrableOn (fun t : ℝ => 2 ^ k * Real.exp (-(k : ℝ) * t)) (Set.Ioi R) volume :=
    (integrableOn_exp_mul_Ioi (by linarith) R).const_mul _
  have hfi : IntegrableOn (fun t : ℝ => (Real.cosh t)⁻¹ ^ k) (Set.Ioi R) volume := by
    refine Integrable.mono' hgi ?_ (Eventually.of_forall fun t => ?_)
    · exact ((Real.continuous_cosh.inv₀ fun t => (Real.cosh_pos t).ne').pow k).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.2 (Real.cosh_pos t).le) _)]
      exact hbound t
  refine ⟨hfi, ?_⟩
  calc _ ≤ ∫ t in Set.Ioi R, 2 ^ k * Real.exp (-(k : ℝ) * t) :=
        setIntegral_mono hfi hgi hbound
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
      field_simp

lemma sin_image_Ioo_pi_div_two :
    Real.sin '' Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) = Set.Ioo (-1 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have hmono := Real.strictMonoOn_sin
    have h1 := hmono ⟨le_rfl, by linarith [Real.pi_pos]⟩ ⟨hθ.1.le, hθ.2.le⟩ hθ.1
    have h2 := hmono ⟨hθ.1.le, hθ.2.le⟩ ⟨by linarith [Real.pi_pos], le_rfl⟩ hθ.2
    simp only [Real.sin_neg, Real.sin_pi_div_two] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Real.arcsin x, ⟨Real.neg_pi_div_two_lt_arcsin.2 h1, Real.arcsin_lt_pi_div_two.2 h2⟩,
      Real.sin_arcsin h1.le h2.le⟩

theorem sqrt_weight_substitution {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (-1 : ℝ) 1)) :
    IntegrableOn (fun t => g t / Real.sqrt (1 - t ^ 2))
      (Set.Ioo (-1 : ℝ) 1) volume ∧
      (∫ t in Set.Ioo (-1 : ℝ) 1, g t / Real.sqrt (1 - t ^ 2)) =
        ∫ θ in (-Real.pi / 2)..(Real.pi / 2), g (Real.sin θ) := by
  set s := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
  have hs : MeasurableSet s := measurableSet_Ioo
  have hderiv : ∀ x ∈ s, HasDerivWithinAt Real.sin (Real.cos x) s x :=
    fun x _ => (Real.hasDerivAt_sin x).hasDerivWithinAt
  have hinj : Set.InjOn Real.sin s :=
    Real.injOn_sin.mono Set.Ioo_subset_Icc_self
  have hcos : ∀ x ∈ s, 0 < Real.cos x := fun x hx => Real.cos_pos_of_mem_Ioo hx
  have hsimp : Set.EqOn (fun x => |Real.cos x| • (g (Real.sin x) / Real.sqrt (1 - Real.sin x ^ 2)))
      (fun x => g (Real.sin x)) s := by
    intro x hx
    have hc := hcos x hx
    simp only [smul_eq_mul]
    rw [show 1 - Real.sin x ^ 2 = Real.cos x ^ 2 by rw [← Real.cos_sq_add_sin_sq x]; ring,
      Real.sqrt_sq hc.le, abs_of_pos hc]
    field_simp
  have hgs : IntegrableOn (fun x => g (Real.sin x)) s volume := by
    have hc : ContinuousOn (fun x => g (Real.sin x)) (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
      hg.comp Real.continuous_sin.continuousOn (fun x _ => ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩)
    exact (hc.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  rw [← sin_image_Ioo_pi_div_two]
  refine ⟨?_, ?_⟩
  · rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hs hderiv hinj]
    exact IntegrableOn.congr_fun hgs hsimp.symm hs
  · rw [integral_image_eq_integral_abs_deriv_smul hs hderiv hinj, setIntegral_congr_fun hs hsimp,
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo,
      neg_div]

end Intgrl
