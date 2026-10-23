module

public import Init.Data.Cast
public import Init.Data.List.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Defs
public import Lynth.Interval.Integral.Math.Integrand
import all Lynth.Interval.Integral.Math.Integrand
import all Lynth.Interval.Integral.Math.IntegralBounds

/-! Portable tail models and integral assembly contracts. -/

namespace Intgrl

public inductive TailFamily where
  | gaussian (power : ℕ)
  | exponential (power : ℕ)
  | sech (power : ℕ)
  | arctan
  | airyDamped
deriving Repr, Inhabited

public structure TailModel where
  family : TailFamily
  scale : ℚ := 1
deriving Repr, Inhabited

@[expose] public def gaussianTerm : Term := .unary .exp (.unary .neg (.pow .var 2))
@[expose] public def exponentialTerm : Term := .unary .exp (.unary .neg .var)

@[expose] public def classifyTail : Term → Option TailModel
  | .binary .mul (.unary .exp (.unary .neg .var)) (.unary .airyAi (.unary .neg .var))
  | .binary .mul (.unary .airyAi (.unary .neg .var)) (.unary .exp (.unary .neg .var)) =>
      some ⟨.airyDamped,1⟩
  | .unary .exp (.unary .neg (.pow .var 2)) => some ⟨.gaussian 0,1⟩
  | .unary .exp (.unary .neg .var) => some ⟨.exponential 0,1⟩
  | .binary .mul (.unary .exp (.unary .neg (.pow .var 2))) (.pow .var n) =>
      some ⟨.gaussian n,1⟩
  | .binary .mul (.pow .var n) (.unary .exp (.unary .neg (.pow .var 2))) =>
      some ⟨.gaussian n,1⟩
  | .binary .mul (.unary .exp (.unary .neg .var)) (.pow .var n) =>
      some ⟨.exponential n,1⟩
  | .binary .mul (.pow .var n) (.unary .exp (.unary .neg .var)) =>
      some ⟨.exponential n,1⟩
  | .unary .inv (.unary .cosh .var) => some ⟨.sech 1,1⟩
  | .binary .div (.rat q) (.unary .cosh .var) => some ⟨.sech 1,q⟩
  | .pow (.unary .inv (.unary .cosh .var)) n =>
      if n > 0 then some ⟨.sech n,1⟩ else none
  | .binary .div (.rat q) (.binary .add (.rat p) (.pow .var 2)) =>
      if p == 1 then some ⟨.arctan,q⟩ else none
  | _ => none

@[expose] public def gaussianBoundTerm : ℕ → Term
  | 0 => .binary .div gaussianTerm (.binary .mul (.rat 2) .var)
  | 1 => .binary .div gaussianTerm (.rat 2)
  | n + 2 => .binary .div
      (.binary .add (.binary .mul (.pow .var (n+1)) gaussianTerm)
        (.binary .mul (.rat (n+1)) (gaussianBoundTerm n))) (.rat 2)

@[expose] public def TailModel.boundTerm (m : TailModel) : Term :=
  .binary .mul (.rat |m.scale|) (match m.family with
    | .gaussian n => gaussianBoundTerm n
    | .exponential n =>
      .binary .mul exponentialTerm
        ((List.range (n+1)).foldr (fun j acc =>
          .binary .add (.binary .mul (.rat ((n.factorial : ℚ) / j.factorial))
            (.pow .var j)) acc) (.rat 0))
    | .sech n => .binary .mul (.rat ((2 : ℚ)^n / n))
        (.unary .exp (.unary .neg (.binary .mul (.rat n) .var)))
    | .arctan => .unary .inv .var
    | .airyDamped => exponentialTerm)

@[expose] public def TailModel.twoSided : TailModel → Bool
  | ⟨.gaussian _,_⟩ => true
  | _ => false

section TailProofs
open Filter Topology MeasureTheory Set


theorem tail_majorant {f g G : ℝ → ℝ} {R : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi R)))
    (hG : ∀ x ∈ Ici R, HasDerivAt G (-g x) x) (hfg : ∀ x ∈ Ioi R, |f x| ≤ g x)
    (hlim : Tendsto G atTop (𝓝 0)) :
    IntegrableOn f (Ioi R) ∧ |∫ x in Ioi R, f x| ≤ G R := by
  have hcont : ContinuousWithinAt (fun x => -G x) (Ici R) R :=
    (hG R (Set.mem_Ici.2 le_rfl)).continuousAt.neg.continuousWithinAt
  have hder : ∀ x ∈ Ioi R, HasDerivAt (fun x => -G x) (g x) x := fun x hx => by
    have := (hG x (Set.mem_Ici.2 (Set.mem_Ioi.1 hx).le)).neg
    rwa [neg_neg] at this
  have hpos : ∀ x ∈ Ioi R, 0 ≤ g x := fun x hx => (abs_nonneg _).trans (hfg x hx)
  have hlim' : Tendsto (fun x => -G x) atTop (𝓝 0) := by simpa using hlim.neg
  have hgi : IntegrableOn g (Ioi R) := integrableOn_Ioi_deriv_of_nonneg hcont hder hpos hlim'
  have hgv : ∫ x in Ioi R, g x = G R := by
    rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hder hpos hlim']; ring
  have hae : ∀ᵐ x ∂(volume.restrict (Ioi R)), ‖f x‖ ≤ g x := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ fun x hx => by rw [Real.norm_eq_abs]; exact hfg x hx
  refine ⟨Integrable.mono' hgi hf hae, ?_⟩
  rw [← Real.norm_eq_abs, ← hgv]
  exact norm_integral_le_of_norm_le hgi hae

theorem tendsto_pow_mul_exp_neg_sq (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * Real.exp (-x ^ 2)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k) ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop 1] with x hx
    gcongr
    nlinarith

/-- Antiderivative-type majorants for the Gaussian moments. -/
noncomputable def gaussG : ℕ → ℝ → ℝ
  | 0, x => Real.exp (-x ^ 2) / (2 * x)
  | 1, x => Real.exp (-x ^ 2) / 2
  | n + 2, x => (x ^ (n + 1) * Real.exp (-x ^ 2) + (n + 1) * gaussG n x) / 2

theorem gaussianBoundTerm_real (n : ℕ) (x : ℝ) :
    (gaussianBoundTerm n).real x = gaussG n x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [gaussianBoundTerm, gaussG, Term.real, gaussianTerm, Unary.real, Binary.real]
    | 1, _ => simp [gaussianBoundTerm, gaussG, Term.real, gaussianTerm, Unary.real, Binary.real]
    | n + 2, ih =>
      simp only [gaussianBoundTerm, gaussG, Term.real, gaussianTerm, Unary.real, Binary.real,
        ih n (by omega)]
      push_cast; ring

theorem gaussG_tendsto (n : ℕ) : Tendsto (gaussG n) atTop (𝓝 0) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        ((tendsto_pow_mul_exp_neg_sq 0).congr (f₂ := fun x => Real.exp (-x^2)) (fun x => by simp)) ?_ ?_
      · filter_upwards [eventually_ge_atTop 0] with x hx
        simp only [gaussG]; positivity
      · filter_upwards [eventually_ge_atTop 1] with x hx
        simp only [gaussG]
        rw [div_le_iff₀ (by linarith)]
        nlinarith [Real.exp_pos (-x^2)]
    | 1, _ =>
      have := (tendsto_pow_mul_exp_neg_sq 0).div_const 2
      simpa [gaussG] using this
    | n + 2, ih =>
      have := ((tendsto_pow_mul_exp_neg_sq (n+1)).add
        ((ih n (by omega)).const_mul ((n:ℝ) + 1))).div_const 2
      simpa [gaussG] using this

theorem gaussG_deriv (n : ℕ) : ∃ g : ℝ → ℝ, (∀ x, 0 < x → HasDerivAt (gaussG n) (-g x) x) ∧
    ∀ x, 0 < x → x ^ n * Real.exp (-x ^ 2) ≤ g x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      refine ⟨fun x => Real.exp (-x^2) + Real.exp (-x^2) / (2 * x^2), fun x hx => ?_,
        fun x hx => ?_⟩
      · have h1 : HasDerivAt (fun x => Real.exp (-x^2)) (Real.exp (-x^2) * (-(2 * x))) x := by
          have := ((hasDerivAt_pow 2 x).neg).exp
          simpa using this
        have h2 : HasDerivAt (fun x => Real.exp (-x^2) / (2 * x))
            ((Real.exp (-x ^ 2) * -(2 * x) * (2 * x) - Real.exp (-x ^ 2) * (2 * 1)) / (2 * x) ^ 2) x :=
          h1.div ((hasDerivAt_id x).const_mul 2) (by positivity)
        have e : gaussG 0 = fun x => Real.exp (-x^2) / (2 * x) := by
          funext y; simp [gaussG]
        rw [e]
        convert h2 using 1
        field_simp
        ring
      · simp only [pow_zero, one_mul]
        have : 0 ≤ Real.exp (-x^2) / (2 * x^2) := by positivity
        linarith
    | 1, _ =>
      refine ⟨fun x => x * Real.exp (-x^2), fun x hx => ?_, fun x hx => by simp⟩
      have h1 : HasDerivAt (fun x => Real.exp (-x^2)) (Real.exp (-x^2) * (-(2 * x))) x := by
        have := ((hasDerivAt_pow 2 x).neg).exp
        simpa using this
      have e : gaussG 1 = fun x => Real.exp (-x^2) / 2 := by
        funext y; simp [gaussG]
      rw [e]
      convert h1.div_const 2 using 1
      ring
    | n + 2, ih =>
      obtain ⟨g, hg, hgle⟩ := ih n (by omega)
      refine ⟨fun x => x ^ (n+2) * Real.exp (-x^2) +
          ((n:ℝ) + 1) / 2 * (g x - x ^ n * Real.exp (-x^2)), fun x hx => ?_, fun x hx => ?_⟩
      · have h1 : HasDerivAt (fun x => Real.exp (-x^2)) (Real.exp (-x^2) * (-(2 * x))) x := by
          have := ((hasDerivAt_pow 2 x).neg).exp
          simpa using this
        have h3 := (((hasDerivAt_pow (n+1) x).mul h1).add
          ((hg x hx).const_mul ((n:ℝ) + 1))).div_const 2
        have e : gaussG (n+2) = fun x =>
            (x ^ (n + 1) * Real.exp (-x ^ 2) + (n + 1) * gaussG n x) / 2 := by
          funext y; simp [gaussG]
        rw [e]
        convert h3 using 1
        push_cast
        ring
      · have := hgle x hx
        have : 0 ≤ ((n:ℝ) + 1) / 2 * (g x - x ^ n * Real.exp (-x^2)) := by
          apply mul_nonneg (by positivity); linarith
        linarith

theorem gauss_tail (n : ℕ) {f : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi R)))
    (hfx : ∀ x, 0 < x → |f x| = x ^ n * Real.exp (-x ^ 2)) :
    IntegrableOn f (Ioi R) ∧ |∫ x in Ioi R, f x| ≤ gaussG n R := by
  obtain ⟨g, hg, hgle⟩ := gaussG_deriv n
  exact tail_majorant hf (fun x hx => hg x (lt_of_lt_of_le hR hx))
    (fun x hx => (hfx x (hR.trans hx)).le.trans (hgle x (hR.trans hx))) (gaussG_tendsto n)

theorem gauss_tail_left (n : ℕ) {f : ℝ → ℝ} {R : ℝ} (hR : 0 < R) (hf : Measurable f)
    (hfx : ∀ x, 0 < x → |f (-x)| = x ^ n * Real.exp (-x ^ 2)) :
    IntegrableOn f (Iio (-R)) ∧ |∫ x in Iio (-R), f x| ≤ gaussG n R := by
  have h := gauss_tail n (f := fun x => f (-x)) hR
    (hf.comp measurable_neg).aestronglyMeasurable hfx
  refine ⟨?_, ?_⟩
  · have h1 : IntegrableOn (fun x => f (-x)) (Ioi (-(-R))) := by simpa using h.1
    simpa using h1.comp_neg_Iio
  · rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi]
    exact h.2

/-- Closed-form tail of `x^n e^{-x}`. -/
noncomputable def expG : ℕ → ℝ → ℝ
  | 0, x => Real.exp (-x)
  | n + 1, x => x ^ (n + 1) * Real.exp (-x) + (n + 1) * expG n x

theorem expG_deriv (n : ℕ) (x : ℝ) : HasDerivAt (expG n) (-(x ^ n * Real.exp (-x))) x := by
  induction n generalizing x with
  | zero =>
    have e : expG 0 = fun x => Real.exp (-x) := by funext y; simp [expG]
    rw [e]; simpa using (hasDerivAt_neg x).exp
  | succ n ih =>
    have e : expG (n+1) = fun x => x ^ (n + 1) * Real.exp (-x) + (n + 1) * expG n x := by
      funext y; simp [expG]
    rw [e]
    have h1 : HasDerivAt (fun x => Real.exp (-x)) (Real.exp (-x) * (-1)) x := by
      simpa using (hasDerivAt_neg x).exp
    have := ((hasDerivAt_pow (n+1) x).mul h1).add ((ih x).const_mul ((n:ℝ) + 1))
    convert this using 1
    push_cast; ring

theorem expG_tendsto (n : ℕ) : Tendsto (expG n) atTop (𝓝 0) := by
  induction n with
  | zero => simpa [expG] using Real.tendsto_exp_neg_atTop_nhds_zero
  | succ n ih =>
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (n+1)).add (ih.const_mul ((n:ℝ) + 1))
    simpa [expG] using this

theorem expG_eq_sum (n : ℕ) (x : ℝ) :
    expG n x = Real.exp (-x) *
      ∑ j ∈ Finset.range (n + 1), (n.factorial : ℝ) / j.factorial * x ^ j := by
  induction n with
  | zero => simp [expG]
  | succ n ih =>
    rw [expG, ih, Finset.sum_range_succ (n := n + 1)]
    have : ∑ j ∈ Finset.range (n + 1), ((n+1).factorial : ℝ) / j.factorial * x ^ j =
        (n + 1) * ∑ j ∈ Finset.range (n + 1), (n.factorial : ℝ) / j.factorial * x ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.factorial_succ]; push_cast; ring
    rw [this]
    have hf : ((n+1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

theorem foldr_real (c : ℕ → ℚ) (L : List ℕ) (x : ℝ) :
    (L.foldr (fun j acc => Term.binary .add (.binary .mul (.rat (c j)) (.pow .var j)) acc)
      (.rat 0)).real x = (L.map fun j => (c j : ℝ) * x ^ j).sum := by
  induction L with
  | nil => simp [Term.real]
  | cons j L ih => simp [Term.real, Binary.real, ih]

theorem list_sum_range_map (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem exp_tail (n : ℕ) {f : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi R)))
    (hfx : ∀ x, 0 < x → |f x| = x ^ n * Real.exp (-x)) :
    IntegrableOn f (Ioi R) ∧ |∫ x in Ioi R, f x| ≤ expG n R :=
  tail_majorant hf (fun x _ => expG_deriv n x)
    (fun x hx => (hfx x (hR.trans hx)).le) (expG_tendsto n)

theorem sech_tail {n : ℕ} (hn : 0 < n) {c : ℝ} {f : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi R)))
    (hfx : ∀ x, 0 < x → |f x| ≤ c * 2 ^ n * Real.exp (-(n * x))) :
    IntegrableOn f (Ioi R) ∧
      |∫ x in Ioi R, f x| ≤ c * (2 ^ n / n) * Real.exp (-(n * R)) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  refine tail_majorant (G := fun x => c * (2 ^ n / n) * Real.exp (-(n * x))) hf
    (fun x _ => ?_) (fun x hx => hfx x (hR.trans hx)) ?_
  · have h1 : HasDerivAt (fun x => Real.exp (-(n * x))) (Real.exp (-(n * x)) * (-(n:ℝ))) x := by
      have := ((hasDerivAt_id x).const_mul (n:ℝ)).neg.exp
      simpa using this
    convert h1.const_mul (c * (2 ^ n / n)) using 1
    field_simp
  · have : Tendsto (fun x : ℝ => Real.exp (-(n * x))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hn')
    simpa using this.const_mul (c * (2 ^ n / n))

theorem inv_cosh_le (x : ℝ) : (Real.cosh x)⁻¹ ≤ 2 * Real.exp (-x) := by
  have h1 : Real.exp x / 2 ≤ Real.cosh x := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-x)]
  have h2 : 0 < Real.exp x / 2 := by positivity
  calc (Real.cosh x)⁻¹ ≤ (Real.exp x / 2)⁻¹ := inv_anti₀ h2 h1
    _ = 2 * Real.exp (-x) := by rw [Real.exp_neg]; field_simp

theorem arctan_tail {c : ℝ} {f : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi R)))
    (hfx : ∀ x, 0 < x → |f x| ≤ c / x ^ 2) :
    IntegrableOn f (Ioi R) ∧ |∫ x in Ioi R, f x| ≤ c * R⁻¹ := by
  refine tail_majorant (G := fun x => c * x⁻¹) (g := fun x => c / x ^ 2) hf
    (fun x hx => ?_) (fun x hx => hfx x (hR.trans hx)) ?_
  · have hx0 : x ≠ 0 := (hR.trans_le hx).ne'
    convert (hasDerivAt_inv hx0).const_mul c using 1
    ring
  · simpa using tendsto_inv_atTop_zero.const_mul c

theorem expneg_tail {f : ℝ → ℝ} {R : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi R)))
    (hfx : ∀ x, R < x → |f x| ≤ Real.exp (-x)) :
    IntegrableOn f (Ioi R) ∧ |∫ x in Ioi R, f x| ≤ Real.exp (-R) := by
  refine tail_majorant (G := fun x => Real.exp (-x)) (g := fun x => Real.exp (-x)) hf
    (fun x _ => ?_) (fun x hx => hfx x hx) Real.tendsto_exp_neg_atTop_nhds_zero
  simpa using (hasDerivAt_neg x).exp

theorem expBound_eq (n : ℕ) (R : ℝ) :
    Real.exp (-R) * ∑ j ∈ Finset.range (n + 1),
      (((n.factorial : ℚ) / (j.factorial : ℚ) : ℚ) : ℝ) * R ^ j = expG n R := by
  rw [expG_eq_sum]; push_cast; rfl

end TailProofs

theorem tailModel_sound {e : Term} {m : TailModel}
    (h : classifyTail e = some m) {R : ℝ} (hR : 0 < R) :
    MeasureTheory.IntegrableOn e.real (Set.Ioi R) ∧
      |(∫ x in Set.Ioi R, e.real x)| ≤ m.boundTerm.real R := by
  have hmeas := e.measurable.aestronglyMeasurable (μ := MeasureTheory.volume.restrict (Set.Ioi R))
  unfold classifyTail at h
  split at h
  all_goals first
    | (split_ifs at h with hc <;> cases h)
    | cases h
  all_goals simp only [TailModel.boundTerm, Term.real, Unary.real, Binary.real, exponentialTerm,
    abs_one, Rat.cast_one, one_mul, gaussianBoundTerm_real, foldr_real, list_sum_range_map,
    expBound_eq] at hmeas ⊢
  · refine expneg_tail hmeas fun x _ => ?_
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (SpecialFunctions.airy_real_bound _)
  · refine expneg_tail hmeas fun x _ => ?_
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (SpecialFunctions.airy_real_bound _)
  · exact gauss_tail 0 hR hmeas fun x _ => by simp [abs_of_pos (Real.exp_pos _)]
  · exact exp_tail 0 hR hmeas fun x _ => by simp [abs_of_pos (Real.exp_pos _)]
  · exact gauss_tail _ hR hmeas fun x hx => by
      rw [abs_of_nonneg (by positivity)]; ring
  · exact gauss_tail _ hR hmeas fun x hx => by
      rw [abs_of_nonneg (by positivity)]
  · exact exp_tail _ hR hmeas fun x hx => by
      rw [abs_of_nonneg (by positivity)]; ring
  · exact exp_tail _ hR hmeas fun x hx => by
      rw [abs_of_nonneg (by positivity)]
  · have := sech_tail (n := 1) one_pos (c := 1) hR hmeas fun x _ => by
      rw [abs_of_pos (inv_pos.2 (Real.cosh_pos x))]
      simpa using inv_cosh_le x
    refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
    norm_num
  · rename_i q
    have := sech_tail (n := 1) one_pos (c := |(q:ℝ)|) hR hmeas fun x _ => by
      rw [abs_div, abs_of_pos (Real.cosh_pos x), div_eq_mul_inv]
      have := inv_cosh_le x
      have hq := abs_nonneg (q:ℝ)
      simp only [pow_one, Nat.cast_one, one_mul]
      nlinarith
    refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
    push_cast
    ring
  · rename_i n
    have := sech_tail (n := n) hc (c := 1) hR hmeas fun x _ => by
      rw [abs_of_pos (pow_pos (inv_pos.2 (Real.cosh_pos x)) n), one_mul,
        show -((n:ℝ) * x) = n * (-x) by ring, Real.exp_nat_mul, ← mul_pow]
      exact pow_le_pow_left₀ (inv_pos.2 (Real.cosh_pos x)).le (inv_cosh_le x) n
    refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
    push_cast
    ring
  · rename_i q p
    have hp : p = 1 := beq_iff_eq.mp hc
    subst hp
    have := arctan_tail (c := |(q:ℝ)|) hR hmeas fun x hx => by
      push_cast
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 1 + x ^ 2)]
      gcongr
      linarith
    refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
    push_cast; rfl

theorem tailModel_left_sound {e : Term} {m : TailModel}
    (h : classifyTail e = some m) (hs : m.twoSided = true)
    {R : ℝ} (hR : 0 < R) :
    MeasureTheory.IntegrableOn e.real (Set.Iio (-R)) ∧
      |(∫ x in Set.Iio (-R), e.real x)| ≤ m.boundTerm.real R := by
  have hmeas := e.measurable
  unfold classifyTail at h
  split at h
  all_goals first
    | (split_ifs at h with hc <;> cases h)
    | cases h
  all_goals simp only [TailModel.twoSided, reduceCtorEq] at hs
  all_goals simp only [TailModel.boundTerm, Term.real, Unary.real, Binary.real,
    abs_one, Rat.cast_one, one_mul, gaussianBoundTerm_real] at hmeas ⊢
  · exact gauss_tail_left 0 hR hmeas fun x _ => by simp [abs_of_pos (Real.exp_pos _)]
  · exact gauss_tail_left _ hR hmeas fun x hx => by
      rw [abs_mul, abs_pow, abs_neg, abs_of_pos hx, abs_of_pos (Real.exp_pos _), neg_sq]; ring
  · exact gauss_tail_left _ hR hmeas fun x hx => by
      rw [abs_mul, abs_pow, abs_neg, abs_of_pos hx, abs_of_pos (Real.exp_pos _), neg_sq]

theorem halfline_assembly {f : ℝ → ℝ} {a R E : ℝ}
    (haR : a ≤ R) (hm : IntervalIntegrable f MeasureTheory.volume a R)
    (ht : MeasureTheory.IntegrableOn f (Set.Ioi R))
    (he : |(∫ x in Set.Ioi R, f x)| ≤ E) :
    MeasureTheory.IntegrableOn f (Set.Ioi a) ∧
      |(∫ x in Set.Ioi a, f x) - (∫ x in a..R, f x)| ≤ E := by
  have hsplit : Set.Ioi a = Set.Ioc a R ∪ Set.Ioi R := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
    constructor
    · intro h
      by_cases hR : x ≤ R
      · exact Or.inl ⟨h, hR⟩
      · exact Or.inr (not_le.mp hR)
    · intro h
      rcases h with h | h
      · exact h.1
      · linarith
  have hIoc : MeasureTheory.IntegrableOn f (Set.Ioc a R) := hm.1
  have hIoi : MeasureTheory.IntegrableOn f (Set.Ioi a) := by
    rw [hsplit]
    exact hIoc.union ht
  refine ⟨hIoi, ?_⟩
  have hval : (∫ x in Set.Ioi a, f x)
      = (∫ x in Set.Ioc a R, f x) + (∫ x in Set.Ioi R, f x) := by
    rw [hsplit]
    exact MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same
      measurableSet_Ioi hIoc ht
  have hmid : (∫ x in a..R, f x) = ∫ x in Set.Ioc a R, f x :=
    intervalIntegral.integral_of_le haR
  have hstep : (∫ x in Set.Ioc a R, f x) + (∫ x in Set.Ioi R, f x)
      - (∫ x in Set.Ioc a R, f x) = (∫ x in Set.Ioi R, f x) := by ring
  rw [hval, hmid, hstep]
  exact he

theorem wholeline_assembly {f : ℝ → ℝ} {R L U : ℝ} (hR : 0 < R)
    (hm : IntervalIntegrable f MeasureTheory.volume (-R) R)
    (hl : MeasureTheory.IntegrableOn f (Set.Iio (-R)))
    (hu : MeasureTheory.IntegrableOn f (Set.Ioi R))
    (hL : |(∫ x in Set.Iio (-R), f x)| ≤ L)
    (hU : |(∫ x in Set.Ioi R, f x)| ≤ U) :
    MeasureTheory.IntegrableOn f Set.univ ∧
      |(∫ x, f x) - (∫ x in (-R)..R, f x)| ≤ L + U := by
  have hle : (-R:ℝ) ≤ R := neg_le_self hR.le
  have hIcc : MeasureTheory.IntegrableOn f (Set.Icc (-R) R) := by
    rw [← Set.Ioc_union_left hle]
    exact hm.1.union (MeasureTheory.integrableOn_singleton (hx := by simp))
  have huniv : (Set.univ : Set ℝ) = Set.Iio (-R) ∪ Set.Icc (-R) R ∪ Set.Ioi R := by
    symm
    apply Set.eq_univ_of_forall
    intro x
    by_cases h1 : x < -R
    · exact Or.inl (Or.inl h1)
    by_cases h2 : x ≤ R
    · exact Or.inl (Or.inr ⟨not_lt.mp h1, h2⟩)
    · exact Or.inr (not_le.mp h2)
  have hun : MeasureTheory.IntegrableOn f Set.univ := by
    rw [huniv]
    exact (hl.union hIcc).union hu
  refine ⟨hun, ?_⟩
  have hdisj01 : Disjoint (Set.Iio (-R)) (Set.Icc (-R) R) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Iio, Set.mem_Icc] at hx1 hx2
    linarith
  have hdisj2 : Disjoint (Set.Iio (-R) ∪ Set.Icc (-R) R) (Set.Ioi R) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Ioi] at hx1 hx2
    rcases hx1 with h | h
    · linarith
    · rcases h with ⟨h1, h2⟩
      linarith
  have hval : (∫ x, f x) =
      (∫ x in Set.Iio (-R), f x)
        + ((∫ x in Set.Icc (-R) R, f x) + (∫ x in Set.Ioi R, f x)) := by
    rw [← MeasureTheory.setIntegral_univ, huniv,
      MeasureTheory.setIntegral_union hdisj2 measurableSet_Ioi (hl.union hIcc) hu,
      MeasureTheory.setIntegral_union hdisj01 measurableSet_Icc hl hIcc]
    exact add_assoc _ _ _
  have hae : (Set.Icc (-R) R : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioc (-R) R := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · have hsd : Set.Icc (-R) R \ Set.Ioc (-R) R = {(-R:ℝ)} := by
        ext x
        simp only [Set.mem_diff, Set.mem_Icc, Set.mem_Ioc, Set.mem_singleton_iff]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          by_contra hne
          exact h3 ⟨lt_of_le_of_ne h1 (Ne.symm hne), h2⟩
        · rintro rfl
          exact ⟨⟨le_rfl, neg_le_self hR.le⟩, fun h => lt_irrefl _ h.1⟩
      rw [hsd, Real.volume_singleton]
    · have hempty : Set.Ioc (-R) R \ Set.Icc (-R) R = ∅ :=
        (Set.diff_eq_empty).2 (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
      rw [hempty]
      simp
  have hv2 : (∫ x in Set.Icc (-R) R, f x) = ∫ x in (-R)..R, f x := by
    rw [MeasureTheory.setIntegral_congr_set hae]
    exact (intervalIntegral.integral_of_le hle).symm
  have hstep : (∫ x in Set.Iio (-R), f x)
      + ((∫ x in (-R)..R, f x) + (∫ x in Set.Ioi R, f x))
      - (∫ x in (-R)..R, f x)
      = (∫ x in Set.Iio (-R), f x) + (∫ x in Set.Ioi R, f x) := by ring
  rw [hval, hv2, hstep]
  exact le_trans (abs_add_le _ _) (add_le_add hL hU)

end Intgrl
