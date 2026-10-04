import Lynth.Interval.Fns.EulerGamma.Proof.Notation

/-!
# Entire power series and the derivatives of `bmB`, `bmA`
-/

open Real Finset Nat

namespace BM

/-- the power series `Σ a_k y^k` -/
noncomputable def PS (a : ℕ → ℝ) (y : ℝ) : ℝ := ∑' k, a k * y ^ k

/-- entire coefficient sequences -/
def Entire (a : ℕ → ℝ) : Prop := ∀ R : ℝ, 0 ≤ R → Summable (fun k => |a k| * R ^ k)

/-- coefficients of the derivative -/
def dco (a : ℕ → ℝ) (k : ℕ) : ℝ := (k + 1) * a (k + 1)

lemma nat_le_two_pow (k : ℕ) : (k : ℝ) ≤ 2 ^ k := by
  have : k < 2 ^ k := Nat.lt_two_pow_self
  exact_mod_cast this.le

lemma Entire.summable {a : ℕ → ℝ} (ha : Entire a) (y : ℝ) : Summable (fun k => a k * y ^ k) := by
  refine Summable.of_norm ?_
  have := ha |y| (abs_nonneg y)
  refine this.congr (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]

lemma Entire.summable_k {a : ℕ → ℝ} (ha : Entire a) (R : ℝ) (hR : 1 ≤ R) :
    Summable (fun k => |a k| * k * R ^ (k - 1)) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (ha (2 * R) (by linarith))
  have h1 : R ^ (k - 1) ≤ R ^ k := pow_le_pow_right₀ hR (Nat.sub_le k 1)
  have h2 : (k : ℝ) * R ^ (k - 1) ≤ (2 * R) ^ k := by
    rw [mul_pow]
    exact mul_le_mul (nat_le_two_pow k) h1 (by positivity) (by positivity)
  calc |a k| * k * R ^ (k - 1) = |a k| * (k * R ^ (k - 1)) := by ring
    _ ≤ |a k| * (2 * R) ^ k := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

lemma Entire.dco {a : ℕ → ℝ} (ha : Entire a) : Entire (dco a) := by
  intro R hR
  set R' := max R 1
  have hR' : 1 ≤ R' := le_max_right _ _
  have h := (ha.summable_k R' hR')
  have h2 := (summable_nat_add_iff 1).mpr h
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h2
  simp only [BM.dco, abs_mul, Nat.add_sub_cancel]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) + 1)]
  push_cast
  have : R ^ k ≤ R' ^ k := pow_le_pow_left₀ hR (le_max_left _ _) k
  calc ((k:ℝ) + 1) * |a (k + 1)| * R ^ k ≤ ((k:ℝ) + 1) * |a (k + 1)| * R' ^ k :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = |a (k + 1)| * ((k:ℝ) + 1) * R' ^ k := by ring

lemma hasDerivAt_PS {a : ℕ → ℝ} (ha : Entire a) (y : ℝ) :
    HasDerivAt (PS a) (PS (dco a) y) y := by
  set R := |y| + 1
  have hR : 1 ≤ R := by have := abs_nonneg y; linarith
  have hy : y ∈ Set.Ioo (-R) R := by
    constructor <;> [have := neg_abs_le y; have := le_abs_self y] <;> linarith
  have key := hasDerivAt_tsum_of_isPreconnected (g := fun k z => a k * z ^ k)
    (g' := fun k z => a k * (k * z ^ (k - 1))) (ha.summable_k R hR) isOpen_Ioo
    isPreconnected_Ioo (fun k z _ => (hasDerivAt_pow k z).const_mul (a k))
    (fun k z hz => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
      have : |z| ≤ R := by rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
      have := pow_le_pow_left₀ (abs_nonneg z) this (k - 1)
      calc |a k| * (k * |z| ^ (k - 1)) ≤ |a k| * (k * R ^ (k - 1)) := by gcongr
        _ = |a k| * k * R ^ (k - 1) := by ring)
    hy (ha.summable y) hy
  unfold PS
  convert key using 1
  have hs : Summable (fun k => a k * (k * y ^ (k - 1))) := by
    refine Summable.of_norm_bounded (ha.summable_k R hR) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    have : |y| ≤ R := by linarith
    have := pow_le_pow_left₀ (abs_nonneg y) this (k - 1)
    calc |a k| * (k * |y| ^ (k - 1)) ≤ |a k| * (k * R ^ (k - 1)) := by gcongr
      _ = |a k| * k * R ^ (k - 1) := by ring
  rw [hs.tsum_eq_zero_add]
  simp only [CharP.cast_eq_zero, zero_mul, mul_zero, zero_add, BM.dco]
  refine tsum_congr (fun k => ?_)
  push_cast
  ring

lemma PS_zero (a : ℕ → ℝ) : PS a 0 = a 0 := by
  unfold PS
  rw [tsum_eq_single 0]
  · simp
  · intro k hk; simp [hk]

/-- shift: `y * PS c y = PS (shift c) y` -/
def shco (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => c k

lemma Entire.shco {c : ℕ → ℝ} (hc : Entire c) : Entire (shco c) := by
  intro R hR
  rw [← summable_nat_add_iff 1]
  have := (hc R hR).mul_left R
  refine this.congr (fun k => ?_)
  simp only [BM.shco, pow_succ]; ring

lemma PS_shco (c : ℕ → ℝ) (hc : Entire c) (y : ℝ) : PS (shco c) y = y * PS c y := by
  unfold PS
  rw [(hc.shco.summable y).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [shco, zero_mul, zero_add]
  refine tsum_congr (fun k => ?_)
  rw [pow_succ]; ring

lemma PS_congr {a b : ℕ → ℝ} (h : ∀ k, a k = b k) (y : ℝ) : PS a y = PS b y := by
  unfold PS; simp_rw [h]

lemma PS_add {a b : ℕ → ℝ} (ha : Entire a) (hb : Entire b) (y : ℝ) :
    PS (fun k => a k + b k) y = PS a y + PS b y := by
  unfold PS
  rw [← (ha.summable y).tsum_add (hb.summable y)]
  simp_rw [add_mul]

lemma Entire.of_le {a b : ℕ → ℝ} (hb : Entire b) (h : ∀ k, |a k| ≤ |b k|) : Entire a := by
  intro R hR
  exact Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => mul_le_mul_of_nonneg_right (h k) (by positivity)) (hb R hR)

/-! ### The concrete series -/

/-- coefficients of `bmB` -/
noncomputable def bco (k : ℕ) : ℝ := 1 / ((k ! : ℝ)) ^ 2

/-- coefficients of `bmA` -/
noncomputable def aco (k : ℕ) : ℝ := (harmonic k : ℝ) / ((k ! : ℝ)) ^ 2

lemma entire_exp_like : Entire (fun k => 2 ^ k / (k ! : ℝ)) := by
  intro R hR
  have := Real.summable_pow_div_factorial (2 * R)
  refine this.congr (fun k => ?_)
  rw [abs_of_nonneg (by positivity), mul_pow]; ring

lemma entire_bco : Entire bco := by
  refine entire_exp_like.of_le (fun k => ?_)
  unfold bco
  have hf : (1 : ℝ) ≤ k ! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  nlinarith

lemma entire_aco : Entire aco := by
  refine entire_exp_like.of_le (fun k => ?_)
  unfold aco
  have hf : (1 : ℝ) ≤ k ! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hH : (harmonic k : ℝ) ≤ k := harmonic_le_self k
  have hH0 : (0 : ℝ) ≤ harmonic k := harmonic_nonneg' k
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 := nat_le_two_pow k
  have : (harmonic k : ℝ) * k ! ≤ 2 ^ k * (k ! : ℝ) ^ 2 := by
    calc (harmonic k : ℝ) * k ! ≤ 2 ^ k * k ! := by gcongr; linarith
      _ ≤ 2 ^ k * (k ! : ℝ) ^ 2 := by gcongr; nlinarith
  linarith

lemma bmB_eq_PS (y : ℝ) : bmB y = PS bco y := by
  unfold bmB PS bmBterm bco; congr 1; ext k; ring

lemma bmA_eq_PS (y : ℝ) : bmA y = PS aco y := by
  unfold bmA PS bmAterm aco; congr 1; ext k; ring

/-! ### The functions in the variable `x` (with `y = x²`) -/

/-- `I(x) = bmB(x²)` -/
noncomputable def II (x : ℝ) : ℝ := PS bco (x ^ 2)
/-- `S(x) = bmA(x²)` -/
noncomputable def SS (x : ℝ) : ℝ := PS aco (x ^ 2)
/-- `x I'(x)` -/
noncomputable def I1 (x : ℝ) : ℝ := 2 * PS (shco (dco bco)) (x ^ 2)
/-- `x S'(x)` -/
noncomputable def S1 (x : ℝ) : ℝ := 2 * PS (shco (dco aco)) (x ^ 2)

lemma hasDerivAt_comp_sq {a : ℕ → ℝ} (ha : Entire a) (x : ℝ) :
    HasDerivAt (fun x => PS a (x ^ 2)) (PS (dco a) (x ^ 2) * (2 * x)) x := by
  have h1 := hasDerivAt_PS ha (x ^ 2)
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  exact HasDerivAt.comp (h₂ := PS a) x h1 h2

lemma hasDerivAt_II (x : ℝ) : HasDerivAt II (2 * x * PS (dco bco) (x ^ 2)) x := by
  have := hasDerivAt_comp_sq entire_bco x
  convert this using 1 <;> first | rfl | ring

lemma hasDerivAt_SS (x : ℝ) : HasDerivAt SS (2 * x * PS (dco aco) (x ^ 2)) x := by
  have := hasDerivAt_comp_sq entire_aco x
  convert this using 1 <;> first | rfl | ring

lemma I1_eq (x : ℝ) : I1 x = x * (2 * x * PS (dco bco) (x ^ 2)) := by
  unfold I1; rw [PS_shco _ entire_bco.dco]; ring

lemma S1_eq (x : ℝ) : S1 x = x * (2 * x * PS (dco aco) (x ^ 2)) := by
  unfold S1; rw [PS_shco _ entire_aco.dco]; ring

lemma dco_shco_dco_bco (k : ℕ) : dco (shco (dco bco)) k = bco k := by
  simp only [dco, shco, bco]
  rw [Nat.factorial_succ]; push_cast
  field_simp

lemma dco_shco_dco_aco (k : ℕ) : dco (shco (dco aco)) k = aco k + dco bco k := by
  simp only [dco, shco, bco, aco]
  rw [Nat.factorial_succ, harmonic_succ]; push_cast
  field_simp

lemma hasDerivAt_I1 (x : ℝ) : HasDerivAt I1 (4 * x * II x) x := by
  have h := (hasDerivAt_comp_sq entire_bco.dco.shco x).const_mul 2
  unfold I1
  convert h using 1
  rw [PS_congr dco_shco_dco_bco, II]; ring

lemma hasDerivAt_S1 (x : ℝ) :
    HasDerivAt S1 (4 * x * SS x + 2 * (2 * x * PS (dco bco) (x ^ 2))) x := by
  have h := (hasDerivAt_comp_sq entire_aco.dco.shco x).const_mul 2
  unfold S1
  convert h using 1
  rw [PS_congr dco_shco_dco_aco, PS_add entire_aco entire_bco.dco, SS]; ring

lemma II_zero : II 0 = 1 := by simp [II, PS_zero, bco]
lemma SS_zero : SS 0 = 0 := by simp [SS, PS_zero, aco]
lemma I1_zero : I1 0 = 0 := by simp [I1_eq]
lemma S1_zero : S1 0 = 0 := by simp [S1_eq]

lemma II_eq (x : ℝ) : II x = bmB (x ^ 2) := by rw [II, bmB_eq_PS]
lemma SS_eq (x : ℝ) : SS x = bmA (x ^ 2) := by rw [SS, bmA_eq_PS]

/-- `x (S' I - S I') = I² - 1` -/
lemma S1_II_sub (x : ℝ) : S1 x * II x - I1 x * SS x = II x ^ 2 - 1 := by
  set f := fun x => S1 x * II x - I1 x * SS x - II x ^ 2
  have hd : ∀ x, HasDerivAt f 0 x := by
    intro x
    have := (((hasDerivAt_S1 x).mul (hasDerivAt_II x)).sub
      ((hasDerivAt_I1 x).mul (hasDerivAt_SS x))).sub ((hasDerivAt_II x).pow 2)
    convert this using 1
    rw [S1_eq, I1_eq]; push_cast; ring
  have hc : f x = f 0 := is_const_of_deriv_eq_zero
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) x 0
  simp only [f, S1_zero, I1_zero, II_zero, SS_zero] at hc
  linarith

end BM
