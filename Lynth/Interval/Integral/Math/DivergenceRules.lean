import Lynth.Interval.Integral.Math.Integrand
import Lynth.Interval.Integral.Math.Divergence

/-! Portable semantic rules for recognized non-integrable families. -/

namespace Intgrl

inductive DivergenceRule where
  | invPower (n : ℕ)
  | shiftedInv (q : ℚ)
  | tangent
  | constant (q : ℚ)
  | linear | sine | exponential
deriving Repr, Inhabited

def classifyDivergence : Term → Option DivergenceRule
  | .unary .inv .var => some (.invPower 1)
  | .unary .inv (.pow .var n) => if 0 < n then some (.invPower n) else none
  | .binary .div (.rat q) .var =>
      if q == 1 then some (.invPower 1) else none
  | .binary .div (.rat q) (.pow .var n) =>
      if q == 1 && n > 0 then some (.invPower n) else none
  | .binary .div (.rat q) (.binary .sub (.rat p) .var) =>
      if q == 1 then some (.shiftedInv p) else none
  | .unary .inv (.binary .sub (.rat p) .var) => some (.shiftedInv p)
  | .binary .div (.unary .sin .var) (.unary .cos .var) => some .tangent
  | .rat q => if q != 0 then some (.constant q) else none
  | .var => some .linear
  | .unary .sin .var => some .sine
  | .unary .exp .var => some .exponential
  | _ => none

def Region.isFinite : Region → Bool
  | .interval | .icc | .ioc | .ico | .ioo => true
  | _ => false

def DivergenceRule.Condition (r : DivergenceRule) (k : Region) (a b : ℝ) : Prop :=
  match r with
  | .invPower n =>
    if k.isFinite then a < b ∧ a ≤ 0 ∧ 0 ≤ b ∧ 0 < n
    else if k == .univ then 0 < n
    else n = 1 ∨ (a ≤ 0 ∧ 0 < n)
  | .shiftedInv q =>
    if k.isFinite then a < b ∧ a ≤ q ∧ (q : ℝ) ≤ b
    else True
  | .tangent =>
    if k.isFinite then a < b ∧ a ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ b
    else True
  | _ => ¬ k.isFinite

set_option maxHeartbeats 1000000 in
open scoped Topology in
theorem divergenceRule_sound {e : Term} {r : DivergenceRule}
    (hclass : classifyDivergence e = some r)
    {k : Region} {a b : ℝ} (h : r.Condition k a b) :
    ¬ k.Converges e.real a b := open MeasureTheory Set Filter Asymptotics in by
    have nonfinite_converges : ∀ {g : ℝ → ℝ} {a b : ℝ} {k : Region} (hk : ¬ k.isFinite) (hconv : k.Converges g a b), MeasureTheory.IntegrableOn g (k.set a b) MeasureTheory.volume := by
      intro g
      intro a b
      intro k
      intro hk
      intro hconv
      cases k with
      | interval => simp [Region.isFinite] at hk
      | icc => simp [Region.isFinite] at hk
      | ioc => simp [Region.isFinite] at hk
      | ico => simp [Region.isFinite] at hk
      | ioo => simp [Region.isFinite] at hk
      | ioi => exact hconv
      | ici => exact hconv
      | univ => exact hconv
    have pole_aux : ∀ {g : ℝ → ℝ} {l : Filter ℝ} {k : Set ℝ} {c : ℝ} [NeBot l] [TendstoIxxClass Set.Icc l l] (hk : k ∈ l) (hle : l ≤ 𝓝[≠] c) (hO : (fun x => (x - c)⁻¹) =O[l] g), ¬ MeasureTheory.IntegrableOn g k := by
      intro g
      intro l
      intro k
      intro c
      intro
      intro
      intro hk
      intro hle
      intro hO
      have hA : ∀ᶠ x in l,
          HasDerivAt (fun y : ℝ => Real.log (y - c)) (x - c)⁻¹ x := by
        filter_upwards [hle self_mem_nhdsWithin] with x hx
        simpa using ((hasDerivAt_id x).sub_const c).log (sub_ne_zero.2 hx)
      have hT : Tendsto (fun x => x - c) l (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · simpa using (tendsto_id.sub_const c).mono_left (le_trans hle inf_le_left)
        · filter_upwards [hle self_mem_nhdsWithin] with x hx using sub_ne_zero.2 hx
      have hN : Tendsto (fun x => ‖Real.log (x - c)‖) l atTop := by
        simpa [Function.comp_def] using
          tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsNE_zero.comp hT)
      refine not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter
        l hk (hA.mono fun x hx => hx.differentiableAt) hN ?_
      exact hO.congr' (hA.mono fun x hx => hx.deriv.symm) EventuallyEq.rfl
    have not_integrableOn_Ioo_right : ∀ {g : ℝ → ℝ} {c d : ℝ} (hc : c < d) (hO : (fun x => (x - c)⁻¹) =O[𝓝[>] c] g), ¬ MeasureTheory.IntegrableOn g (Set.Ioo c d) := by
      intro g
      intro c d
      intro hc
      intro hO
      exact pole_aux (k := Set.Ioo c d) (Ioo_mem_nhdsGT hc) (nhdsWithin_mono _ fun _ h => ne_of_gt h) hO
    have not_integrableOn_Ioo_left : ∀ {g : ℝ → ℝ} {c d : ℝ} (hc : d < c) (hO : (fun x => (x - c)⁻¹) =O[𝓝[<] c] g), ¬ MeasureTheory.IntegrableOn g (Set.Ioo d c) := by
      intro g
      intro c d
      intro hc
      intro hO
      exact pole_aux (k := Set.Ioo d c) (Ioo_mem_nhdsLT hc) (nhdsWithin_mono _ fun _ h => ne_of_lt h) hO
    have not_integrableOn_Ioi_of_pole_tail : ∀ {g : ℝ → ℝ} {p a : ℝ} (hO : (fun x => (x - p)⁻¹) =O[atTop] g), ¬ MeasureTheory.IntegrableOn g (Set.Ioi a) := by
      intro g
      intro p a
      intro hO
      have hA : ∀ᶠ x in (atTop : Filter ℝ),
          HasDerivAt (fun y : ℝ => Real.log (y - p)) (x - p)⁻¹ x := by
        filter_upwards [Ioi_mem_atTop p] with x hx
        simpa using ((hasDerivAt_id x).sub_const p).log (sub_ne_zero.2 (ne_of_gt hx))
      have hN : Tendsto (fun x => ‖Real.log (x - p)‖) (atTop : Filter ℝ) atTop := by
        simpa [Function.comp_def, sub_eq_add_neg] using
          tendsto_norm_atTop_atTop.comp
            (Real.tendsto_log_atTop.comp (map_sub_atTop_eq p).le)
      refine not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter
        atTop (Ioi_mem_atTop a) (hA.mono fun x hx => hx.differentiableAt) hN ?_
      · exact hO.congr' (hA.mono fun x hx => hx.deriv.symm) EventuallyEq.rfl
    have shift_bound : ∀ {p : ℝ}, ∀ x : ℝ, ‖(x - p)⁻¹‖ ≤ ‖(p - x)⁻¹‖ := by
      intro p
      exact fun x => by simp [Real.norm_eq_abs, abs_sub_comm]
    have shift_isBigO : ∀ {p : ℝ} (l : Filter ℝ), (fun x => (x - p)⁻¹) =O[l] fun x => (p - x)⁻¹ := by
      intro p
      intro l
      exact isBigO_of_le l shift_bound
    have inv_one_bound : ∀ x : ℝ, ‖(x - 0)⁻¹‖ ≤ ‖x⁻¹‖ := by
      exact fun x => by simp [sub_zero]
    have inv_one_isBigO : ∀ (l : Filter ℝ), (fun x => (x - 0)⁻¹) =O[l] fun x => x⁻¹ := by
      intro l
      exact isBigO_of_le l inv_one_bound
    have pow_sub_one_le : ∀ {n : ℕ} (hn : 0 < n) {y : ℝ} (hy1 : 0 < y) (hy2 : y ≤ 1), y ^ n ≤ y := by
      intro n
      intro hn
      intro y
      intro hy1
      intro hy2
      have h1le : 1 ≤ n := by omega
      have heq1 : (n - 1) + 1 = n := by omega
      have heq : y ^ (n - 1) * y = y ^ n := by rw [← pow_succ, heq1]
      rw [← heq]
      simpa [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hy1.le hy2) hy1.le
    have inv_pow_bound_right : ∀ {n : ℕ} (hn : 0 < n) {x : ℝ} (h1 : 0 < x) (h2 : x ≤ 1), ‖(x - 0)⁻¹‖ ≤ ‖(x ^ n)⁻¹‖ := by
      intro n
      intro hn
      intro x
      intro h1
      intro h2
      have hxn : 0 < x ^ n := pow_pos h1 n
      simp only [Real.norm_eq_abs, sub_zero, abs_inv, abs_of_pos h1, abs_of_pos hxn]
      exact (inv_le_inv₀ h1 hxn).2 (pow_sub_one_le hn h1 h2)
    have inv_pow_bound_left : ∀ {n : ℕ} (hn : 0 < n) {x : ℝ} (h1 : 0 < |x|) (h2 : |x| ≤ 1), ‖(x - 0)⁻¹‖ ≤ ‖(x ^ n)⁻¹‖ := by
      intro n
      intro hn
      intro x
      intro h1
      intro h2
      simp only [Real.norm_eq_abs, sub_zero, abs_inv]
      rw [abs_pow]
      exact (inv_le_inv₀ h1 (pow_pos h1 n)).2 (pow_sub_one_le hn h1 h2)
    have inv_pow_isBigO_right : ∀ {n : ℕ} (hn : 0 < n), (fun x : ℝ => (x - 0)⁻¹) =O[𝓝[>] (0:ℝ)] fun x => (x ^ n)⁻¹ := by
      intro n
      intro hn
      refine IsBigO.of_bound' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with x hx
      exact inv_pow_bound_right hn (mem_Ioo.1 hx).1 (by linarith [(mem_Ioo.1 hx).2])
    have inv_pow_isBigO_left : ∀ {n : ℕ} (hn : 0 < n), (fun x : ℝ => (x - 0)⁻¹) =O[𝓝[<] (0:ℝ)] fun x => (x ^ n)⁻¹ := by
      intro n
      intro hn
      refine IsBigO.of_bound' ?_
      filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 0 by norm_num)] with x hx
      obtain ⟨h1, h2⟩ := mem_Ioo.1 hx
      have ha : |x| = -x := abs_of_neg (by linarith)
      refine inv_pow_bound_left hn ?_ ?_
      · rw [ha]; linarith
      · rw [ha]; linarith
    have tan_add_nat_pi : ∀ (N : ℕ) (y : ℝ), Real.tan (y + N * Real.pi) = Real.tan y := by
      intro N
      intro y
      induction N with
      | zero => simp
      | succ N ih =>
        have h : y + ((N + 1 : ℕ) : ℝ) * Real.pi = (y + N * Real.pi) + Real.pi := by
          push_cast
          ring
        rw [h, Real.tan_add_pi, ih]
    have cot_bound : ∀ {t : ℝ} (ht0 : 0 < t) (ht4 : t < Real.pi / 4), t⁻¹ ≤ 2 * (Real.cos t * (Real.sin t)⁻¹) := by
      intro t
      intro ht0
      intro ht4
      have hs0 : 0 < Real.sin t := Real.sin_pos_of_mem_Ioo ⟨ht0, by linarith [ht4, Real.pi_pos]⟩
      have hc1 : Real.sqrt 2 / 2 ≤ Real.cos t := by
        rw [← Real.cos_pi_div_four]
        exact Real.cos_le_cos_of_nonneg_of_le_pi ht0.le (by linarith [Real.pi_pos]) ht4.le
      have hroot : (1:ℝ) ≤ Real.sqrt 2 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by norm_num)
      have hcos : (1:ℝ) / 2 ≤ Real.cos t := le_trans (by linarith [hroot]) hc1
      have hsin : Real.sin t ≤ t := Real.sin_le ht0.le
      have h1 : t⁻¹ ≤ (Real.sin t)⁻¹ := (inv_le_inv₀ ht0 hs0).2 hsin
      have h2 : (Real.sin t)⁻¹ ≤ 2 * (Real.cos t * (Real.sin t)⁻¹) := by
        nlinarith [hcos, inv_pos.2 hs0]
      exact h1.trans h2
    have tan_pole_bound_right : ∀ (t : ℝ) (ht0 : 0 < t) (ht4 : t < Real.pi / 4), |t|⁻¹ ≤ 2 * |Real.tan (Real.pi / 2 + t)| := by
      intro t
      intro ht0
      intro ht4
      have hs0 : 0 < Real.sin t := Real.sin_pos_of_mem_Ioo ⟨ht0, by linarith [ht4, Real.pi_pos]⟩
      have hcpos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], by linarith [ht4, Real.pi_pos]⟩
      have h1 : Real.tan (Real.pi / 2 + t) = Real.cos t / -Real.sin t := by
        rw [add_comm, Real.tan_eq_sin_div_cos, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
      rw [h1, div_eq_mul_inv, abs_mul, abs_inv, abs_neg]
      rw [abs_of_pos ht0, abs_of_pos hcpos, abs_of_pos hs0]
      exact cot_bound ht0 ht4
    have tan_pole_bound_left : ∀ (t : ℝ) (ht0 : 0 < t) (ht4 : t < Real.pi / 4), |t|⁻¹ ≤ 2 * |Real.tan (Real.pi / 2 - t)| := by
      intro t
      intro ht0
      intro ht4
      have hs0 : 0 < Real.sin t := Real.sin_pos_of_mem_Ioo ⟨ht0, by linarith [ht4, Real.pi_pos]⟩
      have hcpos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], by linarith [ht4, Real.pi_pos]⟩
      have h1 : Real.tan (Real.pi / 2 - t) = Real.cos t / Real.sin t := by
        rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
      rw [h1, div_eq_mul_inv, abs_mul, abs_inv]
      rw [abs_of_pos ht0, abs_of_pos hcpos, abs_of_pos hs0]
      exact cot_bound ht0 ht4
    have tan_isBigO_right : ∀ {N : ℕ} (c : ℝ) (hc : c = Real.pi / 2 + N * Real.pi), (fun x : ℝ => (x - c)⁻¹) =O[𝓝[>] c] fun x => Real.tan x := by
      intro N
      intro c
      intro hc
      refine IsBigO.of_bound 2 ?_
      filter_upwards [Ioo_mem_nhdsGT (show c < c + Real.pi / 4 by linarith [Real.pi_pos])] with x hx
      obtain ⟨hcx, hxc⟩ := mem_Ioo.1 hx
      set t := x - c with ht
      have ht0 : 0 < t := sub_pos.2 hcx
      have htp : t < Real.pi / 4 := by linarith [ht, hxc]
      have hxc2 : x = c + t := by linarith [ht]
      rw [hxc2]
      simp only [Real.norm_eq_abs, abs_inv]
      rw [hc]
      have hrearr : Real.pi / 2 + N * Real.pi + t = (Real.pi / 2 + t) + N * Real.pi := by ring
      rw [hrearr, tan_add_nat_pi]
      exact tan_pole_bound_right t ht0 htp
    have tan_isBigO_left : ∀ {N : ℕ} (c : ℝ) (hc : c = Real.pi / 2 + N * Real.pi), (fun x : ℝ => (x - c)⁻¹) =O[𝓝[<] c] fun x => Real.tan x := by
      intro N
      intro c
      intro hc
      refine IsBigO.of_bound 2 ?_
      filter_upwards [Ioo_mem_nhdsLT (show c - Real.pi / 4 < c by linarith [Real.pi_pos])] with x hx
      obtain ⟨hcx, hxc⟩ := mem_Ioo.1 hx
      set t := c - x with ht
      have ht0 : 0 < t := by linarith [hxc]
      have htp : t < Real.pi / 4 := by linarith [ht, hcx]
      have hxc2 : x = c - t := by linarith [ht]
      rw [hxc2]
      simp only [Real.norm_eq_abs, abs_inv]
      have hneg : (c - t) - c = -t := by ring
      rw [hneg, abs_neg]
      rw [hc]
      have hrearr : Real.pi / 2 + N * Real.pi - t = (Real.pi / 2 - t) + N * Real.pi := by ring
      rw [hrearr, tan_add_nat_pi]
      exact tan_pole_bound_left t ht0 htp
    have linear_tail_bound : ∀ᶠ x in (atTop : Filter ℝ), ‖(x - 1)⁻¹‖ ≤ 1 * ‖x‖ := by
      filter_upwards [Ioi_mem_atTop 2] with x hx
      have hx2 : 2 < x := mem_Ioi.1 hx
      simp only [Real.norm_eq_abs, one_mul, abs_inv]
      rw [abs_of_pos (by linarith [hx2]), abs_of_pos (by linarith [hx2])]
      have h1 : (x - 1)⁻¹ ≤ 1 :=
        (inv_le_one₀ (show (0:ℝ) < x - 1 from by linarith [hx2])).2 (by linarith [hx2])
      exact h1.trans (by linarith [hx2])
    have linear_tail_isBigO : (fun x : ℝ => (x - 1)⁻¹) =O[atTop] (fun x : ℝ => x) := by
      exact IsBigO.of_bound 1 linear_tail_bound
    have exp_tail_bound : ∀ᶠ x in (atTop : Filter ℝ), ‖(x - 1)⁻¹‖ ≤ 1 * ‖Real.exp x‖ := by
      filter_upwards [Ioi_mem_atTop 2] with x hx
      have hx2 : 2 < x := mem_Ioi.1 hx
      simp only [Real.norm_eq_abs, one_mul, abs_inv]
      rw [abs_of_pos (by linarith [hx2]), abs_of_pos (Real.exp_pos _)]
      have h1 : (x - 1)⁻¹ ≤ 1 :=
        (inv_le_one₀ (show (0:ℝ) < x - 1 from by linarith [hx2])).2 (by linarith [hx2])
      have h2 : 1 ≤ Real.exp x := by
        rw [← Real.exp_zero]
        exact (Real.exp_le_exp).2 (by linarith [hx2])
      exact h1.trans h2
    have exp_tail_isBigO : (fun x : ℝ => (x - 1)⁻¹) =O[atTop] (fun x : ℝ => Real.exp x) := by
      exact IsBigO.of_bound 1 exp_tail_bound
    have const_tail_isBigO : ∀ {q : ℚ} (hq : q ≠ 0), (fun x : ℝ => (x - 1)⁻¹) =O[atTop] fun _ : ℝ => (q:ℝ) := by
      intro q
      intro hq
      refine IsBigO.of_bound ((|(q:ℝ)|)⁻¹) ?_
      filter_upwards [Ioi_mem_atTop 2] with x hx
      have hx2 : 2 < x := mem_Ioi.1 hx
      simp only [Real.norm_eq_abs, abs_inv]
      rw [abs_of_pos (by linarith [hx2])]
      have hq0 : 0 < |(q:ℝ)| := abs_pos.2 (Rat.cast_ne_zero.mpr hq)
      have hmul : (|(q:ℝ)|)⁻¹ * |(q:ℝ)| = 1 := inv_mul_cancel₀ (ne_of_gt hq0)
      rw [hmul]
      exact (inv_le_one₀ (show (0:ℝ) < x - 1 from by linarith [hx2])).2 (by linarith [hx2])
    have tail_not_converges : ∀ {g : ℝ → ℝ} {p a b : ℝ} {k : Region} (hk : ¬ k.isFinite) (hOtop : (fun x : ℝ => (x - p)⁻¹)=O[atTop] g) (hs : Set.Ioi a ⊆ k.set a b), ¬ k.Converges g a b := by
      intro g
      intro p a b
      intro k
      intro hk
      intro hOtop
      intro hs
      intro hconv
      exact not_integrableOn_Ioi_of_pole_tail hOtop ((nonfinite_converges hk hconv).mono hs le_rfl)
    have punctured_not_converges : ∀ {g : ℝ → ℝ} {c d a b : ℝ} {k : Region} (hk : ¬ k.isFinite) (hc : c < d) (hO : (fun x : ℝ => (x - c)⁻¹)=O[𝓝[>] c] g) (hs : Set.Ioo c d ⊆ k.set a b), ¬ k.Converges g a b := by
      intro g
      intro c d a b
      intro k
      intro hk
      intro hc
      intro hO
      intro hs
      intro hconv
      exact not_integrableOn_Ioo_right hc hO ((nonfinite_converges hk hconv).mono hs le_rfl)
    have finite_pole_diverges : ∀ {g : ℝ → ℝ} {c : ℝ} (hOr : (fun x : ℝ => (x - c)⁻¹)=O[𝓝[>] c] g) (hOl : (fun x : ℝ => (x - c)⁻¹)=O[𝓝[<] c] g) {a b : ℝ} (hab : a < b) (hca : a ≤ c) (hcb : c ≤ b) {k : Region} (hk : k.isFinite), ¬ k.Converges g a b := by
      intro g
      intro c
      intro hOr
      intro hOl
      intro a b
      intro hab
      intro hca
      intro hcb
      intro k
      intro hk
      intro hconv
      have hint : MeasureTheory.IntegrableOn g (Set.Ioo a b) MeasureTheory.volume := by
        cases k with
        | interval =>
          simp only [Region.Converges] at hconv
          have h1 := intervalIntegrable_iff.mp hconv
          rw [Set.uIoc_of_le (hca.trans hcb)] at h1
          exact h1.mono Set.Ioo_subset_Ioc_self le_rfl
        | icc =>
          simp only [Region.Converges, Region.set] at hconv
          exact hconv.mono Set.Ioo_subset_Icc_self le_rfl
        | ioc =>
          simp only [Region.Converges, Region.set] at hconv
          exact hconv.mono Set.Ioo_subset_Ioc_self le_rfl
        | ico =>
          simp only [Region.Converges, Region.set] at hconv
          exact hconv.mono Set.Ioo_subset_Ico_self le_rfl
        | ioo =>
          simp only [Region.Converges, Region.set] at hconv
          exact hconv
        | ioi => simp [Region.isFinite] at hk
        | ici => simp [Region.isFinite] at hk
        | univ => simp [Region.isFinite] at hk
      by_cases hcb' : c < b
      · have hsub : Set.Ioo c ((c + b) / 2) ⊆ Set.Ioo a b := by
          intro x hx
          have hx1 : c < x := hx.1
          have hx2 : x < (c + b) / 2 := hx.2
          exact ⟨lt_of_le_of_lt hca hx1, lt_trans hx2 (by linarith)⟩
        exact not_integrableOn_Ioo_right (show c < (c + b) / 2 from by linarith) hOr
          (hint.mono hsub le_rfl)
      · have hbc : b ≤ c := le_of_not_gt hcb'
        have hceq : c = b := le_antisymm hcb hbc
        have hac : a < c := hab.trans_le hbc
        have hsub : Set.Ioo ((a + c) / 2) c ⊆ Set.Ioo a b := by
          intro x hx
          have hx1 : (a + c) / 2 < x := hx.1
          have hx2 : x < c := hx.2
          exact ⟨lt_trans (by linarith) hx1, hx2.trans_le hceq.le⟩
        exact not_integrableOn_Ioo_left (show (a + c) / 2 < c from by linarith) hOl
          (hint.mono hsub le_rfl)
    have ioi_subset_cases : ∀ {a b : ℝ} {k : Region} (hk : ¬ k.isFinite), Set.Ioi a ⊆ k.set a b := by
      intro a b
      intro k
      intro hk
      cases k with
      | interval => simp [Region.isFinite] at hk
      | icc => simp [Region.isFinite] at hk
      | ioc => simp [Region.isFinite] at hk
      | ico => simp [Region.isFinite] at hk
      | ioo => simp [Region.isFinite] at hk
      | ioi => exact fun x hx => hx
      | ici => exact fun x hx => Set.mem_Ici.2 (le_of_lt (Set.mem_Ioi.1 hx))
      | univ => exact fun _ _ => Set.mem_univ _
    have ioo_subset_cases : ∀ {a b : ℝ} {k : Region} (hk : ¬ k.isFinite) (ha : a ≤ 0), Set.Ioo 0 1 ⊆ k.set a b := by
      intro a b
      intro k
      intro hk
      intro ha
      cases k with
      | interval => simp [Region.isFinite] at hk
      | icc => simp [Region.isFinite] at hk
      | ioc => simp [Region.isFinite] at hk
      | ico => simp [Region.isFinite] at hk
      | ioo => simp [Region.isFinite] at hk
      | ioi =>
        intro x hx
        have hx1 : (0:ℝ) < x := (Set.mem_Ioo.1 hx).1
        exact Set.mem_Ioi.2 (by linarith [hx1])
      | ici => exact fun x hx => Set.mem_Ici.2 (le_trans ha (le_of_lt (Set.mem_Ioo.1 hx).1))
      | univ => exact fun _ _ => Set.mem_univ _
    have notIntegrableOn_ioi : ∀ {g : ℝ → ℝ} {p a : ℝ} (hOtop : (fun x : ℝ => (x - p)⁻¹)=O[atTop] g), ¬ MeasureTheory.IntegrableOn g (Set.Ioi a) := by
      intro g
      intro p a
      intro hOtop
      exact not_integrableOn_Ioi_of_pole_tail hOtop
    have notIntegrableOn_ici : ∀ {g : ℝ → ℝ} {p a : ℝ} (hOtop : (fun x : ℝ => (x - p)⁻¹)=O[atTop] g), ¬ MeasureTheory.IntegrableOn g (Set.Ici a) := by
      intro g
      intro p a
      intro hOtop
      intro h
      exact notIntegrableOn_ioi hOtop
        (h.mono (fun x hx => Set.mem_Ici.2 (le_of_lt (Set.mem_Ioi.1 hx))) le_rfl)
    have notIntegrableOn_univ : ∀ {g : ℝ → ℝ} {p : ℝ} (hOtop : (fun x : ℝ => (x - p)⁻¹)=O[atTop] g), ¬ MeasureTheory.IntegrableOn g Set.univ := by
      intro g
      intro p
      intro hOtop
      intro h
      exact not_integrableOn_Ioi_of_pole_tail (a := 0) hOtop (h.mono (fun _ _ => Set.mem_univ _) le_rfl)
    have notIntegrableOn_punctured : ∀ {g : ℝ → ℝ} {c d : ℝ} {s : Set ℝ} (hc : c < d) (hO : (fun x : ℝ => (x - c)⁻¹)=O[𝓝[>] c] g) (hs : Set.Ioo c d ⊆ s), ¬ MeasureTheory.IntegrableOn g s := by
      intro g
      intro c d
      intro s
      intro hc
      intro hO
      intro hs
      intro h
      exact not_integrableOn_Ioo_right hc hO (h.mono hs le_rfl)
    have punctured_between : ∀ {g : ℝ → ℝ} {c a b : ℝ} (hOr : (fun x : ℝ => (x - c)⁻¹)=O[𝓝[>] c] g) (hOl : (fun x : ℝ => (x - c)⁻¹)=O[𝓝[<] c] g) (hab : a < b) (hca : a ≤ c) (hcb : c ≤ b) (hint : MeasureTheory.IntegrableOn g (Set.Ioo a b) MeasureTheory.volume), False := by
      intro g
      intro c a b
      intro hOr
      intro hOl
      intro hab
      intro hca
      intro hcb
      intro hint
      by_cases hcb' : c < b
      · refine not_integrableOn_Ioo_right (show c < (c + b) / 2 from by linarith) hOr ?_
        exact hint.mono (by
          intro x hx
          have hx1 : c < x := hx.1
          have hx2 : x < (c + b) / 2 := hx.2
          exact ⟨lt_of_le_of_lt hca hx1, lt_trans hx2 (by linarith)⟩) le_rfl
      · have hceq : c = b := le_antisymm hcb (le_of_not_gt hcb')
        refine not_integrableOn_Ioo_left (show (a + c) / 2 < c from by linarith) hOl ?_
        exact hint.mono (by
          intro x hx
          have hx1 : (a + c) / 2 < x := hx.1
          have hx2 : x < c := hx.2
          exact ⟨lt_trans (by linarith [hab, hceq]) hx1, hx2.trans_le hceq.le⟩) le_rfl
    have pole_between_not_converges : ∀ {g : ℝ → ℝ} {c a b : ℝ} {k : Region} (hOr : (fun x : ℝ => (x - c)⁻¹)=O[𝓝[>] c] g) (hOl : (fun x : ℝ => (x - c)⁻¹)=O[𝓝[<] c] g) (hab : a < b) (hca : a ≤ c) (hcb : c ≤ b), ¬ k.Converges g a b := by
      intro g
      intro c a b
      intro k
      intro hOr
      intro hOl
      intro hab
      intro hca
      intro hcb
      intro hconv
      cases k with
      | interval =>
        simp only [Region.Converges] at hconv
        have h1 := intervalIntegrable_iff.mp hconv
        rw [Set.uIoc_of_le (le_trans hca hcb)] at h1
        exact punctured_between hOr hOl hab hca hcb (h1.mono Set.Ioo_subset_Ioc_self le_rfl)
      | icc =>
        simp only [Region.Converges, Region.set] at hconv
        exact punctured_between hOr hOl hab hca hcb (hconv.mono Set.Ioo_subset_Icc_self le_rfl)
      | ioc =>
        simp only [Region.Converges, Region.set] at hconv
        exact punctured_between hOr hOl hab hca hcb (hconv.mono Set.Ioo_subset_Ioc_self le_rfl)
      | ico =>
        simp only [Region.Converges, Region.set] at hconv
        exact punctured_between hOr hOl hab hca hcb (hconv.mono Set.Ioo_subset_Ico_self le_rfl)
      | ioo =>
        simp only [Region.Converges, Region.set] at hconv
        exact punctured_between hOr hOl hab hca hcb hconv
      | ioi =>
        simp only [Region.Converges, Region.set] at hconv
        exact not_integrableOn_Ioo_right (show c < c + 1 from by linarith) hOr
          (hconv.mono (fun x hx => Set.mem_Ioi.2 (lt_of_le_of_lt hca (Set.mem_Ioo.1 hx).1)) le_rfl)
      | ici =>
        simp only [Region.Converges, Region.set] at hconv
        exact not_integrableOn_Ioo_right (show c < c + 1 from by linarith) hOr
          (hconv.mono (fun x hx =>
            Set.mem_Ici.2 (le_trans hca (le_of_lt (Set.mem_Ioo.1 hx).1))) le_rfl)
      | univ =>
        simp only [Region.Converges, Region.set] at hconv
        exact not_integrableOn_Ioo_right (show c < c + 1 from by linarith) hOr
          (hconv.mono (fun x _ => Set.mem_univ x) le_rfl)
    have linear_not_converges : ∀ {k : Region} {a b : ℝ} (hk : ¬ k.isFinite), ¬ k.Converges (fun x : ℝ => x) a b := by
      intro k
      intro a b
      intro hk
      exact tail_not_converges hk linear_tail_isBigO (ioi_subset_cases hk)
    have constant_not_converges : ∀ {q : ℚ} (hq : q ≠ 0) {k : Region} {a b : ℝ} (hk : ¬ k.isFinite), ¬ k.Converges (fun _ : ℝ => (q:ℝ)) a b := by
      intro q
      intro hq
      intro k
      intro a b
      intro hk
      exact tail_not_converges hk (const_tail_isBigO hq) (ioi_subset_cases hk)
    have exponential_not_converges : ∀ {k : Region} {a b : ℝ} (hk : ¬ k.isFinite), ¬ k.Converges (fun x : ℝ => Real.exp x) a b := by
      intro k
      intro a b
      intro hk
      exact tail_not_converges hk exp_tail_isBigO (ioi_subset_cases hk)
    have sine_not_converges : ∀ {k : Region} {a b : ℝ} (hk : ¬ k.isFinite), ¬ k.Converges (fun x : ℝ => Real.sin x) a b := by
      intro k
      intro a b
      intro hk
      intro hconv
      have ht : ¬ MeasureTheory.IntegrableOn Real.sin (Set.Ioi a) MeasureTheory.volume :=
        not_integrable_periodic_tail Real.two_pi_pos Real.sin_periodic
          intervalIntegral.intervalIntegrable_sin
          (by
            refine intervalIntegral.integral_pos Real.two_pi_pos ?_ ?_ ?_
            · exact (continuous_abs.comp Real.continuous_sin).continuousOn.mono (Set.subset_univ _)
            · intro x _; exact abs_nonneg _
            · exact ⟨Real.pi / 2, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
                by rw [Real.sin_pi_div_two]; norm_num⟩)
          a
      exact ht ((nonfinite_converges hk hconv).mono (ioi_subset_cases hk) le_rfl)
    have invPow_tail : ∀ {a : ℝ} {s : Set ℝ} (hs : Set.Ioi a ⊆ s), ¬ MeasureTheory.IntegrableOn (fun x : ℝ => (x ^ 1)⁻¹) s := by
      intro a
      intro s
      intro hs
      intro h
      have h' : MeasureTheory.IntegrableOn (fun x : ℝ => x⁻¹) s MeasureTheory.volume := by
        simpa only [pow_one] using h
      exact notIntegrableOn_ioi (inv_one_isBigO (atTop : Filter ℝ)) (h'.mono hs le_rfl)
    have invPow_punctured : ∀ {n : ℕ} {s : Set ℝ} (hn : 0 < n) (hs : Set.Ioo 0 1 ⊆ s), ¬ MeasureTheory.IntegrableOn (fun x : ℝ => (x ^ n)⁻¹) s := by
      intro n
      intro s
      intro hn
      intro hs
      exact notIntegrableOn_punctured (show (0:ℝ) < 1 from by norm_num) (inv_pow_isBigO_right hn) hs
    have tangent_not_converges : ∀ {a : ℝ} {s : Set ℝ} (hs : Set.Ioi a ⊆ s), ¬ MeasureTheory.IntegrableOn (fun x : ℝ => Real.tan x) s := by
      intro a
      intro s
      intro hs
      obtain ⟨N, hN⟩ := exists_nat_ge ((a - Real.pi / 2) / Real.pi)
      have hN' : a - Real.pi / 2 ≤ (N : ℝ) * Real.pi := (div_le_iff₀ Real.pi_pos).mp hN
      have hN'' : a ≤ Real.pi / 2 + (N : ℝ) * Real.pi := by linarith
      exact notIntegrableOn_punctured
        (show Real.pi / 2 + (N : ℝ) * Real.pi < Real.pi / 2 + (N : ℝ) * Real.pi + 1 from by linarith)
        (tan_isBigO_right (N := N) (c := Real.pi / 2 + (N : ℝ) * Real.pi) (by ring))
        (Set.Subset.trans
          (fun x hx => Set.mem_Ioi.2 (lt_of_le_of_lt hN'' (Set.mem_Ioo.1 hx).1)) hs)
    cases e with
    | var =>
      simp only [classifyDivergence, Option.some.injEq] at hclass
      subst hclass
      simp only [Term.real]
      exact linear_not_converges h
    | pi => simp [classifyDivergence] at hclass
    | pow a n => simp [classifyDivergence] at hclass
    | rpow a q => simp [classifyDivergence] at hclass
    | rat q =>
      by_cases hq0 : q = 0
      · simp [classifyDivergence, hq0] at hclass
      · have hX : classifyDivergence (.rat q) = some (DivergenceRule.constant q) := by
          simp [classifyDivergence, hq0]
        rw [hX] at hclass
        have hr : DivergenceRule.constant q = r := Option.some.inj hclass
        subst hr
        simp only [Term.real]
        exact constant_not_converges hq0 h
    | unary op a =>
      cases op with
      | neg | cos | sinh | cosh | log | sqrt | abs | floor | atan | erf | si | eta | airyAi =>
        simp [classifyDivergence] at hclass
      | sin =>
        cases a with
        | var =>
          simp only [classifyDivergence, Option.some.injEq] at hclass
          subst hclass
          simp only [Term.real, Unary.real]
          exact sine_not_converges h
        | _ => simp [classifyDivergence] at hclass
      | exp =>
        cases a with
        | var =>
          simp only [classifyDivergence, Option.some.injEq] at hclass
          subst hclass
          simp only [Term.real, Unary.real]
          exact exponential_not_converges h
        | _ => simp [classifyDivergence] at hclass
      | inv =>
        cases a with
        | var =>
          simp only [classifyDivergence, Option.some.injEq] at hclass
          subst hclass
          simp only [Term.real, Unary.real]
          cases k with
          | interval | icc | ioc | ico | ioo =>
            simp [DivergenceRule.Condition, Region.isFinite] at h
            exact pole_between_not_converges (inv_one_isBigO (𝓝[>] (0:ℝ)))
              (inv_one_isBigO (𝓝[<] (0:ℝ))) h.1 h.2.1 h.2.2
          | ioi =>
            simp only [Region.Converges, Region.set]
            exact notIntegrableOn_ioi (inv_one_isBigO (atTop : Filter ℝ))
          | ici =>
            simp only [Region.Converges, Region.set]
            exact notIntegrableOn_ici (inv_one_isBigO (atTop : Filter ℝ))
          | univ =>
            simp only [Region.Converges, Region.set]
            exact notIntegrableOn_univ (inv_one_isBigO (atTop : Filter ℝ))
        | pow a' n =>
          cases a' with
          | var =>
            have hn0 : 0 < n := by
              by_contra hcon
              simp [classifyDivergence, hcon] at hclass
            have hX : classifyDivergence (.unary .inv (.pow .var n))
                = some (DivergenceRule.invPower n) := by
              simp [classifyDivergence, hn0]
            rw [hX] at hclass
            have hr : DivergenceRule.invPower n = r := Option.some.inj hclass
            subst hr
            simp only [Term.real, Unary.real]
            cases k with
            | interval | icc | ioc | ico | ioo =>
              simp [DivergenceRule.Condition, Region.isFinite] at h
              exact pole_between_not_converges (inv_pow_isBigO_right hn0)
                (inv_pow_isBigO_left hn0) h.1 h.2.1 h.2.2.1
            | ioi =>
              simp [DivergenceRule.Condition, Region.isFinite] at h
              simp only [Region.Converges, Region.set]
              rcases h with h1 | ⟨ha, hn⟩
              · subst h1
                exact invPow_tail (fun x hx => hx)
              · exact invPow_punctured hn
                  (fun x hx => Set.mem_Ioi.2 (by linarith [(Set.mem_Ioo.1 hx).1]))
            | ici =>
              simp [DivergenceRule.Condition, Region.isFinite] at h
              simp only [Region.Converges, Region.set]
              rcases h with h1 | ⟨ha, hn⟩
              · subst h1
                exact invPow_tail (fun x hx => Set.mem_Ici.2 (le_of_lt (Set.mem_Ioi.1 hx)))
              · exact invPow_punctured hn
                  (fun x hx => Set.mem_Ici.2 (le_trans ha (le_of_lt (Set.mem_Ioo.1 hx).1)))
            | univ =>
              simp [DivergenceRule.Condition, Region.isFinite] at h
              simp only [Region.Converges, Region.set]
              exact invPow_punctured h (fun _ _ => Set.mem_univ _)
          | _ => simp [classifyDivergence] at hclass
        | binary op' l r' =>
          cases op' with
          | sub =>
            cases l with
            | rat p =>
              cases r' with
              | var =>
                simp only [classifyDivergence, Option.some.injEq] at hclass
                subst hclass
                simp only [Term.real, Unary.real, Binary.real]
                cases k with
                | interval | icc | ioc | ico | ioo =>
                  simp [DivergenceRule.Condition, Region.isFinite] at h
                  exact pole_between_not_converges (shift_isBigO (𝓝[>] (p : ℝ)))
                    (shift_isBigO (𝓝[<] (p : ℝ))) h.1 h.2.1 h.2.2
                | ioi =>
                  simp only [Region.Converges, Region.set]
                  exact notIntegrableOn_ioi (shift_isBigO (atTop : Filter ℝ) (p := (p : ℝ)))
                | ici =>
                  simp only [Region.Converges, Region.set]
                  exact notIntegrableOn_ici (shift_isBigO (atTop : Filter ℝ) (p := (p : ℝ)))
                | univ =>
                  simp only [Region.Converges, Region.set]
                  exact notIntegrableOn_univ (shift_isBigO (atTop : Filter ℝ) (p := (p : ℝ)))
              | _ => simp [classifyDivergence] at hclass
            | _ => simp [classifyDivergence] at hclass
          | _ => simp [classifyDivergence] at hclass
        | _ => simp [classifyDivergence] at hclass
    | binary op l r' =>
      cases op with
      | add | sub | mul | max | min => simp [classifyDivergence] at hclass
      | div =>
        cases l with
        | rat q =>
          cases r' with
          | var =>
            have hq1 : q = 1 := by
              by_contra hcon
              simp [classifyDivergence, hcon] at hclass
            have hone : ((1:ℚ) : ℝ) = 1 := by norm_num
            have hX : classifyDivergence (.binary .div (.rat q) .var)
                = some (DivergenceRule.invPower 1) := by
              simp [classifyDivergence, hq1]
            rw [hX] at hclass
            have hr : DivergenceRule.invPower 1 = r := Option.some.inj hclass
            subst hr
            simp only [Term.real, Binary.real, hq1, hone, one_div]
            cases k with
            | interval | icc | ioc | ico | ioo =>
              simp [DivergenceRule.Condition, Region.isFinite] at h
              exact pole_between_not_converges (inv_one_isBigO (𝓝[>] (0:ℝ)))
                (inv_one_isBigO (𝓝[<] (0:ℝ))) h.1 h.2.1 h.2.2
            | ioi =>
              simp only [Region.Converges, Region.set]
              exact notIntegrableOn_ioi (inv_one_isBigO (atTop : Filter ℝ))
            | ici =>
              simp only [Region.Converges, Region.set]
              exact notIntegrableOn_ici (inv_one_isBigO (atTop : Filter ℝ))
            | univ =>
              simp only [Region.Converges, Region.set]
              exact notIntegrableOn_univ (inv_one_isBigO (atTop : Filter ℝ))
          | pow a' n =>
            cases a' with
            | var =>
              have hq1 : q = 1 := by
                by_contra hcon
                simp [classifyDivergence, hcon] at hclass
              have hn0 : 0 < n := by
                by_contra hcon
                simp [classifyDivergence, hq1, hcon] at hclass
              have hX : classifyDivergence (.binary .div (.rat q) (.pow .var n))
                  = some (DivergenceRule.invPower n) := by
                simp [classifyDivergence, hq1, hn0]
              rw [hX] at hclass
              have hr : DivergenceRule.invPower n = r := Option.some.inj hclass
              subst hr
              have hone : ((1:ℚ) : ℝ) = 1 := by norm_num
              simp only [Term.real, Binary.real, hq1, hone, one_div]
              cases k with
              | interval | icc | ioc | ico | ioo =>
                simp [DivergenceRule.Condition, Region.isFinite] at h
                exact pole_between_not_converges (inv_pow_isBigO_right hn0)
                  (inv_pow_isBigO_left hn0) h.1 h.2.1 h.2.2.1
              | ioi =>
                simp [DivergenceRule.Condition, Region.isFinite] at h
                simp only [Region.Converges, Region.set]
                rcases h with h1 | ⟨ha, hn⟩
                · subst h1
                  exact invPow_tail (fun x hx => hx)
                · exact invPow_punctured hn
                    (fun x hx => Set.mem_Ioi.2 (by linarith [(Set.mem_Ioo.1 hx).1]))
              | ici =>
                simp [DivergenceRule.Condition, Region.isFinite] at h
                simp only [Region.Converges, Region.set]
                rcases h with h1 | ⟨ha, hn⟩
                · subst h1
                  exact invPow_tail (fun x hx => Set.mem_Ici.2 (le_of_lt (Set.mem_Ioi.1 hx)))
                · exact invPow_punctured hn
                    (fun x hx => Set.mem_Ici.2 (le_trans ha (le_of_lt (Set.mem_Ioo.1 hx).1)))
              | univ =>
                simp [DivergenceRule.Condition, Region.isFinite] at h
                simp only [Region.Converges, Region.set]
                exact invPow_punctured h (fun _ _ => Set.mem_univ _)
            | _ => simp [classifyDivergence] at hclass
          | binary op' l' r'' =>
            cases op' with
            | sub =>
              cases l' with
              | rat p =>
                cases r'' with
                | var =>
                  have hq1 : q = 1 := by
                    by_contra hcon
                    simp [classifyDivergence, hcon] at hclass
                  have hX :
                      classifyDivergence (.binary .div (.rat q) (.binary .sub (.rat p) .var))
                        = some (DivergenceRule.shiftedInv p) := by
                    simp [classifyDivergence, hq1]
                  rw [hX] at hclass
                  have hr : DivergenceRule.shiftedInv p = r := Option.some.inj hclass
                  subst hr
                  have hone : ((1:ℚ) : ℝ) = 1 := by norm_num
                  simp only [Term.real, Binary.real, hq1, hone, one_div]
                  cases k with
                  | interval | icc | ioc | ico | ioo =>
                    simp [DivergenceRule.Condition, Region.isFinite] at h
                    exact pole_between_not_converges (shift_isBigO (𝓝[>] (p : ℝ)))
                      (shift_isBigO (𝓝[<] (p : ℝ))) h.1 h.2.1 h.2.2
                  | ioi =>
                    simp only [Region.Converges, Region.set]
                    exact notIntegrableOn_ioi (shift_isBigO (atTop : Filter ℝ) (p := (p : ℝ)))
                  | ici =>
                    simp only [Region.Converges, Region.set]
                    exact notIntegrableOn_ici (shift_isBigO (atTop : Filter ℝ) (p := (p : ℝ)))
                  | univ =>
                    simp only [Region.Converges, Region.set]
                    exact notIntegrableOn_univ (shift_isBigO (atTop : Filter ℝ) (p := (p : ℝ)))
                | _ => simp [classifyDivergence] at hclass
              | _ => simp [classifyDivergence] at hclass
            | _ => simp [classifyDivergence] at hclass
          | _ => simp [classifyDivergence] at hclass
        | unary op' a' =>
          cases op' with
          | sin =>
            cases a' with
            | var =>
              cases r' with
              | unary op2 a2 =>
                cases op2 with
                | cos =>
                  cases a2 with
                  | var =>
                    simp only [classifyDivergence, Option.some.injEq] at hclass
                    subst hclass
                    simp only [Term.real, Unary.real, Binary.real, ← Real.tan_eq_sin_div_cos]
                    cases k with
                    | interval | icc | ioc | ico | ioo =>
                      simp [DivergenceRule.Condition, Region.isFinite] at h
                      exact pole_between_not_converges
                        (tan_isBigO_right (N := 0) (c := Real.pi / 2) (by ring))
                        (tan_isBigO_left (N := 0) (c := Real.pi / 2) (by ring))
                        h.1 h.2.1 h.2.2
                    | ioi =>
                      simp only [Region.Converges, Region.set]
                      exact tangent_not_converges (fun x hx => hx)
                    | ici =>
                      simp only [Region.Converges, Region.set]
                      exact tangent_not_converges
                        (fun x hx => Set.mem_Ici.2 (le_of_lt (Set.mem_Ioi.1 hx)))
                    | univ =>
                      simp only [Region.Converges, Region.set]
                      exact tangent_not_converges (a := a) (fun _ _ => Set.mem_univ _)
                  | _ => simp [classifyDivergence] at hclass
                | _ => simp [classifyDivergence] at hclass
              | _ => simp [classifyDivergence] at hclass
            | _ => simp [classifyDivergence] at hclass
          | _ => simp [classifyDivergence] at hclass
        | _ => simp [classifyDivergence] at hclass
end Intgrl
