import Lynth.Interval.Integral.Math.NestedSyntaxLemmas
import Lynth.Interval.Integral.Math.NestedAnalysis

/-! Semantics of power regularization and the one-dimensional changes of
variables used by `transformed`. -/

namespace Lynth.Interval.Integral.Nested
open Intgrl MeasureTheory Set

theorem collectPower_sound {level : Nat} {env : List ℝ} {t : ℝ} (ht : 0 < t)
    (hl : env[level]? = some t) (e : Expr) :
    e.real env = t ^ (((collectPower level e).1 : ℚ) : ℝ) * (collectPower level e).2.real env ∧
    ((collectPower level e).2.Converges env → e.Converges env) := by
  have hv : ∀ r : ℚ, (rpow (.var level) r).real env = t ^ (r : ℝ) := by
    intro r; rw [rpow_real]; simp [NExpr.real, hl]
  induction e with
  | var i =>
    simp only [collectPower]
    split
    · rename_i h
      have : i = level := by simpa using h
      subst this; simp [NExpr.real, NExpr.Converges, hl]
    · simp [NExpr.real]
  | rat | pi => simp [collectPower]
  | integral => simp [collectPower]
  | rpow a q ih => simp [collectPower]
  | pow a n ih =>
    rcases hc : collectPower level a with ⟨p, A⟩
    rw [hc] at ih
    simp only [collectPower, hc]
    refine ⟨?_, fun h => ih.2 ((pow_converges _ _ _).1 h)⟩
    rw [NExpr.real, ih.1, pow_real, mul_pow, ← Real.rpow_natCast (t ^ _), ← Real.rpow_mul ht.le]
    push_cast; ring_nf
  | unary op a ih =>
    rcases hc : collectPower level a with ⟨p, A⟩
    rw [hc] at ih
    cases op
    case neg =>
      simp only [collectPower, hc]
      refine ⟨?_, fun h => ih.2 ((neg_converges _ _).1 h)⟩
      rw [NExpr.real, ih.1, neg_real]; simp [Unary.real]
    case inv =>
      simp only [collectPower, hc]
      refine ⟨?_, fun h => ih.2 h⟩
      simp only [NExpr.real, Unary.real, ih.1]
      push_cast
      rw [Real.rpow_neg ht.le, mul_inv]
    case sqrt =>
      simp only [collectPower, hc]
      refine ⟨?_, fun h => ih.2 h⟩
      simp only [NExpr.real, Unary.real, ih.1]
      rw [Real.sqrt_mul (Real.rpow_nonneg ht.le _), Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
      push_cast; ring_nf
    all_goals simp [collectPower]
  | binary op a b iha ihb =>
    rcases hca : collectPower level a with ⟨p, A⟩
    rcases hcb : collectPower level b with ⟨q, B⟩
    rw [hca] at iha; rw [hcb] at ihb
    cases op
    case mul =>
      simp only [collectPower, hca, hcb]
      refine ⟨?_, fun h => ?_⟩
      · simp only [NExpr.real, Binary.real, mul_real, iha.1, ihb.1]
        push_cast; rw [Real.rpow_add ht]; ring
      · rw [mul_converges] at h; exact ⟨iha.2 h.1, ihb.2 h.2⟩
    case div =>
      simp only [collectPower, hca, hcb]
      refine ⟨?_, fun h => ?_⟩
      · simp only [NExpr.real, Binary.real, div_real, iha.1, ihb.1]
        push_cast; rw [Real.rpow_sub ht]; field_simp
      · rw [div_converges] at h; exact ⟨iha.2 h.1, ihb.2 h.2⟩
    case add =>
      simp only [collectPower, hca, hcb]
      simp only [show (Binary.add == Binary.add) = true from rfl, ↓reduceIte]
      refine ⟨?_, fun h => ?_⟩
      · simp only [NExpr.real, Binary.real, add_real, mul_real, hv, iha.1, ihb.1]
        push_cast
        rw [mul_add, ← mul_assoc, ← mul_assoc, ← Real.rpow_add ht, ← Real.rpow_add ht]
        ring_nf
      · simp only [add_converges, mul_converges] at h
        exact ⟨iha.2 h.1.2, ihb.2 h.2.2⟩
    case sub =>
      simp only [collectPower, hca, hcb]
      simp only [show (Binary.sub == Binary.add) = false from rfl, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, fun h => ?_⟩
      · simp only [NExpr.real, Binary.real, sub_real, mul_real, hv, iha.1, ihb.1]
        push_cast
        rw [mul_sub, ← mul_assoc, ← mul_assoc, ← Real.rpow_add ht, ← Real.rpow_add ht]
        ring_nf
      · simp only [sub_converges, mul_converges] at h
        exact ⟨iha.2 h.1.2, ihb.2 h.2.2⟩
    all_goals simp [collectPower]

theorem regularize_sound {level : Nat} {env : List ℝ} {t : ℝ} (ht : 0 < t)
    (hl : env[level]? = some t) (e : Expr) :
    (regularize level e).real env = e.real env ∧
    ((regularize level e).Converges env → e.Converges env) := by
  have hv : ∀ r : ℚ, (rpow (.var level) r).real env = t ^ (r : ℝ) := by
    intro r; rw [rpow_real]; simp [NExpr.real, hl]
  have hc := collectPower_sound ht hl (simplify e)
  have hs := simplify_sound e env
  unfold regularize
  rcases hcp : collectPower level (simplify e) with ⟨p, A⟩
  rw [hcp] at hc
  simp only
  have h2 := simplify_sound (mul (rpow (.var level) p) A) env
  refine ⟨?_, fun h => ?_⟩
  · rw [h2.1, mul_real, hv, ← hc.1, hs.1]
  · rw [h2.2, mul_converges] at h
    exact hs.2.1 (hc.2 h.2)


theorem cov_Ioo01 {φ φ' F g : ℝ → ℝ} {T : Set ℝ}
    (hφ : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivWithinAt φ (φ' t) (Ioo 0 1) t)
    (hinj : InjOn φ (Ioo 0 1)) (himg : φ '' Ioo 0 1 = T)
    (hg : ∀ t ∈ Ioo (0:ℝ) 1, g t = |φ' t| * F (φ t)) (hint : IntegrableOn g (Ioo 0 1)) :
    IntegrableOn F T ∧ ∫ x in T, F x = ∫ t in Ioo 0 1, g t := by
  subst himg
  refine ⟨?_, ?_⟩
  · rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hφ hinj]
    refine hint.congr_fun (fun t ht => ?_) measurableSet_Ioo
    simp [hg t ht]
  · rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hφ hinj]
    refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    simp [hg t ht]

theorem ii01_iff (g : ℝ → ℝ) : IntervalIntegrable g volume 0 1 ↔ IntegrableOn g (Ioo 0 1) :=
  intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one

theorem int01 (g : ℝ → ℝ) : ∫ t in (0:ℝ)..1, g t = ∫ t in Ioo 0 1, g t := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

theorem affine_interval {F g : ℝ → ℝ} {α β : ℝ}
    (hg : ∀ t ∈ Ioo (0:ℝ) 1, g t = (β - α) * F (α + (β - α) * t))
    (hint : IntegrableOn g (Ioo 0 1)) :
    IntervalIntegrable F volume α β ∧ ∫ x in α..β, F x = ∫ t in Ioo 0 1, g t := by
  have hd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivWithinAt (fun t => α + (β - α) * t) (β - α) (Ioo 0 1) t := by
    intro t _
    simpa using ((hasDerivAt_id t).const_mul (β - α)).const_add α |>.hasDerivWithinAt
  rcases lt_trichotomy α β with h | h | h
  · have hinj : InjOn (fun t => α + (β - α) * t) (Ioo 0 1) := by
      intro x _ y _ hxy
      have : (β - α) * x = (β - α) * y := by simpa using hxy
      exact mul_left_cancel₀ (by linarith) this
    have himg : (fun t => α + (β - α) * t) '' Ioo 0 1 = Ioo α β := by
      ext x; constructor
      · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
        constructor <;> nlinarith
      · rintro ⟨h0, h1⟩
        refine ⟨(x - α) / (β - α), ⟨?_, ?_⟩, ?_⟩
        · apply div_pos <;> linarith
        · rw [div_lt_one (by linarith)]; linarith
        · field_simp; ring
    obtain ⟨h1, h2⟩ := cov_Ioo01 (F := F) hd hinj himg
      (fun t ht => by rw [hg t ht, abs_of_pos (by linarith)]) hint
    refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le h.le).2 h1, ?_⟩
    rw [intervalIntegral.integral_of_le h.le, integral_Ioc_eq_integral_Ioo, h2]
  · subst h
    refine ⟨IntervalIntegrable.refl, ?_⟩
    rw [intervalIntegral.integral_same]
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0:ℝ)) (fun t ht => by simp [hg t ht])]
    simp
  · have hinj : InjOn (fun t => α + (β - α) * t) (Ioo 0 1) := by
      intro x _ y _ hxy
      have : (β - α) * x = (β - α) * y := by simpa using hxy
      exact mul_left_cancel₀ (by linarith) this
    have himg : (fun t => α + (β - α) * t) '' Ioo 0 1 = Ioo β α := by
      ext x; constructor
      · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
        constructor <;> nlinarith
      · rintro ⟨h0, h1⟩
        refine ⟨(α - x) / (α - β), ⟨?_, ?_⟩, ?_⟩
        · apply div_pos <;> linarith
        · rw [div_lt_one (by linarith)]; linarith
        · field_simp; ring
    obtain ⟨h1, h2⟩ := cov_Ioo01 (F := F) (g := fun t => -g t) hd hinj himg
      (fun t ht => by rw [hg t ht, abs_of_neg (by linarith)]; ring) hint.neg
    refine ⟨((intervalIntegrable_iff_integrableOn_Ioo_of_le h.le).2 h1).symm, ?_⟩
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le h.le,
      integral_Ioc_eq_integral_Ioo, h2, integral_neg, neg_neg]

theorem power_transport {m : ℕ} (hm : 0 < m) (right : Bool) {h g : ℝ → ℝ}
    (hg : ∀ t ∈ Ioo (0:ℝ) 1, g t = m * t ^ (m - 1) * h (if right then 1 - t ^ m else t ^ m))
    (hint : IntegrableOn g (Ioo 0 1)) :
    IntegrableOn h (Ioo 0 1) ∧ ∫ s in Ioo 0 1, h s = ∫ t in Ioo 0 1, g t := by
  have hmono : StrictMonoOn (fun t : ℝ => t ^ m) (Ioo 0 1) := by
    intro x hx y _ hxy
    exact pow_lt_pow_left₀ hxy hx.1.le hm.ne'
  have himg0 : (fun t : ℝ => t ^ m) '' Ioo 0 1 = Ioo 0 1 := by
    ext s; constructor
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
      exact ⟨pow_pos h0 m, pow_lt_one₀ h0.le h1 hm.ne'⟩
    · rintro ⟨h0, h1⟩
      refine ⟨s ^ ((m:ℝ)⁻¹), ⟨Real.rpow_pos_of_pos h0 _, ?_⟩, ?_⟩
      · exact Real.rpow_lt_one h0.le h1 (by positivity)
      · simp only
        rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, inv_mul_cancel₀ (by positivity),
          Real.rpow_one]
  have hd0 : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivWithinAt (fun t : ℝ => t ^ m)
      ((m:ℝ) * t ^ (m - 1)) (Ioo 0 1) t := by
    intro t _
    simpa using (hasDerivAt_pow m t).hasDerivWithinAt
  cases right
  · exact cov_Ioo01 hd0 hmono.injOn himg0 (fun t ht => by
      rw [hg t ht, abs_of_nonneg (by have := ht.1; positivity)]; simp) hint
  · have hd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivWithinAt (fun t : ℝ => 1 - t ^ m)
        (-((m:ℝ) * t ^ (m - 1))) (Ioo 0 1) t := by
      intro t ht
      simpa using (hd0 t ht).const_sub 1
    have hinj : InjOn (fun t : ℝ => 1 - t ^ m) (Ioo 0 1) := by
      intro x hx y hy hxy
      exact hmono.injOn hx hy (by simpa using hxy)
    have himg : (fun t : ℝ => 1 - t ^ m) '' Ioo 0 1 = Ioo 0 1 := by
      rw [show (fun t : ℝ => 1 - t ^ m) = (fun s => 1 - s) ∘ (fun t : ℝ => t ^ m) from rfl,
        image_comp, himg0]
      ext s; simp only [mem_image, mem_Ioo]
      constructor
      · rintro ⟨u, ⟨h0, h1⟩, rfl⟩; constructor <;> linarith
      · rintro ⟨h0, h1⟩; exact ⟨1 - s, ⟨by linarith, by linarith⟩, by ring⟩
    exact cov_Ioo01 hd hinj himg (fun t ht => by
      rw [hg t ht, abs_neg, abs_of_nonneg (by have := ht.1; positivity)]; simp) hint

theorem tail_transport (right : Bool) {F g : ℝ → ℝ} {α : ℝ}
    (hg : ∀ t ∈ Ioo (0:ℝ) 1, g t =
      F (if right then α + ((1 - t)⁻¹ - 1) else α - ((1 - t)⁻¹ - 1)) / (1 - t) ^ 2)
    (hint : IntegrableOn g (Ioo 0 1)) :
    IntegrableOn F (if right then Ioi α else Iio α) ∧
      ∫ x in (if right then Ioi α else Iio α), F x = ∫ t in Ioo 0 1, g t := by
  have hu : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivWithinAt (fun t : ℝ => (1 - t)⁻¹ - 1)
      (((1 - t) ^ 2)⁻¹) (Ioo 0 1) t := by
    intro t ht
    have h1 : (1 - t) ≠ 0 := by linarith [ht.2]
    have := ((hasDerivAt_id t).const_sub 1).inv h1
    have := this.sub_const 1
    refine HasDerivAt.hasDerivWithinAt (this.congr_deriv ?_)
    simp only [id, neg_neg, one_div]
  have hmono : StrictMonoOn (fun t : ℝ => (1 - t)⁻¹ - 1) (Ioo 0 1) := by
    intro x hx y hy hxy
    simp only
    have : (1 - x)⁻¹ < (1 - y)⁻¹ := by
      apply inv_strictAnti₀ (by linarith [hy.2]) (by linarith)
    linarith
  have himg0 : (fun t : ℝ => (1 - t)⁻¹ - 1) '' Ioo 0 1 = Ioi 0 := by
    ext u; constructor
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
      simp only [mem_Ioi, sub_pos]
      exact one_lt_inv₀ (by linarith) |>.2 (by linarith)
    · intro hu0
      simp only [mem_Ioi] at hu0
      refine ⟨u / (1 + u), ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_lt_one (by linarith)]; linarith
      · simp only
        have : 1 - u / (1 + u) = (1 + u)⁻¹ := by field_simp; ring
        rw [this, inv_inv]; ring
  have hpos : ∀ t ∈ Ioo (0:ℝ) 1, 0 < ((1 - t) ^ 2)⁻¹ := fun t ht => by
    have : 0 < 1 - t := by linarith [ht.2]
    positivity
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte] at hg ⊢
    have hd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivWithinAt (fun t : ℝ => α - ((1 - t)⁻¹ - 1))
        (-((1 - t) ^ 2)⁻¹) (Ioo 0 1) t := fun t ht => (hu t ht).const_sub α
    have hinj : InjOn (fun t : ℝ => α - ((1 - t)⁻¹ - 1)) (Ioo 0 1) := by
      intro x hx y hy hxy
      exact hmono.injOn hx hy (by simpa using hxy)
    have himg : (fun t : ℝ => α - ((1 - t)⁻¹ - 1)) '' Ioo 0 1 = Iio α := by
      rw [show (fun t : ℝ => α - ((1 - t)⁻¹ - 1)) =
        (fun u => α - u) ∘ (fun t : ℝ => (1 - t)⁻¹ - 1) from rfl, image_comp, himg0]
      ext x; simp only [mem_image, mem_Ioi, mem_Iio]
      constructor
      · rintro ⟨u, h0, rfl⟩; linarith
      · intro h0; exact ⟨α - x, by linarith, by ring⟩
    exact cov_Ioo01 hd hinj himg (fun t ht => by
      rw [hg t ht, abs_neg, abs_of_pos (hpos t ht)]; ring) hint
  · simp only [↓reduceIte] at hg ⊢
    have hd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivWithinAt (fun t : ℝ => α + ((1 - t)⁻¹ - 1))
        (((1 - t) ^ 2)⁻¹) (Ioo 0 1) t := fun t ht => (hu t ht).const_add α
    have hinj : InjOn (fun t : ℝ => α + ((1 - t)⁻¹ - 1)) (Ioo 0 1) := by
      intro x hx y hy hxy
      exact hmono.injOn hx hy (by simpa using hxy)
    have himg : (fun t : ℝ => α + ((1 - t)⁻¹ - 1)) '' Ioo 0 1 = Ioi α := by
      rw [show (fun t : ℝ => α + ((1 - t)⁻¹ - 1)) =
        (fun u => α + u) ∘ (fun t : ℝ => (1 - t)⁻¹ - 1) from rfl, image_comp, himg0]
      ext x; simp only [mem_image, mem_Ioi]
      constructor
      · rintro ⟨u, h0, rfl⟩; linarith
      · intro h0; exact ⟨x - α, by linarith, by ring⟩
    exact cov_Ioo01 hd hinj himg (fun t ht => by
      rw [hg t ht, abs_of_pos (hpos t ht)]; ring) hint


/-! ### Pointwise semantics of the transformed integrands -/

theorem shift_real0 (a : Expr) (xs : List ℝ) (t : ℝ) :
    (a.shift xs.length 1).real (xs ++ [t]) = a.real xs := by
  simpa using (shift_sound a (L1 := xs) rfl t []).1

theorem var_real0 (xs : List ℝ) (t : ℝ) : (NExpr.var xs.length).real (xs ++ [t]) = t := by
  simp [NExpr.real]

theorem replace_sound0 (e u : Expr) (xs : List ℝ) (t c : ℝ) (hu : u.real (xs ++ [t]) = c) :
    (e.replace xs.length u).real (xs ++ [t]) = e.real (xs ++ [c]) ∧
      ((e.replace xs.length u).Converges (xs ++ [t]) → e.Converges (xs ++ [c])) := by
  have h := replace_sound e (i := xs.length) (E0 := xs ++ [t]) (by simp) c u []
    (fun L' hL' => by
      have : L' = [] := List.eq_nil_of_length_eq_zero (by simpa using hL')
      subst this; simpa using hu)
  simpa using h

theorem affineE_sound (xs : List ℝ) (a b f : Expr) (t : ℝ) :
    (simplify (mul (sub (b.shift xs.length 1) (a.shift xs.length 1))
      (f.replace xs.length (add (a.shift xs.length 1)
        (mul (sub (b.shift xs.length 1) (a.shift xs.length 1)) (NExpr.var xs.length)))))).real
        (xs ++ [t]) =
      (b.real xs - a.real xs) * f.real (xs ++ [a.real xs + (b.real xs - a.real xs) * t]) ∧
    ((simplify (mul (sub (b.shift xs.length 1) (a.shift xs.length 1))
      (f.replace xs.length (add (a.shift xs.length 1)
        (mul (sub (b.shift xs.length 1) (a.shift xs.length 1)) (NExpr.var xs.length)))))).Converges
        (xs ++ [t]) →
      f.Converges (xs ++ [a.real xs + (b.real xs - a.real xs) * t])) := by
  have hw : (sub (b.shift xs.length 1) (a.shift xs.length 1)).real (xs ++ [t]) =
      b.real xs - a.real xs := by
    rw [sub_real, shift_real0, shift_real0]
  have hr := replace_sound0 f (add (a.shift xs.length 1)
    (mul (sub (b.shift xs.length 1) (a.shift xs.length 1)) (NExpr.var xs.length))) xs t
    (a.real xs + (b.real xs - a.real xs) * t)
    (by rw [add_real, mul_real, hw, shift_real0, var_real0])
  have hs := simplify_sound (mul (sub (b.shift xs.length 1) (a.shift xs.length 1))
      (f.replace xs.length (add (a.shift xs.length 1)
        (mul (sub (b.shift xs.length 1) (a.shift xs.length 1)) (NExpr.var xs.length))))) (xs ++ [t])
  refine ⟨?_, fun h => ?_⟩
  · rw [hs.1, mul_real, hw, hr.1]
  · rw [hs.2, mul_converges] at h
    exact hr.2 h.2

theorem affine_sem (xs : List ℝ) (a b f : Expr) (t : ℝ) :
    (transformed xs.length .affine a b f).real (xs ++ [t]) =
      (b.real xs - a.real xs) * f.real (xs ++ [a.real xs + (b.real xs - a.real xs) * t]) ∧
    ((transformed xs.length .affine a b f).Converges (xs ++ [t]) →
      f.Converges (xs ++ [a.real xs + (b.real xs - a.real xs) * t])) := by
  simp only [transformed]
  exact affineE_sound xs a b f t

theorem power_sem (xs : List ℝ) (a b f : Expr) (m : Nat) (right : Bool) {t : ℝ}
    (ht : t ∈ Ioo (0:ℝ) 1) :
    (transformed xs.length (.power m right) a b f).real (xs ++ [t]) =
      m * t ^ (m - 1) * ((b.real xs - a.real xs) *
        f.real (xs ++ [a.real xs + (b.real xs - a.real xs) *
          (if right then 1 - t ^ m else t ^ m)])) ∧
    ((transformed xs.length (.power m right) a b f).Converges (xs ++ [t]) →
      f.Converges (xs ++ [a.real xs + (b.real xs - a.real xs) *
          (if right then 1 - t ^ m else t ^ m)])) := by
  simp only [transformed]
  have hl : (xs ++ [t])[xs.length]? = some t := by simp
  have hm : (if right then sub (NExpr.rat 1) (pow (NExpr.var xs.length) m)
      else pow (NExpr.var xs.length) m).real (xs ++ [t]) =
      (if right then 1 - t ^ m else t ^ m) := by
    split
    · rw [sub_real, pow_real, var_real0]; simp [NExpr.real]
    · rw [pow_real, var_real0]
  obtain ⟨hE1, hE2⟩ := affineE_sound xs a b f (if right then 1 - t ^ m else t ^ m)
  have hr := replace_sound0 (simplify (mul (sub (b.shift xs.length 1) (a.shift xs.length 1))
      (f.replace xs.length (add (a.shift xs.length 1)
        (mul (sub (b.shift xs.length 1) (a.shift xs.length 1)) (NExpr.var xs.length))))))
    _ xs t _ hm
  have hreg := regularize_sound ht.1 hl (mul (mul (NExpr.rat m) (pow (NExpr.var xs.length) (m - 1)))
    ((simplify (mul (sub (b.shift xs.length 1) (a.shift xs.length 1))
      (f.replace xs.length (add (a.shift xs.length 1)
        (mul (sub (b.shift xs.length 1) (a.shift xs.length 1)) (NExpr.var xs.length)))))).replace
      xs.length (if right then sub (NExpr.rat 1) (pow (NExpr.var xs.length) m)
      else pow (NExpr.var xs.length) m)))
  refine ⟨?_, fun h => ?_⟩
  · rw [hreg.1, mul_real, mul_real, pow_real, var_real0, hr.1, hE1]
    simp [NExpr.real]
  · have h' := hreg.2 h
    rw [mul_converges] at h'
    exact hE2 (hr.2 h'.2)

theorem tail_sem (xs : List ℝ) (a b f : Expr) (how : Change)
    (hhow : how = .right ∨ how = .left) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    (transformed xs.length how a b f).real (xs ++ [t]) =
      f.real (xs ++ [if how == .right then a.real xs + ((1 - t)⁻¹ - 1)
        else a.real xs - ((1 - t)⁻¹ - 1)]) / (1 - t) ^ 2 ∧
    ((transformed xs.length how a b f).Converges (xs ++ [t]) →
      f.Converges (xs ++ [if how == .right then a.real xs + ((1 - t)⁻¹ - 1)
        else a.real xs - ((1 - t)⁻¹ - 1)])) := by
  have htr : transformed xs.length how a b f =
      (let t := NExpr.var xs.length
      let d := sub (.rat 1) t
      let u := sub (.unary .inv d) (.rat 1)
      let A := a.shift xs.length 1
      let y := if how == .right then add A u else sub A u
      let E := simplify (div (f.replace xs.length y) (pow d 2))
      let atRight := simplify (E.replace xs.length (sub (.rat 1) t))
      simplify ((regularize xs.length atRight).replace xs.length (sub (.rat 1) t))) := by
    rcases hhow with rfl | rfl <;> rfl
  rw [htr]
  simp only
  set n := xs.length
  set d := sub (NExpr.rat 1) (NExpr.var n)
  set A := a.shift n 1
  set y := if how == .right then add A (sub (.unary .inv d) (.rat 1))
    else sub A (sub (.unary .inv d) (.rat 1)) with hy
  set E := simplify (div (f.replace n y) (pow d 2))
  have hd : ∀ s, d.real (xs ++ [s]) = 1 - s := by
    intro s; rw [sub_real, var_real0]; simp [NExpr.real]
  have hyv : ∀ s, y.real (xs ++ [s]) = (if how == .right then a.real xs + ((1 - s)⁻¹ - 1)
      else a.real xs - ((1 - s)⁻¹ - 1)) := by
    intro s
    rw [hy]; split
    · rw [add_real, sub_real, shift_real0]; simp [NExpr.real, Unary.real, hd]
    · rw [sub_real, sub_real, shift_real0]; simp [NExpr.real, Unary.real, hd]
  have hEs : ∀ s, E.real (xs ++ [s]) = f.real (xs ++ [if how == .right then
        a.real xs + ((1 - s)⁻¹ - 1) else a.real xs - ((1 - s)⁻¹ - 1)]) / (1 - s) ^ 2 ∧
      (E.Converges (xs ++ [s]) → f.Converges (xs ++ [if how == .right then
        a.real xs + ((1 - s)⁻¹ - 1) else a.real xs - ((1 - s)⁻¹ - 1)])) := by
    intro s
    have hs := simplify_sound (div (f.replace n y) (pow d 2)) (xs ++ [s])
    have hr := replace_sound0 f y xs s _ (hyv s)
    refine ⟨?_, fun h => ?_⟩
    · rw [hs.1, div_real, pow_real, hd, hr.1]
    · rw [hs.2, div_converges] at h
      exact hr.2 h.1
  have h1t : 0 < 1 - t := by linarith [ht.2]
  have hl : (xs ++ [1 - t])[n]? = some (1 - t) := by simp [n]
  have hsub : ∀ s, (sub (NExpr.rat 1) (NExpr.var n)).real (xs ++ [s]) = 1 - s := hd
  have hr2 := replace_sound0 E (sub (NExpr.rat 1) (NExpr.var n)) xs (1 - t) _ (hsub (1 - t))
  have hs2 := simplify_sound (E.replace n (sub (NExpr.rat 1) (NExpr.var n))) (xs ++ [1 - t])
  have hreg := regularize_sound h1t hl (simplify (E.replace n (sub (NExpr.rat 1) (NExpr.var n))))
  have hr1 := replace_sound0 (regularize n (simplify (E.replace n (sub (NExpr.rat 1)
    (NExpr.var n))))) (sub (NExpr.rat 1) (NExpr.var n)) xs t _ (hsub t)
  have hs1 := simplify_sound ((regularize n (simplify (E.replace n (sub (NExpr.rat 1)
    (NExpr.var n))))).replace n (sub (NExpr.rat 1) (NExpr.var n))) (xs ++ [t])
  rw [sub_sub_cancel] at hr2
  refine ⟨?_, fun h => ?_⟩
  · rw [hs1.1, hr1.1, hreg.1, hs2.1, hr2.1, (hEs t).1]
  · exact (hEs t).2 (hr2.2 (hs2.2.1 (hreg.2 (hr1.2 (hs1.2.1 h)))))



theorem affine_surj {α β x : ℝ} (hx : x ∈ uIoo α β) :
    ∃ s ∈ Ioo (0:ℝ) 1, α + (β - α) * s = x := by
  rcases lt_trichotomy α β with h | h | h
  · rw [uIoo_of_le h.le] at hx
    refine ⟨(x - α) / (β - α), ⟨div_pos (by linarith [hx.1]) (by linarith), ?_⟩, ?_⟩
    · rw [div_lt_one (by linarith)]; linarith [hx.2]
    · field_simp; ring
  · subst h; simp at hx
  · rw [uIoo_of_ge h.le] at hx
    refine ⟨(α - x) / (α - β), ⟨div_pos (by linarith [hx.2]) (by linarith), ?_⟩, ?_⟩
    · rw [div_lt_one (by linarith)]; linarith [hx.1]
    · field_simp; ring

theorem power_surj {m : ℕ} (hm : 0 < m) (right : Bool) {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    ∃ t ∈ Ioo (0:ℝ) 1, (if right then 1 - t ^ m else t ^ m) = s := by
  have key : ∀ r ∈ Ioo (0:ℝ) 1, ∃ t ∈ Ioo (0:ℝ) 1, t ^ m = r := by
    intro r hr
    refine ⟨r ^ ((m:ℝ)⁻¹), ⟨Real.rpow_pos_of_pos hr.1 _,
      Real.rpow_lt_one hr.1.le hr.2 (by positivity)⟩, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.1.le, inv_mul_cancel₀ (by positivity),
      Real.rpow_one]
  cases right
  · simpa using key s hs
  · obtain ⟨t, ht, h⟩ := key (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    exact ⟨t, ht, by simp [h]⟩

theorem tail_surj (right : Bool) {α x : ℝ} (hx : x ∈ (if right then Ioi α else Iio α)) :
    ∃ t ∈ Ioo (0:ℝ) 1,
      (if right then α + ((1 - t)⁻¹ - 1) else α - ((1 - t)⁻¹ - 1)) = x := by
  have key : ∀ u : ℝ, 0 < u → ∃ t ∈ Ioo (0:ℝ) 1, (1 - t)⁻¹ - 1 = u := by
    intro u hu
    refine ⟨u / (1 + u), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one (by linarith)]; linarith
    · have : 1 - u / (1 + u) = (1 + u)⁻¹ := by field_simp; ring
      rw [this, inv_inv]; ring
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte, mem_Iio] at hx ⊢
    obtain ⟨t, ht, h⟩ := key (α - x) (by linarith)
    exact ⟨t, ht, by rw [h]; ring⟩
  · simp only [↓reduceIte, mem_Ioi] at hx ⊢
    obtain ⟨t, ht, h⟩ := key (x - α) (by linarith)
    exact ⟨t, ht, by rw [h]; ring⟩

theorem finite_core {xs : List ℝ} {how : Change} {a b f : Expr}
    (hhow : how = .affine ∨ ∃ m r, how = .power m r ∧ 0 < m)
    (hint : IntegrableOn (fun t => (transformed xs.length how a b f).real (xs ++ [t])) (Ioo 0 1))
    (hconv : ∀ t ∈ Ioo (0:ℝ) 1, (transformed xs.length how a b f).Converges (xs ++ [t])) :
    IntervalIntegrable (fun x => f.real (xs ++ [x])) volume (a.real xs) (b.real xs) ∧
      ∫ x in (a.real xs)..(b.real xs), f.real (xs ++ [x]) =
        ∫ t in Ioo 0 1, (transformed xs.length how a b f).real (xs ++ [t]) ∧
      ∀ x ∈ uIoo (a.real xs) (b.real xs), f.Converges (xs ++ [x]) := by
  rcases hhow with rfl | ⟨m, r, rfl, hm⟩
  · obtain ⟨h1, h2⟩ := affine_interval (F := fun x => f.real (xs ++ [x]))
      (fun t _ => (affine_sem xs a b f t).1) hint
    refine ⟨h1, h2, fun x hx => ?_⟩
    obtain ⟨s, hs, rfl⟩ := affine_surj hx
    exact (affine_sem xs a b f s).2 (hconv s hs)
  · obtain ⟨hh1, hh2⟩ := power_transport hm r
      (h := fun s => (b.real xs - a.real xs) *
        f.real (xs ++ [a.real xs + (b.real xs - a.real xs) * s]))
      (fun t ht => (power_sem xs a b f m r ht).1) hint
    obtain ⟨h1, h2⟩ := affine_interval (F := fun x => f.real (xs ++ [x]))
      (fun t _ => rfl) hh1
    refine ⟨h1, h2.trans hh2, fun x hx => ?_⟩
    obtain ⟨s, hs, rfl⟩ := affine_surj hx
    obtain ⟨t, ht, hts⟩ := power_surj hm r hs
    have := (power_sem xs a b f m r ht).2 (hconv t ht)
    rwa [hts] at this



theorem tail_core {xs : List ℝ} {how : Change} {a b f : Expr} (right : Bool)
    (hhow : how = if right then .right else .left)
    (hint : IntegrableOn (fun t => (transformed xs.length how a b f).real (xs ++ [t])) (Ioo 0 1))
    (hconv : ∀ t ∈ Ioo (0:ℝ) 1, (transformed xs.length how a b f).Converges (xs ++ [t])) :
    IntegrableOn (fun x => f.real (xs ++ [x]))
        (if right then Ioi (a.real xs) else Iio (a.real xs)) ∧
      ∫ x in (if right then Ioi (a.real xs) else Iio (a.real xs)), f.real (xs ++ [x]) =
        ∫ t in Ioo 0 1, (transformed xs.length how a b f).real (xs ++ [t]) ∧
      ∀ x ∈ (if right then Ioi (a.real xs) else Iio (a.real xs)), f.Converges (xs ++ [x]) := by
  have hor : how = .right ∨ how = .left := by cases right <;> simp [hhow]
  have hb : (how == .right) = right := by cases right <;> subst hhow <;> rfl
  have hsem := fun t (ht : t ∈ Ioo (0:ℝ) 1) => tail_sem xs a b f how hor ht
  simp only [hb] at hsem
  obtain ⟨h1, h2⟩ := tail_transport right (F := fun x => f.real (xs ++ [x])) (α := a.real xs)
    (fun t ht => (hsem t ht).1) hint
  refine ⟨h1, h2, fun x hx => ?_⟩
  obtain ⟨t, ht, rfl⟩ := tail_surj right hx
  exact (hsem t ht).2 (hconv t ht)


end Lynth.Interval.Integral.Nested

