import Mathlib

/-!
P1: generic root certification. This file is entirely standalone.
Existence comes from a checked sign bracket. Interval Newton subsequently
preserves an existing root; it must not be used as an unchecked existence claim.
-/

noncomputable section

namespace Intgrl

theorem root_bracket {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hsign : f a * f b < 0)
    (hnonzero : ∀ t ∈ Set.Icc a b, f' t ≠ 0) :
    ∃! r, r ∈ Set.Icc a b ∧ f r = 0 := by
  have hcont : ContinuousOn f (Set.Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  obtain ⟨r, hr, hr0⟩ : ∃ r ∈ Set.Icc a b, f r = 0 := by
    rcases lt_or_gt_of_ne (show f a ≠ 0 by intro h; simp [h] at hsign) with ha | ha
    · have hb : 0 < f b := by nlinarith
      exact intermediate_value_Icc hab.le hcont ⟨ha.le, hb.le⟩
    · have hb : f b < 0 := by nlinarith
      exact intermediate_value_Icc' hab.le hcont ⟨hb.le, ha.le⟩
  refine ⟨r, ⟨hr, hr0⟩, ?_⟩
  rintro s ⟨hs, hs0⟩
  by_contra hne
  have key : ∀ u v, u ∈ Set.Icc a b → v ∈ Set.Icc a b → u < v → f u = 0 → f v = 0 → False := by
    intro u v hu hv huv hu0 hv0
    obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero huv
      (fun t ht => (hf t ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩).continuousAt.continuousWithinAt)
      (by rw [hu0, hv0])
      (fun t ht => hf t ⟨hu.1.trans ht.1.le, ht.2.le.trans hv.2⟩)
    exact hnonzero c ⟨hu.1.trans hc.1.le, hc.2.le.trans hv.2⟩ hc0
  rcases lt_or_gt_of_ne hne with h | h
  · exact key s r hs hr h hs0 hr0
  · exact key r s hr hs h hr0 hs0

theorem interval_newton_preserves_root {f f' : ℝ → ℝ} {a b m r dl du : ℝ}
    (hab : a ≤ b) (hm : m ∈ Set.Icc a b) (hr : r ∈ Set.Icc a b)
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hroot : f r = 0)
    (hderiv : ∀ t ∈ Set.Icc a b, f' t ∈ Set.Icc dl du)
    (haway : 0 < dl ∨ du < 0) :
    ∃ d ∈ Set.Icc dl du, r = m - f m / d := by
  have hdne : ∀ d ∈ Set.Icc dl du, d ≠ 0 := by
    rintro d ⟨h1, h2⟩ rfl
    rcases haway with h | h <;> linarith
  -- mean value theorem between `r` and `m`
  have mvt : ∀ u v, u ∈ Set.Icc a b → v ∈ Set.Icc a b → u < v →
      ∃ c ∈ Set.Icc a b, f v - f u = f' c * (v - u) := by
    intro u v hu hv huv
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope f f' huv
      (fun t ht => (hf t ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩).continuousAt.continuousWithinAt)
      (fun t ht => hf t ⟨hu.1.trans ht.1.le, ht.2.le.trans hv.2⟩)
    refine ⟨c, ⟨hu.1.trans hc.1.le, hc.2.le.trans hv.2⟩, ?_⟩
    rw [hc']
    field_simp [sub_ne_zero.mpr huv.ne']
  rcases lt_trichotomy r m with h | h | h
  · obtain ⟨c, hc, hcv⟩ := mvt r m hr hm h
    refine ⟨f' c, hderiv c hc, ?_⟩
    have := hdne _ (hderiv c hc)
    rw [hroot, sub_zero] at hcv
    rw [hcv]
    field_simp
    ring
  · subst h
    refine ⟨f' a, hderiv a ⟨le_rfl, hab⟩, ?_⟩
    simp [hroot]
  · obtain ⟨c, hc, hcv⟩ := mvt m r hm hr h
    refine ⟨f' c, hderiv c hc, ?_⟩
    have := hdne _ (hderiv c hc)
    rw [hroot, zero_sub] at hcv
    have hfm : f m = - (f' c * (r - m)) := by linarith
    rw [hfm]
    field_simp
    ring

/-- Use this with a midpoint evaluation and a bound for the second derivative. -/
theorem deriv_enclosure_of_second_bound {f' f'' : ℝ → ℝ}
    {a b m t D : ℝ}
    (hm : m ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (hD : 0 ≤ D)
    (hsecond : ∀ u ∈ Set.Icc a b, HasDerivAt f' (f'' u) u)
    (hbound : ∀ u ∈ Set.Icc a b, |f'' u| ≤ D) :
    |f' t - f' m| ≤ D * |t - m| := by
  -- `hD` is part of the contract but is implied by `hbound` and not needed.
  have _hD : 0 ≤ D := hD
  have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f') (f' := f'') (C := D)
    (fun u hu => (hsecond u hu).hasDerivWithinAt)
    (fun u hu => by simpa [Real.norm_eq_abs] using hbound u hu) hm ht
  simpa [Real.norm_eq_abs] using this

end Intgrl
