import Lynth.Interval.Num.Ival
import Lynth.Interval.Integral.Math.IntegralBounds

/-! Interval adapters for the portable integral enclosure theorems. -/

namespace Lynth.Interval.Integral

theorem integral_mem_mul {f : ℝ → ℝ} {a b : ℝ} {V L : Ival} {p : Nat}
    (hab : a ≤ b) (hm : Measurable f) (hfinite : V.isFinite = true)
    (hL : b - a ∈ L) (hV : ∀ x ∈ Set.Ioo a b, f x ∈ V)
    (hVne : ∃ v : ℝ, v ∈ V) :
    IntervalIntegrable f MeasureTheory.volume a b ∧
      (∫ x in a..b, f x) ∈ Ival.mul p L V := by
  cases hlo : V.lo with
  | none => simp [Ival.isFinite, hlo] at hfinite
  | some lo =>
    cases hhi : V.hi with
    | none => simp [Ival.isFinite, hhi] at hfinite
    | some hi =>
      have hv : ∀ x ∈ Set.Ioo a b, f x ∈ Set.Icc lo.toReal hi.toReal := by
        intro x hx
        exact ⟨(hV x hx).1 lo hlo, (hV x hx).2 hi hhi⟩
      have hh := Intgrl.direct_enclosure_open hab hm hv
      refine ⟨hh.1, ?_⟩
      by_cases hz : a = b
      · subst b
        have hzero : (0 : ℝ) ∈ L := by simpa using hL
        have hp := Ival.mem_mul (p := p) hzero hVne.choose_spec
        simpa using hp
      · have hpos : 0 < b-a := by
          have hlt : a < b := by
            by_contra hn
            exact hz (le_antisymm hab (le_of_not_gt hn))
          exact sub_pos.mpr hlt
        let v := (∫ x in a..b, f x) / (b-a)
        have hmean : v ∈ V := by
          simp only [Ival.mem_def, Ival.LoLe, Ival.LeHi, hlo, hhi,
            Option.some.injEq, forall_eq, v]
          constructor
          · rintro l rfl
            apply (le_div_iff₀ hpos).2
            simpa only [mul_comm] using hh.2.1
          · rintro h rfl
            apply (div_le_iff₀ hpos).2
            simpa only [mul_comm] using hh.2.2
        have hp := Ival.mem_mul (p := p) hL hmean
        have heq : (b-a) * v = ∫ x in a..b, f x := by
          dsimp [v]
          field_simp [ne_of_gt hpos]
        rwa [heq] at hp

end Lynth.Interval.Integral
