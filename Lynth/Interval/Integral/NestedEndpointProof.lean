import Lynth.Interval.Integral.NestedPrimitiveProof

/-! The numerical power/log moment used by nested endpoint envelopes. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl Fns MeasureTheory
open scoped BigOperators

theorem endpointErrorBound_value {c : Ctx} (hc : c.Valid) {δ : Dy} {A : Scale} {R : Dy}
    (h : endpointErrorBound c δ A = some R) :
    -1 < A.power ∧ ∃ r, boxRadius c A.coeff = some r ∧
      r.toReal * δ.toReal^((A.power:ℝ)+1) *
        (∑ j ∈ Finset.range (A.logs+1),
          ((A.logs.factorial:ℝ)/j.factorial/((A.power:ℝ)+1)^(A.logs-j+1)) *
            (1-Real.log δ.toReal)^j) ≤ R.toReal := by
  unfold endpointErrorBound at h
  split at h
  · contradiction
  · rename_i hp
    have hp' : -1 < A.power := lt_of_not_ge hp
    cases hr : boxRadius c A.coeff with
    | none => simp [hr] at h
    | some r =>
      refine ⟨hp',r,rfl,?_⟩
      let k : ℚ := A.power+1
      let L := Ival.sub c.prec Ival.one (logIval c (Ival.pt δ))
      let T : Nat → Ival := fun j => Ival.mul c.prec
        (Ival.ofRat c.prec ((A.logs.factorial:ℚ)/j.factorial/k^(A.logs-j+1)))
        (Ival.npow c.prec L j)
      let v : Nat → ℝ := fun j =>
        ((A.logs.factorial:ℝ)/j.factorial/((A.power:ℝ)+1)^(A.logs-j+1)) *
          (1-Real.log δ.toReal)^j
      let S := (List.range (A.logs+1)).foldl (fun s j => Ival.add c.prec s (T j)) Ival.zero
      have hL : 1-Real.log δ.toReal ∈ L :=
        Ival.mem_sub Ival.mem_one (mem_logIval hc (Ival.mem_pt δ))
      have hT : ∀ j, v j ∈ T j := by
        intro j
        apply Ival.mem_mul (p := c.prec) _ (Ival.mem_npow hL j)
        convert Ival.mem_ofRat c.prec
          ((A.logs.factorial:ℚ)/j.factorial/k^(A.logs-j+1)) using 1
        all_goals
          simp only [k,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_add,Rat.cast_one]
      have hsum : ∀ K, (∑ j ∈ Finset.range K, v j) ∈
          (List.range K).foldl (fun s j => Ival.add c.prec s (T j)) Ival.zero := by
        intro K
        induction K with
        | zero => simpa using Ival.mem_zero
        | succ K ih =>
          rw [List.range_succ,List.foldl_append,Finset.sum_range_succ]
          exact Ival.mem_add ih (hT K)
      have hS : (∑ j ∈ Finset.range (A.logs+1), v j) ∈ S := hsum (A.logs+1)
      have hD : δ.toReal^((A.power:ℝ)+1) ∈
          rpowIval c (Ival.pt δ) (Ival.ofRat c.prec k) := by
        apply mem_rpowIval hc (Ival.mem_pt δ)
        simpa only [k,Rat.cast_add,Rat.cast_one] using Ival.mem_ofRat c.prec k
      have hvalue := Ival.mem_mul (p := c.prec) (Ival.mem_pt r)
        (Ival.mem_mul (p := c.prec) hD hS)
      have hhi : (Ival.mul c.prec (Ival.pt r)
          (Ival.mul c.prec (rpowIval c (Ival.pt δ) (Ival.ofRat c.prec k)) S)).hi = some R := by
        simp only [hr,bind,pure,Option.bind_some] at h
        simp only [Std.Legacy.Range.forIn_eq_forIn_range',
          Std.Legacy.Range.size,← List.range_eq_range',
          Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one] at h
        change ((forIn (List.range (A.logs+1)) Ival.zero
          (fun j s => pure (.yield (Ival.add c.prec s (T j)))) : Option Ival).bind
            fun s => (Ival.mul c.prec (Ival.pt r)
              (Ival.mul c.prec (rpowIval c (Ival.pt δ) (Ival.ofRat c.prec k)) s)).hi) = some R at h
        rw [List.forIn_pure_yield_eq_foldl] at h
        exact h
      have hb := hvalue.2 R hhi
      simpa only [v,mul_assoc] using hb

theorem endpointErrorBound_radius {c : Ctx} (hc : c.Valid) {δ : Dy} {A : Scale} {R : Dy}
    (h : endpointErrorBound c δ A = some R) {z : ℂ} (hz : z ∈ A.coeff) :
    -1 < A.power ∧ ∃ C : ℝ, 0 ≤ C ∧
      (∀ w ∈ A.coeff, ‖w‖ ≤ C) ∧
      C * δ.toReal^((A.power:ℝ)+1) *
        (∑ j ∈ Finset.range (A.logs+1),
          ((A.logs.factorial:ℝ)/j.factorial/((A.power:ℝ)+1)^(A.logs-j+1)) *
            (1-Real.log δ.toReal)^j) ≤ R.toReal := by
  obtain ⟨hp,r,hr,hbound⟩ := endpointErrorBound_value hc h
  have hnorm : ∀ w ∈ A.coeff, ‖w‖ ≤ r.toReal := by
    intro w hw
    exact (CBox.mem_norm (p := c.prec) hw).2 r hr
  exact ⟨hp,r.toReal,(norm_nonneg z).trans (hnorm z hz),hnorm,hbound⟩

/-- Exact meaning of a scaled coefficient box at a positive real endpoint
distance. Only the distinguished variable is real; coefficients may be complex. -/
def Scale.Mem (A : Scale) (t : ℝ) (z : ℂ) : Prop :=
  ∃ w ∈ A.coeff, z = ((t^(A.power:ℝ) * (1-Real.log t)^A.logs : ℝ) : ℂ) * w

theorem Scale.weight_nonneg (A : Scale) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ t^(A.power:ℝ) * (1-Real.log t)^A.logs := by
  have hl : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  exact mul_nonneg (Real.rpow_nonneg ht.le _) (pow_nonneg (by linarith) _)

theorem Scale.Mem.norm_le {A : Scale} {t C : ℝ} {z : ℂ}
    (h : A.Mem t z) (ht : 0 < t) (ht1 : t ≤ 1)
    (hC : ∀ w ∈ A.coeff, ‖w‖ ≤ C) :
    ‖z‖ ≤ C*t^(A.power:ℝ)*(1-Real.log t)^A.logs := by
  obtain ⟨w,hw,hz⟩ := h
  have hweight := A.weight_nonneg ht ht1
  calc
    ‖z‖ = (t^(A.power:ℝ)*(1-Real.log t)^A.logs)*‖w‖ := by
      rw [hz,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hweight]
    _ ≤ (t^(A.power:ℝ)*(1-Real.log t)^A.logs)*C :=
      mul_le_mul_of_nonneg_left (hC w hw) hweight
    _ = C*t^(A.power:ℝ)*(1-Real.log t)^A.logs := by ring

theorem endpointErrorBound_sound {c : Ctx} (hc : c.Valid) {δ : Dy} {A : Scale} {R : Dy}
    (h : endpointErrorBound c δ A = some R) (hδ : 0 < δ.toReal) (hδ1 : δ.toReal ≤ 1)
    {F : ℝ → ℂ} (hm : Measurable F)
    (hF : ∀ t ∈ Set.Ioo (0:ℝ) δ.toReal, A.Mem t (F t)) :
    IntegrableOn F (Set.Ioc 0 δ.toReal) ∧
      ‖∫ t in (0:ℝ)..δ.toReal, F t‖ ≤ R.toReal := by
  have ht : δ.toReal/2 ∈ Set.Ioo (0:ℝ) δ.toReal := ⟨by linarith,by linarith⟩
  obtain ⟨w,hw,_⟩ := hF (δ.toReal/2) ht
  obtain ⟨hp,C,hC,hbox,hbound⟩ := endpointErrorBound_radius hc h hw
  have hp' : (-1:ℝ) < (A.power:ℝ) := by exact_mod_cast hp
  have hpoint : ∀ t ∈ Set.Ioo (0:ℝ) δ.toReal,
      ‖F t‖ ≤ C*t^(A.power:ℝ)*(1-Real.log t)^A.logs := by
    intro t ht
    exact (hF t ht).norm_le ht.1 (ht.2.le.trans hδ1) hbox
  have hi := endpoint_remainder hp' hδ hδ1 hC hm hpoint
  exact ⟨hi.1,hi.2.trans hbound⟩

end Lynth.Interval.Integral.Nested
