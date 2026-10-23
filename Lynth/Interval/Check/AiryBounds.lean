module

import all Lynth.Interval.Check.AiryContext
import all Lynth.Interval.Check.AiryBernoulli

/-! Sound enclosures used to certify the Airy normalization constants. -/

namespace Lynth.Interval.AiryProof

open Fns

/-- Reflection avoids a second numerical Gamma evaluation. -/
theorem gamma_two_thirds_reflection :
    Real.Gamma (2 / 3) = (Real.pi / (Real.sqrt 3 / 2)) / Real.Gamma (1 / 3) := by
  apply (eq_div_iff (ne_of_gt (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)))).2
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 3 : ℝ)
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num,
    show Real.pi * (1 / 3 : ℝ) = Real.pi / 3 by ring, Real.sin_pi_div_three] at h
  simpa [mul_comm] using h

/-- Fixed Stirling parameters used only for the normalization certificate. -/
def gammaForNormalization (c : Ctx) (X : Ival) : Ival :=
  let w := c.prec + 16
  match X.lo with
  | none => Ival.top
  | some a =>
    let r := gammaShift a 1024
    let Z := Ival.add w X (Ival.pt (Dy.ofNat r))
    Ival.div w (expIval c (logGammaIval c w Z 108 (bernoulliList 216)))
      (risingIval w X r)

theorem mem_gammaForNormalization {c : Ctx} (hc : c.Valid) {X : Ival} {x : ℝ}
    (hx : x ∈ X) : Real.Gamma x ∈ gammaForNormalization c X := by
  unfold gammaForNormalization
  cases hlo : X.lo with
  | none => exact Ival.mem_top _
  | some a =>
    let w := c.prec + 16
    let r := gammaShift a 1024
    let Z := Ival.add w X (Ival.pt (Dy.ofNat r))
    have hshift := gammaShift_spec a 1024
    have hax := hx.1 a hlo
    have hz : 8 ≤ x + (r : ℝ) := by
      change (1024 : ℝ) ≤ a.toReal + (r : ℝ) at hshift
      linarith
    have hZ : x + (r : ℝ) ∈ Z := Ival.mem_add hx (Ival.mem_pt_nat r)
    have hlog := mem_logGammaIval (w := w) (N := 108) hc hZ hz (by norm_num)
    have hpos : 0 < Real.Gamma (x + (r : ℝ)) := Real.Gamma_pos_of_pos (by linarith)
    have hg : Real.Gamma (x + (r : ℝ)) ∈ expIval c (logGammaIval c w Z 108 (bernoulliList 216)) := by
      rw [← Real.exp_log hpos]
      exact mem_expIval c hlog
    rw [gamma_eq_gamma_add_div_rising x r]
    exact Ival.mem_div hg (mem_risingIval (w := w) hx r)

def rationalBounds (I : Ival) (lo hi : ℚ) : Bool :=
  match I.lo,I.hi with
  | some a,some b => decide (lo ≤ a.toRat) && decide (b.toRat ≤ hi)
  | _,_ => false

theorem rationalBounds_sound {I : Ival} {x : ℝ} {lo hi : ℚ}
    (hx : x ∈ I) (h : rationalBounds I lo hi = true) : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ) := by
  cases hl : I.lo with
  | none => simp [rationalBounds, hl] at h
  | some l =>
    cases hu : I.hi with
    | none => simp [rationalBounds, hl, hu] at h
    | some u =>
      have hh : lo ≤ l.toRat ∧ u.toRat ≤ hi := by simpa [rationalBounds, hl, hu] using h
      have hlo : (lo : ℝ) ≤ l.toReal := by
        change (lo : ℝ) ≤ (l.toRat : ℝ)
        exact_mod_cast hh.1
      have hhi : u.toReal ≤ (hi : ℝ) := by
        change (u.toRat : ℝ) ≤ (hi : ℝ)
        exact_mod_cast hh.2
      exact ⟨hlo.trans (hx.1 l hl), (hx.2 u hu).trans hhi⟩

end Lynth.Interval.AiryProof
