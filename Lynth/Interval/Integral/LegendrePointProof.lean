module

import all Lynth.Interval.Integral.LegendreFixedProof
import all Lynth.Interval.Integral.LegendreSeriesProof
import all Lynth.Interval.Integral.LegendreAsymptoticProof

/-! Soundness of the hybrid point evaluator, including reflection parity. -/
namespace Lynth.Interval.Integral
open Intgrl Fns

theorem legendre_derivative_quotient (n : Nat) (hn : 0 < n) {x : ℝ} (hx : |x| < 1) :
    (legendre n).derivative.eval x =
      (n:ℝ)*((legendre (n-1)).eval x-x*(legendre n).eval x)/(1-x^2) := by
  have hd := legendre_deriv_identity (n-1) x
  have he : n-1+1 = n := by omega
  rw [he] at hd
  have hc : ((n-1:Nat):ℝ)+1 = (n:ℝ) := by exact_mod_cast he
  rw [hc] at hd
  have hx' := abs_lt.mp hx
  have hpos : 0 < 1-x^2 := by nlinarith
  apply (eq_div_iff hpos.ne').mpr
  nlinarith [hd]

theorem pointPairNonneg_sound {c : Ctx} (hc : c.Valid) (n : Nat) {x : Dy}
    (hx0 : 0 ≤ x.toReal) (hx1 : x.toReal < 1) :
    (legendre n).eval x.toReal ∈ (pointPairNonneg c n x).1 ∧
      (legendre n).derivative.eval x.toReal ∈ (pointPairNonneg c n x).2 := by
  have hx : |x.toReal| < 1 := by rwa [abs_of_nonneg hx0]
  unfold pointPairNonneg
  simp only [beq_iff_eq]
  by_cases hn : n = 0
  · subst n
    simp only [↓reduceIte,Id.run,pure]
    simpa [legendre] using And.intro Ival.mem_one Ival.mem_zero
  simp only [hn,↓reduceIte]
  split
  · exact oneValue_sound _ n x
  · have hn0 : 0 < n := by omega
    let vv : Ival × Ival :=
        if n > 256 && c.prec < n/2 then
          (asympValue c (n-1) (min n (c.prec/2+12)) x,
           asympValue c n (min n (c.prec/2+12)) x)
        else if c.prec > 1024 || Dy.ltB x (Dy.ofRatD 64 (1/20)) then
          (zeroValue (c.prec+2*n+16) (n-1) x,zeroValue (c.prec+2*n+16) n x)
        else fixedValue (c.prec+2*Nat.log2 (n+2)+16) n x
    have hvals : (legendre (n-1)).eval x.toReal ∈ vv.1 ∧
        (legendre n).eval x.toReal ∈ vv.2 := by
      dsimp only [vv]
      split_ifs with hh hz
      · have hlarge : 256 < n := by simpa using (Bool.and_eq_true_iff.mp hh).1
        have hk : 0 < min n (c.prec/2+12) := lt_min hn0 (by omega)
        exact ⟨asympValue_sound hc (n-1) _ (by omega) hk x hx,
          asympValue_sound hc n _ hn0 hk x hx⟩
      · exact ⟨zeroValue_sound _ _ _,zeroValue_sound _ _ _⟩
      · exact ⟨(fixedValue_sound _ n hx0 hx1.le).1 hn0,
          (fixedValue_sound _ n hx0 hx1.le).2⟩
    change (legendre n).eval x.toReal ∈ vv.2 ∧
      (legendre n).derivative.eval x.toReal ∈
        Ival.div c.prec
          (Ival.mul c.prec (Ival.ofRat c.prec n)
            (Ival.sub c.prec vv.1 (Ival.mul c.prec (Ival.pt x) vv.2)))
          (Ival.sub c.prec Ival.one (Ival.sq c.prec (Ival.pt x)))
    refine ⟨hvals.2,?_⟩
    rw [legendre_derivative_quotient n hn0 hx]
    exact Ival.mem_div (Ival.mem_mul (by simpa using Ival.mem_ofRat c.prec n)
      (Ival.mem_sub hvals.1 (Ival.mem_mul (Ival.mem_pt x) hvals.2)))
      (Ival.mem_sub Ival.mem_one (Ival.mem_sq (Ival.mem_pt x)))

theorem legendre_derivative_parity (n : Nat) (x : ℝ) :
    (legendre n).derivative.eval (-x) = -((-1:ℝ)^n*(legendre n).derivative.eval x) := by
  have h₁ : HasDerivAt (fun y : ℝ => (legendre n).eval (-y))
      (-(legendre n).derivative.eval (-x)) x := by
    simpa only [Function.comp_def,mul_neg_one] using
      ((legendre n).hasDerivAt (-x)).comp x ((hasDerivAt_id x).neg)
  have h₂ : HasDerivAt (fun y : ℝ => (legendre n).eval (-y))
      ((-1:ℝ)^n*(legendre n).derivative.eval x) x := by
    simpa only [legendre_parity] using ((legendre n).hasDerivAt x).const_mul ((-1:ℝ)^n)
  linarith [h₁.unique h₂]

theorem pointPair_sound_impl {c : Ctx} (hc : c.Valid) (n : Nat) {x : Dy}
    (hx : |x.toReal| < 1) :
    (legendre n).eval x.toReal ∈ (pointPair c n x).1 ∧
      (legendre n).derivative.eval x.toReal ∈ (pointPair c n x).2 := by
  unfold pointPair
  split
  · rename_i hneg
    have hxneg : x.toReal < 0 := by
      change (x.toRat:ℝ) < 0
      exact_mod_cast (Dy.toRat_neg_iff x).mpr hneg
    have hn0 : 0 ≤ x.neg.toReal := by simpa [Dy.toReal_def] using (neg_pos.mpr hxneg).le
    have hn1 : x.neg.toReal < 1 := by
      simp only [Dy.toReal_def,Dy.toRat_neg']
      have := (abs_lt.mp hx).1
      change -1 < (x.toRat:ℝ) at this
      push_cast
      linarith
    have hh := pointPairNonneg_sound hc n hn0 hn1
    have he : x.toReal = -x.neg.toReal := by simp [Dy.toReal_def]
    rw [he,legendre_parity,legendre_derivative_parity]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · simp only [neg_one_pow_eq_pow_mod_two,hn,pow_zero,beq_self_eq_true,↓reduceIte,one_mul]
      exact ⟨hh.1,Ival.mem_neg hh.2⟩
    · simp only [neg_one_pow_eq_pow_mod_two,hn,pow_one,beq_self_eq_true,↓reduceIte,neg_one_mul,neg_neg]
      exact ⟨Ival.mem_neg hh.1,hh.2⟩
  · rename_i hnonneg
    have hx0 : 0 ≤ x.toReal := by
      change (0:ℝ) ≤ (x.toRat:ℝ)
      exact_mod_cast (Dy.toRat_nonneg_iff x).mpr (by omega)
    exact pointPairNonneg_sound hc n hx0 (abs_lt.mp hx).2

end Lynth.Interval.Integral
