module

import all Lynth.Interval.Integral.Legendre

/-! Interval transport for the Legendre evaluator. -/
namespace Lynth.Interval.Integral
open Intgrl

theorem ival_segment_mem {X : Ival} {x y t : ℝ} (hx : x ∈ X) (hy : y ∈ X)
    (ht : t ∈ Set.uIcc x y) : t ∈ X :=
  ⟨fun l hl => (le_min (hx.1 l hl) (hy.1 l hl)).trans ht.1,
   fun u hu => ht.2.trans (max_le (hx.2 u hu) (hy.2 u hu))⟩

theorem polynomial_difference (P : Polynomial ℝ) (a b : ℝ) :
    ∃ t ∈ Set.uIcc a b, P.eval b - P.eval a = (b-a)*P.derivative.eval t := by
  have hpos : ∀ a b : ℝ, a < b →
      ∃ t ∈ Set.Ioo a b, P.eval b-P.eval a = (b-a)*P.derivative.eval t := by
    intro a b hab
    obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope P.eval P.derivative.eval hab
      P.continuous.continuousOn (fun x _ => P.hasDerivAt x)
    exact ⟨t,ht,by rw [he,mul_div_cancel₀ _ (sub_ne_zero.mpr hab.ne')]⟩
  rcases lt_trichotomy a b with hab | rfl | hba
  · obtain ⟨t,ht,he⟩ := hpos a b hab
    exact ⟨t,by simpa [Set.uIcc_of_le hab.le] using ⟨ht.1.le,ht.2.le⟩,he⟩
  · exact ⟨a,Set.left_mem_uIcc,by simp⟩
  · obtain ⟨t,ht,he⟩ := hpos b a hba
    exact ⟨t,by simpa [Set.uIcc_of_ge hba.le] using ⟨ht.1.le,ht.2.le⟩,by linarith⟩

theorem legendre_inner_constant : 4*Real.sqrt 2/Real.sqrt Real.pi ≤ (13:ℝ)/4 := by
  apply (div_le_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)).mpr
  apply le_of_sq_le_sq _ (by positivity)
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
    Real.sq_sqrt Real.pi_pos.le, Real.pi_gt_d2]

theorem secondBound_sound {p n : Nat} {X : Ival} {x : ℝ} (hx : x ∈ X)
    (habs : |x| < 1) : ∃ B : ℝ, B ∈ secondBound p n X ∧
      0 ≤ B ∧ |(legendre n).derivative.derivative.eval x| ≤ B := by
  let G : ℝ := ((n-1 : Nat) : ℝ)*n*(n+1)*(n+2)/8
  have hGmem : G ∈ Ival.ofRat p (((n-1 : Nat) : ℚ)*n*(n+1)*(n+2)/8) := by
    simpa [G] using Ival.mem_ofRat p (((n-1 : Nat) : ℚ)*n*(n+1)*(n+2)/8)
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [abs_lt] using habs
  have hG : |(legendre n).derivative.derivative.eval x| ≤ G := by
    have hb := (legendre_deriv_bounds n ⟨hxI.1.le,hxI.2.le⟩).2
    by_cases hn : n = 0
    · subst n; simpa [G] using hb
    · have he : ((n-1 : Nat) : ℝ) = (n : ℝ)-1 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      simpa only [G,he] using hb
  unfold secondBound
  dsimp only
  split
  · let D := 1-x^2
    have hD : 0 < D := by
      dsimp [D]
      have hp : 0 < (1-x)*(1+x) := mul_pos (by linarith [hxI.2]) (by linarith [hxI.1])
      nlinarith [hp]
    let B : ℝ := ((13:ℝ)*n/4)*Real.sqrt n / (D*Real.sqrt (Real.sqrt D))
    have hDmem := Ival.mem_sub (p := p) Ival.mem_one (Ival.mem_sq (p := p) hx)
    have hBmem : B ∈ Ival.div p
        (Ival.mul p (Ival.ofRat p ((13:ℚ)*n/4)) (Ival.sqrt p (Ival.ofRat p n)))
        (Ival.mul p (Ival.sub p Ival.one (Ival.sq p X))
          (Ival.sqrt p (Ival.sqrt p (Ival.sub p Ival.one (Ival.sq p X))))) := by
      have hnum : (13:ℝ)*n/4 ∈ Ival.ofRat p ((13:ℚ)*n/4) := by
        simpa using Ival.mem_ofRat p ((13:ℚ)*n/4)
      exact Ival.mem_div (Ival.mem_mul hnum (Ival.mem_sqrt (Ival.mem_ofRat p n)))
        (Ival.mem_mul hDmem (Ival.mem_sqrt (Ival.mem_sqrt hDmem)))
    have hB0 : 0 ≤ B := by dsimp [B]; positivity
    have hB : |(legendre n).derivative.derivative.eval x| ≤ B := by
      by_cases hn : n = 0
      · subst n; simpa [legendre] using hB0
      · have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
        have hnpow : (n:ℝ)^(3/2:ℝ) = (n:ℝ)*Real.sqrt n := by
          rw [show (3/2:ℝ) = 1+1/2 by norm_num, Real.rpow_add hn0,
            Real.rpow_one, ← Real.sqrt_eq_rpow]
        have hquarter : Real.sqrt (Real.sqrt D) = D^(1/4:ℝ) := by
          rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hD.le]
          norm_num
        have hDpow : D^(5/4:ℝ) = D*Real.sqrt (Real.sqrt D) := by
          rw [show (5/4:ℝ) = 1+1/4 by norm_num,Real.rpow_add hD,Real.rpow_one,hquarter]
        calc
          |(legendre n).derivative.derivative.eval x| ≤ 4*Real.sqrt 2/Real.sqrt Real.pi * ((n:ℝ)*Real.sqrt n) /
              (D*Real.sqrt (Real.sqrt D)) := by
            have hh := (legendre_deriv_interior_bounds n (by omega) hxI).2
            rw [hnpow,hDpow] at hh
            exact hh
          _ ≤ B := by
            have hh := mul_le_mul_of_nonneg_right legendre_inner_constant
              (show 0 ≤ (n:ℝ)*Real.sqrt n by positivity)
            apply div_le_div_of_nonneg_right _ (by positivity)
            convert hh using 1 <;> ring
    exact ⟨min G B,Ival.mem_min hGmem hBmem,le_min hG0 hB0,le_min hG hB⟩
  · exact ⟨G,hGmem,hG0,hG⟩

end Lynth.Interval.Integral
