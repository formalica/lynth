module

import all Lynth.Interval.Integral.LegendreBounds

/-! Input quantization and interval transport for the integer recurrence. -/
namespace Lynth.Interval.Integral
open Intgrl Fns

theorem atFixed_floor (p : Nat) {x : Dy} (hx : 0 ≤ x.toReal) :
    atFixed p x = Dy.floor (Dy.scale2 x p) := by
  change (0:ℝ) ≤ (x.toRat:ℝ) at hx
  have hm : 0 ≤ x.mantissa := (Dy.toRat_nonneg_iff x).mp (by exact_mod_cast hx)
  unfold atFixed Dy.floor Dy.scale2
  dsimp only
  split <;> simp_all [Int.tdiv_eq_ediv_of_nonneg hm,Int.shiftRight_eq_div_pow]

theorem atFixed_rounding (p : Nat) {x : Dy} (hx : 0 ≤ x.toReal) :
    let q := (atFixed p x : ℝ)/(2:ℝ)^p
    0 ≤ q ∧ q ≤ x.toReal ∧ |q-x.toReal| ≤ 1/(2:ℝ)^p := by
  have hval : (Dy.scale2 x p).toReal = x.toReal*(2:ℝ)^p := by simp [Dy.toReal_def]
  have hlo : (atFixed p x : ℝ) ≤ x.toReal*(2:ℝ)^p := by
    rw [atFixed_floor p hx]
    rw [← hval]
    change ((Dy.floor (Dy.scale2 x p) : Int) : ℝ) ≤ ((Dy.scale2 x p).toRat : ℝ)
    exact_mod_cast Dy.floor_le_toRat (Dy.scale2 x p)
  have hhi : x.toReal*(2:ℝ)^p < (atFixed p x : ℝ)+1 := by
    rw [atFixed_floor p hx,← hval]
    change ((Dy.scale2 x p).toRat : ℝ) < ((Dy.floor (Dy.scale2 x p) : Int) : ℝ)+1
    exact_mod_cast Dy.lt_floor_add_one_toRat (Dy.scale2 x p)
  have hq : 0 ≤ atFixed p x := by
    rw [atFixed_floor p hx,← Dy.floor_real]
    exact Int.floor_nonneg.mpr (by rw [hval]; positivity)
  have hscale : (0:ℝ) < 2^p := by positivity
  have hdown : (atFixed p x : ℝ)/(2:ℝ)^p ≤ x.toReal := (div_le_iff₀ hscale).mpr hlo
  refine ⟨by positivity,hdown,?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hdown)]
  apply (le_div_iff₀ hscale).mpr
  have hh : ((atFixed p x : ℝ)/(2:ℝ)^p)*(2:ℝ)^p = atFixed p x := div_mul_cancel₀ _ hscale.ne'
  nlinarith

theorem legendre_input_error {p n m : Nat} {x : Dy} (hx0 : 0 ≤ x.toReal) (hx1 : x.toReal ≤ 1)
    (hm : m ≤ n) :
    |(legendre m).eval ((atFixed p x : ℝ)/(2:ℝ)^p)-(legendre m).eval x.toReal| ≤
      (((n:ℝ)+1)*((n:ℝ)+2))/(2:ℝ)^p := by
  obtain ⟨hq0,hq1,herr⟩ := atFixed_rounding p hx0
  let q := (atFixed p x : ℝ)/(2:ℝ)^p
  obtain ⟨z,hz,he⟩ := polynomial_difference (legendre m) x.toReal q
  have hzI : z ∈ Set.Icc (-1:ℝ) 1 := by
    constructor
    · exact (le_min (by linarith : (-1:ℝ) ≤ x.toReal)
        (by change (-1:ℝ) ≤ (atFixed p x:ℝ)/(2:ℝ)^p; linarith)).trans hz.1
    · exact hz.2.trans (max_le hx1 (hq1.trans hx1))
  have hd := (legendre_deriv_bounds m hzI).1
  have hmn : (m:ℝ) ≤ n := by exact_mod_cast hm
  have hM : (m:ℝ)*((m:ℝ)+1)/2 ≤ ((n:ℝ)+1)*((n:ℝ)+2) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) n]
  rw [he,abs_mul]
  exact (mul_le_mul herr (hd.trans hM) (abs_nonneg _) (by positivity)).trans_eq (by ring)

theorem fixedValue_sound (p n : Nat) {x : Dy} (hx0 : 0 ≤ x.toReal) (hx1 : x.toReal ≤ 1) :
    (0 < n → (legendre (n-1)).eval x.toReal ∈ (fixedValue p n x).1) ∧
      (legendre n).eval x.toReal ∈ (fixedValue p n x).2 := by
  have hq := atFixed_rounding p hx0
  have hqabs : |(atFixed p x : ℝ)/(2:ℝ)^p| ≤ 1 := by
    rw [abs_of_nonneg hq.1]
    exact hq.2.1.trans hx1
  have hfixed := fixedPair_correct p n (atFixed p x) hqabs
  let err : Dy := ⟨(2*(n+1)*(n+2) : Nat),-(p:Int)⟩
  have he : err.toReal = 2*((n:ℝ)+1)*((n:ℝ)+2)/(2:ℝ)^p := by
    simp [err,Dy.toReal_def,div_eq_mul_inv]
  have hround : ∀ (m : Nat) (a : Int), m ≤ n →
      |(a:ℝ)/(2:ℝ)^p-(legendre m).eval ((atFixed p x : ℝ)/(2:ℝ)^p)| ≤
        (((n:ℝ)+1)*((n:ℝ)+2))/(2:ℝ)^p →
      (legendre m).eval x.toReal ∈ Ival.widen p (Ival.pt ⟨a,-(p:Int)⟩) err := by
    intro m a hm ha
    have hcenter : (a:ℝ)/(2:ℝ)^p ∈ Ival.pt (⟨a,-(p:Int)⟩ : Dy) := by
      simpa [Dy.toReal_def,div_eq_mul_inv] using Ival.mem_pt (⟨a,-(p:Int)⟩ : Dy)
    apply Ival.mem_widen hcenter
    rw [he]
    have hinput := legendre_input_error (p := p) hx0 hx1 hm
    have hh := (abs_sub_le ((legendre m).eval x.toReal)
      ((legendre m).eval ((atFixed p x : ℝ)/(2:ℝ)^p)) ((a:ℝ)/(2:ℝ)^p)).trans
      (add_le_add (by simpa only [abs_sub_comm] using hinput)
        (by simpa only [abs_sub_comm] using ha))
    convert hh using 1 <;> ring
  exact ⟨fun hn => hround (n-1) _ (by omega) (hfixed.2 hn),hround n _ le_rfl hfixed.1⟩

end Lynth.Interval.Integral
