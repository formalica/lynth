import Lynth.Interval.Integral.Legendre

/-! Interval realization of the large-degree Legendre expansion. -/
namespace Lynth.Interval.Integral
open Intgrl Fns
open scoped BigOperators

theorem asymp_phase_term (n k : Nat) (θ a : ℝ) (hs : Real.sin θ ≠ 0) :
    (Complex.exp (((((n:ℝ)+1/2)*θ-Real.pi/4 : ℝ) : ℂ)*Complex.I) *
      ((a:ℂ) * (⟨1,-(Real.cos θ/Real.sin θ)⟩ : ℂ)^k)).re =
      a*Real.cos (((n:ℝ)+k+1/2)*θ-((k:ℝ)+1/2)*Real.pi/2)/Real.sin θ^k := by
  have hsC : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hs
  have hu : (⟨1,-(Real.cos θ/Real.sin θ)⟩ : ℂ) =
      Complex.exp (((θ-Real.pi/2 : ℝ):ℂ)*Complex.I)/(Real.sin θ : ℂ) := by
    apply (eq_div_iff hsC).mpr
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, one_mul, mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re, Real.cos_sub_pi_div_two]
    · simp only [Complex.mul_im, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, Complex.exp_ofReal_mul_I_im, Real.sin_sub_pi_div_two]
      field_simp
  rw [hu,div_pow,← Complex.exp_nat_mul]
  have he : Complex.exp (((((n:ℝ)+1/2)*θ-Real.pi/4 : ℝ) : ℂ)*Complex.I) *
      Complex.exp ((k:ℂ)*(((θ-Real.pi/2 : ℝ):ℂ)*Complex.I)) =
      Complex.exp (((((n:ℝ)+k+1/2)*θ-((k:ℝ)+1/2)*Real.pi/2 : ℝ):ℂ)*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hp : Complex.exp (((((n:ℝ)+1/2)*θ-Real.pi/4 : ℝ) : ℂ)*Complex.I) *
      ((a:ℂ)*(Complex.exp ((k:ℂ)*(((θ-Real.pi/2 : ℝ):ℂ)*Complex.I))/(Real.sin θ:ℂ)^k)) =
      (a:ℂ)*Complex.exp (((((n:ℝ)+k+1/2)*θ-((k:ℝ)+1/2)*Real.pi/2 : ℝ):ℂ)*Complex.I) /
        (Real.sin θ:ℂ)^k := by rw [← he]; ring
  rw [hp]
  rw [← Complex.ofReal_pow, Complex.div_ofReal_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]

theorem asymp_fold_sound {c : Ctx} {n : Nat} {S c₀ : Ival} {step : CBox}
    {s : ℝ} {u : ℂ} (hs : s ∈ S) (h₀ : asympCoeff n 0 ∈ c₀) (hu : u ∈ step) :
    ∀ K : Nat,
    let (v,next,power) := (List.range K).foldl (fun (acc,coeff,power) k =>
      (CBox.add c.prec acc (CBox.mul c.prec (CBox.ofReal coeff) power),
       Ival.mul c.prec coeff (Ival.ofRat c.prec
         (((2*k+1 : Nat):ℚ)^2/(4*(k+1 : Nat)*(2*n+2*k+3 : Nat)))),
       CBox.mul c.prec power step)) (CBox.ofReal Ival.zero,c₀,CBox.ofReal Ival.one)
    (∑ k ∈ Finset.range K, (asympCoeff n k : ℂ)*u^k) ∈ v ∧
      asympCoeff n K ∈ next ∧ u^K ∈ power := by
  intro K
  induction K with
  | zero =>
    exact ⟨CBox.mem_ofReal Ival.mem_zero,h₀,CBox.mem_ofReal Ival.mem_one⟩
  | succ K ih =>
    rw [List.range_succ,List.foldl_append]
    rcases he : (List.range K).foldl (fun (acc,coeff,power) k =>
      (CBox.add c.prec acc (CBox.mul c.prec (CBox.ofReal coeff) power),
       Ival.mul c.prec coeff (Ival.ofRat c.prec
         (((2*k+1 : Nat):ℚ)^2/(4*(k+1 : Nat)*(2*n+2*k+3 : Nat)))),
       CBox.mul c.prec power step)) (CBox.ofReal Ival.zero,c₀,CBox.ofReal Ival.one)
      with ⟨v,next,power⟩
    rw [he] at ih ⊢
    change _ ∈ CBox.add c.prec v (CBox.mul c.prec (CBox.ofReal next) power) ∧
      _ ∈ Ival.mul c.prec next _ ∧ _ ∈ CBox.mul c.prec power step
    dsimp only at ih ⊢
    refine ⟨?_,?_,?_⟩
    · rw [Finset.sum_range_succ]
      exact CBox.mem_add ih.1 (CBox.mem_mul (CBox.mem_ofReal ih.2.1) ih.2.2)
    · rw [asympCoeff_succ]
      rw [mul_div_assoc]
      apply Ival.mem_mul ih.2.1
      convert Ival.mem_ofRat c.prec
        (((2*K+1 : Nat):ℚ)^2/(4*(K+1 : Nat)*(2*n+2*K+3 : Nat))) using 1 <;> push_cast <;> rfl
    · rw [pow_succ]
      exact CBox.mem_mul ih.2.2 hu

theorem asympValue_sound {c : Ctx} (hc : c.Valid) (n K : Nat)
    (hn : 0 < n) (hK : 0 < K) (x : Dy) (hx : |x.toReal| < 1) :
    (legendre n).eval x.toReal ∈ asympValue c n K x := by
  let θ := Real.pi/2-Real.arcsin x.toReal
  let s := Real.sqrt (1-x.toReal^2)
  let φ := ((n:ℝ)+1/2)*θ-Real.pi/4
  let u : ℂ := ⟨1,-(x.toReal/s)⟩
  let prefR := Real.sqrt (2/(Real.pi*s))
  let S := Ival.sqrt c.prec (Ival.sub c.prec Ival.one (Ival.sq c.prec (Ival.pt x)))
  let theta := Ival.sub c.prec (Ival.divNat c.prec c.pi 2) (asinIval c (Ival.pt x))
  let phase := Ival.sub c.prec (Ival.mul c.prec (Ival.ofRat c.prec ((n:ℚ)+1/2)) theta)
    (Ival.divNat c.prec c.pi 4)
  let phaseBox : CBox := ⟨cosIval c phase,sinIval c phase⟩
  let step : CBox := ⟨Ival.one,Ival.neg (Ival.div c.prec (Ival.pt x) S)⟩
  let c₀ := Ival.div c.prec (Ival.pt ⟨1,(2*n:Nat)⟩)
    (Ival.mul c.prec (Ival.sqrt c.prec c.pi)
      (Ival.mul c.prec (Ival.ofRat c.prec ((n:ℚ)+1/2))
        (Ival.pt (Dy.ofNat ((2*n).choose n)))))
  let pref := Ival.sqrt c.prec (Ival.div c.prec (Ival.ofRat c.prec 2)
    (Ival.mul c.prec c.pi S))
  have hx' := abs_lt.mp hx
  have hθ0 : 0 < θ := by
    have := Real.arcsin_lt_pi_div_two.mpr hx'.2
    dsimp [θ]; linarith
  have hθπ : θ < Real.pi := by
    have := Real.neg_pi_div_two_lt_arcsin.mpr hx'.1
    dsimp [θ]; linarith
  have hcos : Real.cos θ = x.toReal := by
    rw [Real.cos_pi_div_two_sub,Real.sin_arcsin hx'.1.le hx'.2.le]
  have hsin : Real.sin θ = s := by
    rw [Real.sin_pi_div_two_sub,Real.cos_arcsin]
  have hs0 : 0 < s := hsin ▸ Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hS : s ∈ S := Ival.mem_sqrt (Ival.mem_sub Ival.mem_one (Ival.mem_sq (Ival.mem_pt x)))
  have htheta : θ ∈ theta := Ival.mem_sub
    (Ival.mem_divNat hc.pi_mem (by norm_num)) (mem_asinIval hc (Ival.mem_pt x))
  have hhalf : ((n:ℝ)+1/2) ∈ Ival.ofRat c.prec ((n:ℚ)+1/2) := by
    simpa using Ival.mem_ofRat c.prec ((n:ℚ)+1/2)
  have hphase : φ ∈ phase := Ival.mem_sub (Ival.mem_mul hhalf htheta)
    (Ival.mem_divNat hc.pi_mem (by norm_num))
  have hphaseBox : Complex.exp ((φ:ℂ)*Complex.I) ∈ phaseBox := by
    exact ⟨by simpa only [Complex.exp_ofReal_mul_I_re] using mem_cosIval hc hphase,
      by simpa only [Complex.exp_ofReal_mul_I_im] using mem_sinIval hc hphase⟩
  have hstep : u ∈ step := ⟨Ival.mem_one,Ival.mem_neg (Ival.mem_div (Ival.mem_pt x) hS)⟩
  have hc₀ : asympCoeff n 0 ∈ c₀ := by
    rw [asympCoeff_zero]
    have hnum : (4:ℝ)^n ∈ Ival.pt (⟨1,(2*n:Nat)⟩ : Dy) := by
      convert Ival.mem_pt (⟨1,(2*n:Nat)⟩ : Dy) using 1
      simp only [Dy.toReal_def,Dy.toRat_mk,Rat.cast_mul,Rat.cast_intCast,Int.cast_one,
        one_mul,Rat.cast_zpow,Rat.cast_ofNat]
      rw [zpow_natCast,pow_mul]
      norm_num
    have hchoose : ((2*n).choose n : ℝ) ∈ Ival.pt (Dy.ofNat ((2*n).choose n)) := by
      simpa [Dy.toReal_def] using Ival.mem_pt (Dy.ofNat ((2*n).choose n))
    have hd := Ival.mem_mul (p := c.prec) (Ival.mem_sqrt (p := c.prec) hc.pi_mem)
      (Ival.mem_mul (p := c.prec) hhalf hchoose)
    rw [← mul_assoc] at hd
    exact Ival.mem_div hnum hd
  have hpref : prefR ∈ pref := Ival.mem_sqrt (Ival.mem_div
    (by simpa using Ival.mem_ofRat c.prec 2) (Ival.mem_mul hc.pi_mem hS))
  rcases he : (List.range K).foldl (fun (acc,coeff,power) k =>
        (CBox.add c.prec acc (CBox.mul c.prec (CBox.ofReal coeff) power),
         Ival.mul c.prec coeff (Ival.ofRat c.prec
           (((2*k+1:Nat):ℚ)^2/(4*(k+1:Nat)*(2*n+2*k+3:Nat)))),
         CBox.mul c.prec power step)) (CBox.ofReal Ival.zero,c₀,CBox.ofReal Ival.one) with ⟨v,next,power⟩
  have hf := asymp_fold_sound (c := c) hS hc₀ hstep K
  rw [he] at hf
  dsimp only at hf
  let mainR := prefR*(Complex.exp ((φ:ℂ)*Complex.I)*
    (∑ k ∈ Finset.range K,(asympCoeff n k:ℂ)*u^k)).re
  let main := Ival.mul c.prec pref (CBox.mul c.prec phaseBox v).re
  let tailR := 2*(prefR*(asympCoeff n K/s^K))
  let tail := Ival.mul c.prec (Ival.ofRat c.prec 2)
    (Ival.mul c.prec pref (Ival.div c.prec next (Ival.npow c.prec S K)))
  have hmain : mainR ∈ main := Ival.mem_mul hpref (CBox.mem_mul hphaseBox hf.1).1
  have htail : tailR ∈ tail := Ival.mem_mul
    (by simpa using Ival.mem_ofRat c.prec 2)
    (Ival.mem_mul hpref (Ival.mem_div hf.2.1 (Ival.mem_npow hS K)))
  have hmainEq : mainR = prefR*∑ k ∈ Finset.range K,
      asympCoeff n k*Real.cos (((n:ℝ)+k+1/2)*θ-((k:ℝ)+1/2)*Real.pi/2)/s^k := by
    dsimp only [mainR]
    congr 1
    rw [Finset.mul_sum,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simpa only [φ,u,hcos,hsin] using asymp_phase_term n k θ (asympCoeff n k) (hsin ▸ hs0.ne')
  have herr : |(legendre n).eval x.toReal-mainR| ≤ tailR := by
    have hh := legendre_asymptotic n K hn hK hθ0 hθπ
    rw [hcos,hsin,← hmainEq] at hh
    convert hh using 1 <;> dsimp only [tailR,prefR] <;> ring
  change (legendre n).eval x.toReal ∈ _
  unfold asympValue
  dsimp only
  rw [he]
  change (legendre n).eval x.toReal ∈ (match tail.hi with | some e => Ival.widen c.prec main e | none => Ival.top)
  cases ht : tail.hi with
  | none => exact Ival.mem_top _
  | some err => exact Ival.mem_widen hmain (herr.trans (htail.2 err ht))

end Lynth.Interval.Integral
