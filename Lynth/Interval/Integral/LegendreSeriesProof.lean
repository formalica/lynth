import Lynth.Interval.Integral.RectEvalProof
import Lynth.Interval.Integral.LegendreCoefficients

/-! Interval realizations of the polynomial expansions at zero and one. -/
namespace Lynth.Interval.Integral
open Intgrl
open scoped BigOperators

noncomputable def coefficientPolynomial (cs : Array Int) : Polynomial ℝ :=
  ∑ i ∈ Finset.range cs.size, Polynomial.monomial i (cs[i]! : ℝ)

theorem coefficientPolynomial_eval (cs : Array Int) (x : ℝ) :
    (coefficientPolynomial cs).eval x = ∑ i ∈ Finset.range cs.size, (cs[i]! : ℝ)*x^i := by
  simp [coefficientPolynomial,Polynomial.eval_finsetSum]

theorem coefficientPolynomial_coeff (cs : Array Int) (i : Nat) :
    (coefficientPolynomial cs).coeff i = if i < cs.size then (cs[i]! : ℝ) else 0 := by
  simp [coefficientPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]

theorem coefficientPolynomial_range (cs : Nat → Int) (n : Nat) (x : ℝ) :
    (coefficientPolynomial ((List.range n).map cs).toArray).eval x =
      ∑ i ∈ Finset.range n, (cs i : ℝ)*x^i := by
  rw [coefficientPolynomial_eval]
  simp only [List.size_toArray,List.length_map,List.length_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hib : i < ((List.range n).map cs).toArray.size := by simpa using hi
  rw [getElem!_pos (((List.range n).map cs).toArray) i hib]
  simp

theorem coefficientPolynomial_derivative (cs : Array Int) :
    coefficientPolynomial ((cs.extract 1 cs.size).mapIdx fun i (a : Int) => a*(i+1 : Nat)) =
      (coefficientPolynomial cs).derivative := by
  ext i
  by_cases hi : i+1 < cs.size
  · have hd : i < ((cs.extract 1 cs.size).mapIdx fun i (a : Int) => a*(i+1 : Nat)).size := by
      simp
      omega
    rw [coefficientPolynomial_coeff,Polynomial.coeff_derivative,coefficientPolynomial_coeff]
    simp only [hi,hd,↓reduceIte]
    rw [getElem!_pos ((cs.extract 1 cs.size).mapIdx fun i (a : Int) => a*(i+1 : Nat)) i hd,
      getElem!_pos cs (i+1) hi]
    simp [Array.getElem_mapIdx,Array.getElem_extract,add_comm,mul_comm]
  · have hd : ¬i < ((cs.extract 1 cs.size).mapIdx fun i (a : Int) => a*(i+1 : Nat)).size := by
      simp
      omega
    simp only [coefficientPolynomial_coeff,Polynomial.coeff_derivative,hi,hd,↓reduceIte,mul_zero,zero_mul]

theorem legendre_one_value (n : Nat) (x : ℝ) :
    (legendre n).eval x = (coefficientPolynomial (oneCoeffs n)).eval ((x-1)/2) := by
  rw [legendre_at_one,coefficientPolynomial_eval,oneCoeffs_eq]
  simp only [List.size_toArray,List.length_map,List.length_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hib : i < ((List.range (n+1)).map (oneCoefficient n)).toArray.size := by simpa using hi
  rw [getElem!_pos (((List.range (n+1)).map (oneCoefficient n)).toArray) i hib]
  simp [oneCoefficient,List.getElem_toArray,List.getElem_map,List.getElem_range]

theorem legendre_one_derivative (n : Nat) (x : ℝ) :
    (legendre n).derivative.eval x =
      (coefficientPolynomial (oneCoeffs n)).derivative.eval ((x-1)/2)/2 := by
  let Q := coefficientPolynomial (oneCoeffs n)
  have hq := (Q.hasDerivAt ((x-1)/2)).comp x (((hasDerivAt_id x).sub_const 1).div_const 2)
  have he : (fun y => Q.eval ((y-1)/2)) = (fun y => (legendre n).eval y) :=
    funext (fun y => (legendre_one_value n y).symm)
  simp only [Function.comp_def,id_eq] at hq
  rw [he] at hq
  simpa only [mul_one_div] using ((legendre n).hasDerivAt x).unique hq

theorem oneValue_sound (p n : Nat) (x : Dy) :
    (legendre n).eval x.toReal ∈ (oneValue p n x).1 ∧
      (legendre n).derivative.eval x.toReal ∈ (oneValue p n x).2 := by
  let U := Ival.divNat p (Ival.sub p (Ival.pt x) Ival.one) 2
  have hu : (x.toReal-1)/2 ∈ U :=
    Ival.mem_divNat (Ival.mem_sub (Ival.mem_pt x) Ival.mem_one) (by norm_num)
  have hv := rectEval_sound (p := p) hu (oneCoeffs n)
  have hd := rectEval_sound (p := p) hu
    (((oneCoeffs n).extract 1 (oneCoeffs n).size).mapIdx fun i (a : Int) => a*(i+1 : Nat))
  rw [← coefficientPolynomial_eval,← legendre_one_value] at hv
  rw [← coefficientPolynomial_eval,coefficientPolynomial_derivative] at hd
  refine ⟨hv,?_⟩
  rw [legendre_one_derivative]
  exact Ival.mem_divNat hd (by norm_num)

theorem zeroCoefficient_term (n j : Nat) (x : ℝ) (hj : j ≤ n/2) :
    (if n%2 == 1 then x else 1) * ((zeroCoefficient n j : ℝ)*(x^2)^j) =
      (-1:ℝ)^(n/2-j)*(n.choose (n/2-j) : ℝ)*((2*n-2*(n/2-j)).choose n : ℝ)*
        x^(n-2*(n/2-j)) := by
  have he : n-2*(n/2-j) = 2*j+n%2 := by omega
  have ht : 2*n-2*(n/2-j) = n+(2*j+n%2) := by omega
  have hc : (n+2*j+n%2).choose (2*j+n%2) = (2*n-2*(n/2-j)).choose n := by
    rw [ht]
    simpa only [Nat.add_assoc] using (Nat.choose_symm_add (a := n) (b := 2*j+n%2)).symm
  simp only [zeroCoefficient,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,
    Int.cast_natCast,hc,he]
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · simp [hn,pow_mul]
  · simp only [hn,beq_self_eq_true,↓reduceIte,pow_succ,pow_mul]
    ring

theorem legendre_zero_value (n : Nat) (x : ℝ) :
    (legendre n).eval x =
      ((if n%2 == 1 then x else 1)*(coefficientPolynomial (zeroCoeffs n)).eval (x^2))*
        ((2:ℝ)⁻¹)^n := by
  rw [zeroCoeffs_eq,coefficientPolynomial_range,Finset.mul_sum]
  have he : (∑ j ∈ Finset.range (n/2+1),
      (if n%2 == 1 then x else 1)*((zeroCoefficient n j : ℝ)*(x^2)^j)) =
      ∑ k ∈ Finset.range (n/2+1),
        (-1:ℝ)^k*(n.choose k : ℝ)*((2*n-2*k).choose n : ℝ)*x^(n-2*k) := by
    calc
      _ = ∑ j ∈ Finset.range (n/2+1),
          (-1:ℝ)^(n/2-j)*(n.choose (n/2-j) : ℝ)*((2*n-2*(n/2-j)).choose n : ℝ)*
            x^(n-2*(n/2-j)) :=
        Finset.sum_congr rfl (fun j hj => zeroCoefficient_term n j x (by simpa using hj))
      _ = _ := by
        simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect
          (fun k => (-1:ℝ)^k*(n.choose k : ℝ)*((2*n-2*k).choose n : ℝ)*x^(n-2*k)) (n/2+1)
  rw [he,legendre_at_zero]
  ring

theorem zeroValue_sound (p n : Nat) (x : Dy) :
    (legendre n).eval x.toReal ∈ zeroValue p n x := by
  have hv := rectEval_sound (p := p) (Ival.mem_sq (p := p) (Ival.mem_pt x)) (zeroCoeffs n)
  rw [← coefficientPolynomial_eval] at hv
  have hscale : ((2:ℝ)⁻¹)^n ∈ Ival.pt (⟨1,-(n:Int)⟩ : Dy) := by
    simpa [Dy.toReal_def] using Ival.mem_pt (⟨1,-(n:Int)⟩ : Dy)
  rw [legendre_zero_value]
  unfold zeroValue
  split
  · exact Ival.mem_mul (Ival.mem_mul (Ival.mem_pt x) hv) hscale
  · simpa only [↓reduceIte,one_mul] using Ival.mem_mul (p := p) hv hscale

end Lynth.Interval.Integral
