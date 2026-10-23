module

import all Lynth.Interval.Integral.Legendre

/-! Exact integer coefficient generation for the endpoint expansion. -/
namespace Lynth.Interval.Integral

def oneCoefficient (n k : Nat) : Int := (n.choose k : Int) * ((n+k).choose k : Int)

theorem oneCoefficient_step (n k : Nat) :
    (oneCoefficient n k * (n-k : Nat) * (n+k+1 : Nat)).tdiv ((k+1 : Nat)^2) =
      oneCoefficient n (k+1) := by
  have h₁ := Nat.choose_succ_right_eq n k
  have h₂ := Nat.add_one_mul_choose_eq (n+k) k
  have hrec : (n.choose (k+1) * (n+k+1).choose (k+1)) * (k+1)^2 =
      (n.choose k * (n+k).choose k) * (n-k) * (n+k+1) := by
    calc
      _ = (n.choose (k+1)*(k+1))*((n+k+1).choose (k+1)*(k+1)) := by ring
      _ = (n.choose k*(n-k))*((n+k+1)*(n+k).choose k) := by rw [h₁,← h₂]
      _ = _ := by ring
  have hr : oneCoefficient n (k+1) * ((k+1 : Nat)^2 : Nat) =
      oneCoefficient n k * (n-k : Nat) * (n+k+1 : Nat) := by
    dsimp only [oneCoefficient]
    exact_mod_cast hrec
  rw [← hr]
  exact Int.mul_tdiv_cancel _ (by positivity)

theorem oneCoeffs_eq (n : Nat) : oneCoeffs n =
    ((List.range (n+1)).map (oneCoefficient n)).toArray := by
  let step := fun (s : Int × Array Int) (k : Nat) =>
    let a := (s.1*(n-k : Nat)*(n+k+1 : Nat)).tdiv ((k+1 : Nat)^2)
    (a,s.2.push a)
  have hloop : ∀ k : Nat, (List.range k).foldl step (1,#[1]) =
      (oneCoefficient n k,((List.range (k+1)).map (oneCoefficient n)).toArray) := by
    intro k
    induction k with
    | zero => simp [oneCoefficient]
    | succ k ih =>
      rw [List.range_succ,List.foldl_append,ih]
      simp only [List.foldl_cons,List.foldl_nil,step,oneCoefficient_step]
      congr 1
      rw [List.push_toArray]
      congr 1
      conv_rhs => rw [List.range_succ,List.map_append]
      simp
  unfold oneCoeffs
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range',List.forIn_pure_yield_eq_foldl]
  simpa [step,Std.Legacy.Range.size,← List.range_eq_range',Id.run,pure,bind] using
    congrArg Prod.snd (hloop n)


def zeroCoefficient (n j : Nat) : Int :=
  (-1:Int)^(n/2-j) * (n.choose (n/2-j) : Int) * ((n+2*j+n%2).choose (2*j+n%2) : Int)

theorem zeroMagnitude_step {n k d : Nat} (hn : 2*k+d = n) (hk : 0 < k) :
    (n.choose (k-1)*(n+d+2).choose (d+2))*((d+1)*(d+2)) =
      (n.choose k*(n+d).choose d)*(n-d)*(n+d+1) := by
  have h₁ : n.choose k*k = n.choose (k-1)*(n-k+1) := by
    simpa only [show k-1+1 = k by omega,show n-(k-1) = n-k+1 by omega] using
      Nat.choose_succ_right_eq n (k-1)
  have h₂ := Nat.add_one_mul_choose_eq (n+d) d
  have h₃ := Nat.add_one_mul_choose_eq (n+d+1) (d+1)
  calc
    _ = n.choose (k-1)*((n+d+2).choose (d+2)*(d+2))*(d+1) := by ring
    _ = n.choose (k-1)*((n+d+2)*(n+d+1).choose (d+1))*(d+1) := by rw [← h₃]
    _ = n.choose (k-1)*(n+d+2)*((n+d+1).choose (d+1)*(d+1)) := by ring
    _ = n.choose (k-1)*(n+d+2)*((n+d+1)*(n+d).choose d) := by rw [← h₂]
    _ = (n.choose (k-1)*(n-k+1))*2*(n+d+1)*(n+d).choose d := by
      rw [show n+d+2 = 2*(n-k+1) by omega]
      ring
    _ = (n.choose k*k)*2*(n+d+1)*(n+d).choose d := by rw [← h₁]
    _ = _ := by rw [show n-d = 2*k by omega]; ring

theorem zeroCoefficient_step {n j : Nat} (hj : j < n/2) :
    (-zeroCoefficient n j * (n-(2*j+n%2) : Nat) * (n+(2*j+n%2)+1 : Nat)).tdiv
      (((2*j+n%2+1)*(2*j+n%2+2) : Nat) : Int) = zeroCoefficient n (j+1) := by
  let k := n/2-j
  let d := 2*j+n%2
  have hk : 0 < k := by dsimp [k]; omega
  have hn : 2*k+d = n := by dsimp [k,d]; omega
  have hrec : (n.choose (k-1) : Int)*((n+d+2).choose (d+2) : Int)*
      (((d+1)*(d+2) : Nat) : Int) =
      (n.choose k : Int)*((n+d).choose d : Int)*(n-d : Nat)*(n+d+1 : Nat) := by
    exact_mod_cast zeroMagnitude_step hn hk
  have hsign : (-1:Int)^(k-1) = -((-1:Int)^k) := by
    conv_rhs => rw [show k = k-1+1 by omega,pow_succ]
    ring
  have hnext : zeroCoefficient n (j+1) =
      (-1:Int)^(k-1)*(n.choose (k-1) : Int)*((n+d+2).choose (d+2) : Int) := by
    simp only [zeroCoefficient,show n/2-(j+1) = k-1 by dsimp [k]; omega,
      show 2*(j+1)+n%2 = d+2 by dsimp [d]; omega,
      show n+2*(j+1)+n%2 = n+d+2 by dsimp [d]; omega]
  have hnum : -zeroCoefficient n j*(n-d : Nat)*(n+d+1 : Nat) =
      zeroCoefficient n (j+1)*(((d+1)*(d+2) : Nat) : Int) := by
    have hcur : zeroCoefficient n j =
        (-1:Int)^k*(n.choose k : Int)*((n+d).choose d : Int) := by
      simp only [zeroCoefficient,k,d,Nat.add_assoc]
    rw [hcur,hnext,hsign]
    change -((-1:Int)^k*(n.choose k : Int)*((n+d).choose d : Int)) *
      (n-d : Nat)*(n+d+1 : Nat) = _
    linear_combination ((-1:Int)^k)*hrec
  change (-zeroCoefficient n j*(n-d : Nat)*(n+d+1 : Nat)).tdiv _ = _
  rw [hnum]
  exact Int.mul_tdiv_cancel _ (by positivity)

theorem zeroCoefficient_initial (n : Nat) :
    (if (n/2)%2 == 1 then
      -((n.choose (n/2) : Int) * (if n%2 == 0 then 1 else (n+1 : Nat))) else
      (n.choose (n/2) : Int) * (if n%2 == 0 then 1 else (n+1 : Nat))) = zeroCoefficient n 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with ho | ho <;>
    rcases Nat.mod_two_eq_zero_or_one (n/2) with hs | hs <;>
    simp [zeroCoefficient,ho,hs,neg_one_pow_eq_pow_mod_two]

theorem zeroCoeffs_eq (n : Nat) : zeroCoeffs n =
    ((List.range (n/2+1)).map (zeroCoefficient n)).toArray := by
  let step := fun (s : Int × Array Int) (j : Nat) =>
    let d := 2*j+n%2
    let a := (-s.1*(n-d : Nat)*(n+d+1 : Nat)).tdiv (((d+1)*(d+2) : Nat) : Int)
    (a,s.2.push a)
  have hloop : ∀ k : Nat, k ≤ n/2 →
      (List.range k).foldl step (zeroCoefficient n 0,#[zeroCoefficient n 0]) =
        (zeroCoefficient n k,((List.range (k+1)).map (zeroCoefficient n)).toArray) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ,List.foldl_append,ih (by omega)]
      simp only [List.foldl_cons,List.foldl_nil,step,zeroCoefficient_step (by omega : k < n/2)]
      congr 1
      rw [List.push_toArray]
      congr 1
      conv_rhs => rw [List.range_succ,List.map_append]
      simp
  unfold zeroCoeffs
  dsimp only
  split <;> rename_i hsign
  all_goals
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',List.forIn_pure_yield_eq_foldl]
    have hi := zeroCoefficient_initial n
    simp only [hsign,↓reduceIte] at hi
    have hres := congrArg Prod.snd (hloop (n/2) le_rfl)
    rw [← hi] at hres
    simpa [step,Std.Legacy.Range.size,← List.range_eq_range',Id.run,pure,bind] using hres

end Lynth.Interval.Integral
