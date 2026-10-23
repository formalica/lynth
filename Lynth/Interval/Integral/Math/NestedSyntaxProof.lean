module

import all Lynth.Interval.Integral.Math.NestedSyntax
import all Lynth.Interval.Integral.SyntaxEq

/-! Semantics of the pure expression simplifications. -/
namespace Intgrl
end Intgrl

namespace Lynth.Interval.Integral.Nested
open Intgrl

theorem converges_of_noIntegral {e : Expr} (h : e.hasIntegral = false) (xs : List ℝ) :
    e.Converges xs := by
  induction e with
  | var | rat | pi => trivial
  | unary op e ih | pow e n ih | rpow e q ih => exact ih h
  | binary op e f ihe ihf =>
    have hh := Bool.or_eq_false_iff.mp h
    exact ⟨ihe hh.1,ihf hh.2⟩
  | integral => simp [NExpr.hasIntegral] at h

theorem env_getD_eq_of_uses {e : Expr} {xs ys : List ℝ}
    (hl : xs.length = ys.length)
    (hu : ∀ i, e.uses i = true → xs[i]?.getD 0 = ys[i]?.getD 0) :
    e.real xs = e.real ys ∧ (e.Converges xs ↔ e.Converges ys) := by
  induction e generalizing xs ys with
  | var i => exact ⟨hu i (by simp [NExpr.uses]),Iff.rfl⟩
  | rat | pi => exact ⟨rfl,Iff.rfl⟩
  | unary op a ih | pow a n ih | rpow a q ih =>
    obtain ⟨he,hc⟩ := ih hl hu
    exact ⟨by simp only [NExpr.real,he],hc⟩
  | binary op a b iha ihb =>
    obtain ⟨ha,hca⟩ := iha hl (fun i hi => hu i (by simp [NExpr.uses,hi]))
    obtain ⟨hb,hcb⟩ := ihb hl (fun i hi => hu i (by simp [NExpr.uses,hi]))
    exact ⟨by simp only [NExpr.real,ha,hb],and_congr hca hcb⟩
  | integral k a b f iha ihb ihf =>
    obtain ⟨ha,hca⟩ := iha hl (fun i hi => hu i (by simp [NExpr.uses,hi]))
    obtain ⟨hb,hcb⟩ := ihb hl (fun i hi => hu i (by simp [NExpr.uses,hi]))
    have hf : ∀ x, f.real (xs++[x]) = f.real (ys++[x]) ∧
        (f.Converges (xs++[x]) ↔ f.Converges (ys++[x])) := by
      intro x
      apply ihf (by simp [hl])
      intro i hi
      by_cases hj : i < xs.length
      · have hj' : i < ys.length := hl ▸ hj
        simpa only [List.getElem?_append,hj,hj',↓reduceIte] using hu i (by simp [NExpr.uses,hi])
      · have hj' : ¬i < ys.length := hl ▸ hj
        simp [List.getElem?_append,hj',hl]
    have hval : (fun x => f.real (xs++[x])) = (fun x => f.real (ys++[x])) :=
      funext (fun x => (hf x).1)
    constructor
    · simp only [NExpr.real,ha,hb,hval]
    · simp only [NExpr.Converges,ha,hb,hval]
      exact and_congr hca (and_congr hcb (and_congr Iff.rfl
        (forall_congr' (fun x => forall_congr' (fun _ => (hf x).2)))))

theorem add_semantics (a b : Expr) (xs : List ℝ) :
    (add a b).real xs = a.real xs+b.real xs ∧
      ((add a b).Converges xs ↔ a.Converges xs ∧ b.Converges xs) := by
  fun_cases add a b <;> simp [add,NExpr.real,NExpr.Converges,Binary.real]

theorem neg_semantics (a : Expr) (xs : List ℝ) :
    (neg a).real xs = -a.real xs ∧
      ((neg a).Converges xs ↔ a.Converges xs) := by
  fun_cases neg a <;> simp [neg,NExpr.real,NExpr.Converges,Unary.real]

theorem neg_real (a : Expr) (xs : List ℝ) : (neg a).real xs = -a.real xs :=
  (neg_semantics a xs).1

theorem neg_converges (a : Expr) (xs : List ℝ) :
    (neg a).Converges xs ↔ a.Converges xs := (neg_semantics a xs).2

theorem div_semantics (a b : Expr) (xs : List ℝ) :
    (div a b).real xs = a.real xs/b.real xs ∧
      ((div a b).Converges xs ↔ a.Converges xs ∧ b.Converges xs) := by
  fun_cases div a b <;> simp [div,NExpr.real,NExpr.Converges,Binary.real]

theorem sub_real (a b : Expr) (xs : List ℝ) :
    (sub a b).real xs = a.real xs-b.real xs := by
  fun_cases sub a b <;>
    simp_all only [NExpr.real,Binary.real,beq_iff_eq,Rat.cast_zero,Rat.cast_sub,
      sub_zero,sub_self,Bool.and_eq_true,Bool.not_eq_true'] <;>
    (try rw [(neg_semantics _ _).1]) <;> norm_num at * <;> ring

theorem mul_real (a b : Expr) (xs : List ℝ) :
    (mul a b).real xs = a.real xs*b.real xs := by
  fun_cases mul a b <;> simp [mul,NExpr.real,Binary.real]

theorem pow_real (a : Expr) (n : Nat) (xs : List ℝ) :
    (pow a n).real xs = a.real xs^n := by
  fun_cases pow a n <;>
    simp_all only [NExpr.real,Unary.real,pow_zero,pow_one,beq_iff_eq,
      Bool.and_eq_true,Bool.not_eq_true',Rat.cast_one]
  all_goals try (rw [(neg_semantics _ _).1]; dsimp only [NExpr.real])
  all_goals rw [neg_pow,neg_one_pow_eq_pow_mod_two]
  all_goals
    rename_i hn
    rcases Nat.mod_two_eq_zero_or_one n with hm | hm <;> simp_all [hm]

theorem sub_converges (a b : Expr) (xs : List ℝ) :
    (sub a b).Converges xs ↔ a.Converges xs ∧ b.Converges xs := by
  have hp : ∀ e : Expr, e.hasIntegral = false → e.Converges xs :=
    fun _ h => converges_of_noIntegral h xs
  fun_cases sub a b <;>
    simp_all only [NExpr.Converges,beq_iff_eq,Bool.and_eq_true,Bool.not_eq_true',
      neg_converges,true_and,and_true,and_self]
  case case1 hh =>
    obtain ⟨rfl,hpure⟩ := hh
    simp [hp _ hpure]
  case case4 A B hh hself =>
    have hc : A.Converges xs := hh.1 ▸ hp a hh.2
    simp [hc]
  case case6 A B h0 hsub hh hself =>
    have hc : b.Converges xs := hh.1 ▸ hp A hh.2
    simp [hc]
  case case8 A B h0 hsub hh hself =>
    have hc : b.Converges xs := hh.1 ▸ hp A hh.2
    simp [hc]
  case case9 A B h0 hsub hab hh hself =>
    have hc : b.Converges xs := hh.1 ▸ hp B hh.2
    simp [hc]

theorem mul_converges (a b : Expr) (xs : List ℝ) :
    (mul a b).Converges xs ↔ a.Converges xs ∧ b.Converges xs := by
  have hp : ∀ e : Expr, e.hasIntegral = false → e.Converges xs :=
    fun _ h => converges_of_noIntegral h xs
  fun_cases mul a b <;>
    simp_all only [NExpr.Converges,Bool.not_eq_true',true_and,and_true,and_self]
  all_goals aesop (add safe forward hp)

theorem pow_converges (a : Expr) (n : Nat) (xs : List ℝ) :
    (pow a n).Converges xs ↔ a.Converges xs := by
  have hp : ∀ e : Expr, e.hasIntegral = false → e.Converges xs :=
    fun _ h => converges_of_noIntegral h xs
  fun_cases pow a n <;>
    simp_all only [NExpr.Converges,beq_iff_eq,Bool.and_eq_true,Bool.not_eq_true',
      neg_converges]
  all_goals aesop (add safe forward hp)

theorem rpow_semantics (a : Expr) (q : ℚ) (xs : List ℝ) :
    (rpow a q).real xs = a.real xs^(q:ℝ) ∧
      ((rpow a q).Converges xs ↔ a.Converges xs) := by
  unfold rpow
  split
  · rename_i hh
    have he : q = 0 ∧ a.hasIntegral = false := by simpa using hh
    have hc := converges_of_noIntegral he.2 xs
    simp [NExpr.real,NExpr.Converges,he.1,hc]
  · split
    · rename_i hh
      have he : q = 1 := by simpa using hh
      subst q
      simp [Real.rpow_one]
    · split
      · rename_i hh
        have he : q.den = 1 ∧ 0 ≤ q.num := by simpa using hh
        have hq : (q:ℝ) = (q.num.toNat:ℝ) := by
          rw [Rat.cast_def,he.1]
          simp only [Nat.cast_one,div_one]
          exact_mod_cast (Int.toNat_of_nonneg he.2).symm
        exact ⟨by rw [pow_real,hq,Real.rpow_natCast],pow_converges _ _ _⟩
      · exact ⟨rfl,Iff.rfl⟩

theorem add_real (a b : Expr) (xs : List ℝ) : (add a b).real xs = a.real xs+b.real xs :=
  (add_semantics a b xs).1

theorem add_converges (a b : Expr) (xs : List ℝ) :
    (add a b).Converges xs ↔ a.Converges xs ∧ b.Converges xs := (add_semantics a b xs).2

theorem div_real (a b : Expr) (xs : List ℝ) : (div a b).real xs = a.real xs/b.real xs :=
  (div_semantics a b xs).1

theorem div_converges (a b : Expr) (xs : List ℝ) :
    (div a b).Converges xs ↔ a.Converges xs ∧ b.Converges xs := (div_semantics a b xs).2

theorem rpow_real (a : Expr) (q : ℚ) (xs : List ℝ) : (rpow a q).real xs = a.real xs^(q:ℝ) :=
  (rpow_semantics a q xs).1

theorem rpow_converges (a : Expr) (q : ℚ) (xs : List ℝ) :
    (rpow a q).Converges xs ↔ a.Converges xs := (rpow_semantics a q xs).2

theorem simplify_semantics (e : Expr) :
    (simplify e).real = e.real ∧ (simplify e).Converges = e.Converges := by
  induction e with
  | var | rat | pi => exact ⟨rfl,rfl⟩
  | unary op a ih =>
    constructor
    · funext xs
      cases op <;> simp only [simplify,NExpr.real,neg_real,Unary.real,ih.1]
    · funext xs
      cases op <;> simp only [simplify,NExpr.Converges,neg_converges,ih.2]
  | binary op a b iha ihb =>
    constructor
    · funext xs
      cases op <;> simp only [simplify,NExpr.real,add_real,sub_real,mul_real,div_real,
        Binary.real,iha.1,ihb.1]
    · funext xs
      cases op <;> simp only [simplify,NExpr.Converges,add_converges,sub_converges,
        mul_converges,div_converges,iha.2,ihb.2]
  | pow a n ih =>
    constructor
    · funext xs
      simp only [simplify,pow_real,NExpr.real,ih.1]
    · funext xs
      simp only [simplify,pow_converges,NExpr.Converges,ih.2]
  | rpow a q ih =>
    constructor
    · funext xs
      simp only [simplify,rpow_real,NExpr.real,ih.1]
    · funext xs
      simp only [simplify,rpow_converges,NExpr.Converges,ih.2]
  | integral k a b f iha ihb ihf =>
    constructor
    · funext xs
      simp only [simplify,NExpr.real,iha.1,ihb.1,ihf.1]
    · funext xs
      simp only [simplify,NExpr.Converges,iha.1,ihb.1,ihf.1,iha.2,ihb.2,ihf.2]

end Lynth.Interval.Integral.Nested
