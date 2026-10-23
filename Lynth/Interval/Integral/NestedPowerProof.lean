module

import all Lynth.Interval.Integral.NestedSemantics
import all Lynth.Interval.Integral.Math.NestedAnalysis

/-! Endpoint power extraction preserves values and recursive convergence. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl

theorem positive_rpow_factor {t : ℝ} (ht : 0 < t) (p r : ℚ) :
    t^(p:ℝ) = t^(r:ℝ)*t^((p-r:ℚ):ℝ) := by
  rw [Rat.cast_sub,← Real.rpow_add ht]
  congr 1
  ring

theorem collectPower_semantics (level : Nat) (e : Expr) (xs : List ℝ)
    (ht : 0 < xs[level]?.getD 0) :
    e.real xs = xs[level]?.getD 0^((collectPower level e).1:ℝ)*
      (collectPower level e).2.real xs ∧
      ((collectPower level e).2.Converges xs ↔ e.Converges xs) := by
  induction e with
  | var i =>
    simp only [collectPower]
    split
    · rename_i he
      have hi : i = level := by simpa using he
      subst i
      simp [NExpr.real,NExpr.Converges]
    · simp [NExpr.real,NExpr.Converges]
  | rat | pi | rpow | integral => simp [collectPower]
  | unary op a ih =>
    rcases ha : collectPower level a with ⟨p,A⟩
    rw [ha] at ih
    dsimp only at ih
    cases op <;> simp only [collectPower,ha,Rat.cast_zero,Real.rpow_zero,one_mul,and_true]
    case neg =>
      constructor
      · simp only [NExpr.real,Unary.real,neg_real]
        rw [ih.1]
        ring
      · exact (neg_converges A xs).trans ih.2
    case inv =>
      constructor
      · simp only [NExpr.real,Unary.real,Rat.cast_neg,Real.rpow_neg ht.le]
        rw [ih.1,mul_inv_rev,mul_comm]
      · exact ih.2
    case sqrt =>
      constructor
      · simp only [NExpr.real,Unary.real,Rat.cast_div,Rat.cast_ofNat]
        rw [ih.1,sqrt_power_factor ht]
      · exact ih.2
  | binary op a b iha ihb =>
    rcases ha : collectPower level a with ⟨p,A⟩
    rcases hb : collectPower level b with ⟨q,B⟩
    rw [ha] at iha
    rw [hb] at ihb
    dsimp only at iha ihb
    cases op <;> simp only [collectPower,ha,hb,beq_iff_eq,reduceCtorEq,↓reduceIte,
      Rat.cast_zero,Real.rpow_zero,one_mul,and_true]
    case add =>
      constructor
      · simp only [add_real,mul_real,rpow_real,NExpr.real,Binary.real]
        rw [iha.1,ihb.1,positive_rpow_factor ht p (min p q),
          positive_rpow_factor ht q (min p q)]
        ring
      · simpa only [add_converges,mul_converges,rpow_converges,NExpr.Converges,true_and]
          using and_congr iha.2 ihb.2
    case sub =>
      constructor
      · simp only [sub_real,mul_real,rpow_real,NExpr.real,Binary.real]
        rw [iha.1,ihb.1,positive_rpow_factor ht p (min p q),
          positive_rpow_factor ht q (min p q)]
        ring
      · simpa only [sub_converges,mul_converges,rpow_converges,NExpr.Converges,true_and]
          using and_congr iha.2 ihb.2
    case mul =>
      constructor
      · simp only [mul_real,NExpr.real,Binary.real,Rat.cast_add,Real.rpow_add ht]
        rw [iha.1,ihb.1]
        ring
      · simpa only [mul_converges,NExpr.Converges] using and_congr iha.2 ihb.2
    case div =>
      constructor
      · simp only [div_real,NExpr.real,Binary.real,Rat.cast_sub,Real.rpow_sub ht]
        rw [iha.1,ihb.1,mul_div_mul_comm]
      · simpa only [div_converges,NExpr.Converges] using and_congr iha.2 ihb.2
  | pow a n ih =>
    rcases ha : collectPower level a with ⟨p,A⟩
    rw [ha] at ih
    dsimp only at ih
    simp only [collectPower,ha]
    constructor
    · simp only [pow_real,NExpr.real,Rat.cast_mul,Rat.cast_natCast,
        Real.rpow_mul_natCast ht.le]
      rw [ih.1,mul_pow]
    · exact (pow_converges A n xs).trans ih.2

theorem regularize_semantics (level : Nat) (e : Expr) (xs : List ℝ)
    (ht : 0 < xs[level]?.getD 0) :
    (regularize level e).real xs = e.real xs ∧
      ((regularize level e).Converges xs ↔ e.Converges xs) := by
  have hs := simplify_semantics e
  have hp := collectPower_semantics level (simplify e) xs ht
  unfold regularize
  rw [(simplify_semantics _).1,(simplify_semantics _).2]
  constructor
  · simp only [mul_real,rpow_real,NExpr.real]
    rw [← hp.1,hs.1]
  · simpa only [mul_converges,rpow_converges,NExpr.Converges,true_and,hs.2] using hp.2

end Lynth.Interval.Integral.Nested
