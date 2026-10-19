import Mathlib
import Lynth

/-!
Complex-valued Mathlib integrals over real variables. Each successful declaration
contains convergence and a complex norm error proof reconstructed by `lynth`.
Every per-declaration limit is ceil(105 * the measured #count_heartbeats / 100).
Numerical witnesses are also checked against independent reference values.
-/
namespace ComplexIntervalArith.Integrals
open MeasureTheory
set_option maxRecDepth 10000

set_option maxHeartbeats 27790 in -- measured: 26466; +5%
/-- NIntegrate item 4. -/
def circular : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => Complex.I*Complex.exp (Complex.I*(x:ℂ))/(Complex.exp (Complex.I*(x:ℂ))+1/2)) volume (0) (2*Real.pi) ∧
    ‖(∫ x in (0:ℝ)..(2*Real.pi), Complex.I*Complex.exp (Complex.I*(x:ℂ))/(Complex.exp (Complex.I*(x:ℂ))+1/2))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |circular.val.1 - (0/10^12 : ℚ)| < 1/10000
#guard |circular.val.2 - (6283185307180/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 30751 in -- measured: 29286; +5%
/-- NIntegrate item 5. -/
def logLog : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => Complex.log (Complex.log (x:ℂ))) volume (0) (1) ∧
    ‖(∫ x in (0:ℝ)..(1), Complex.log (Complex.log (x:ℂ)))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |logLog.val.1 - (-577215664902/10^12 : ℚ)| < 1/10000
#guard |logLog.val.2 - (3141592653590/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 15584 in -- measured: 14841; +5%
/-- NIntegrate item 6. -/
def sqrtLog : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => (Complex.log (x:ℂ))^(1/2:ℂ)) volume (0) (1) ∧
    ‖(∫ x in (0:ℝ)..(1), (Complex.log (x:ℂ))^(1/2:ℂ))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |sqrtLog.val.1 - (0/10^12 : ℚ)| < 1/10000
#guard |sqrtLog.val.2 - (886226925453/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 5774 in -- measured: 5499; +5%
/-- NIntegrate item 10. -/
def sqrtCut : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => (-1+(x:ℂ)*Complex.I)^(1/2:ℂ)) volume (-2) (3) ∧
    ‖(∫ x in (-2:ℝ)..(3), (-1+(x:ℂ)*Complex.I)^(1/2:ℂ))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |sqrtCut.val.1 - (2651340000000/10^12 : ℚ)| < 1/10000
#guard |sqrtCut.val.2 - (1358290000000/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 53031 in -- measured: 50505; +5%
/-- NIntegrate item 11. -/
def logCut : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => Complex.log (-3+(x:ℂ)*Complex.I)) volume (-2) (3) ∧
    ‖(∫ x in (-2:ℝ)..(3), Complex.log (-3+(x:ℂ)*Complex.I))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |logCut.val.1 - (6020710000000/10^12 : ℚ)| < 1/10000
#guard |logCut.val.2 - (2449540000000/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 4914 in -- measured: 4680; +5%
/-- NIntegrate item 13a. -/
def oscExp : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) volume (1) (10000) ∧
    ‖(∫ x in (1:ℝ)..(10000), Complex.exp ((x:ℂ)*Complex.I))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |oscExp.val.1 - (-1147087926078/10^12 : ℚ)| < 1/10000
#guard |oscExp.val.2 - (1492457673127/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 8525 in -- measured: 8119; +5%
/-- NIntegrate item 13b. -/
def oscPower : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => (2:ℂ)^((x:ℂ)*Complex.I)) volume (1) (10000) ∧
    ‖(∫ x in (1:ℝ)..(10000), (2:ℂ)^((x:ℂ)*Complex.I))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |oscPower.val.1 - (375744000000/10^12 : ℚ)| < 1/10000
#guard |oscPower.val.2 - (479159000000/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 15144 in -- measured: 14422; +5%
/-- NIntegrate item 15a. -/
def gaussianExp : {p : ℚ × ℚ //
    IntegrableOn (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)*Complex.exp (-(x:ℂ)^2)) (Set.Ioi (1)) volume ∧
    ‖(∫ x in Set.Ioi (1:ℝ), Complex.exp ((x:ℂ)*Complex.I)*Complex.exp (-(x:ℂ)^2))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |gaussianExp.val.1 - (34019900000/10^12 : ℚ)| < 1/10000
#guard |gaussianExp.val.2 - (129738000000/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 16064 in -- measured: 15299; +5%
/-- NIntegrate item 15b. -/
def gaussianPower : {p : ℚ × ℚ //
    IntegrableOn (fun x : ℝ => (2:ℂ)^((x:ℂ)*Complex.I)*Complex.exp (-(x:ℂ)^2)) (Set.Ioi (1)) volume ∧
    ‖(∫ x in Set.Ioi (1:ℝ), (2:ℂ)^((x:ℂ)*Complex.I)*Complex.exp (-(x:ℂ)^2))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |gaussianPower.val.1 - (83661700000/10^12 : ℚ)| < 1/10000
#guard |gaussianPower.val.2 - (108261000000/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 5573 in -- measured: 5307; +5%
/-- NIntegrate item 18a. -/
def doubleExp : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => ∫ y in (1:ℝ)..10000, Complex.exp (Complex.I*((x:ℂ)+(y:ℂ)))) volume (1) (10000) ∧
    ‖(∫ x in (1:ℝ)..(10000), ∫ y in (1:ℝ)..10000, Complex.exp (Complex.I*((x:ℂ)+(y:ℂ))))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |doubleExp.val.1 - (-911625000000/10^12 : ℚ)| < 1/10000
#guard |doubleExp.val.2 - (-3423950000000/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 774 in -- measured: 737; +5%
def linear : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => (x:ℂ)+Complex.I*x) volume 0 1 ∧
    ‖(∫ x in (0:ℝ)..1, (x:ℂ)+Complex.I*x)-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |linear.val.1 - (500000000000/10^12 : ℚ)| < 1/10000
#guard |linear.val.2 - (500000000000/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 9018 in -- measured: 8588; +5%
def triangle : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => ∫ y in (0:ℝ)..x, (x:ℂ)+y+Complex.I*((x:ℂ)-y)) volume 0 1 ∧
    ‖(∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..x, (x:ℂ)+y+Complex.I*((x:ℂ)-y))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |triangle.val.1 - (500000000000/10^12 : ℚ)| < 1/10000
#guard |triangle.val.2 - (166666666667/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 4727 in -- measured: 4501; +5%
def reverse : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) volume 1 0 ∧
    ‖(∫ x in (1:ℝ)..0, Complex.exp ((x:ℂ)*Complex.I))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |reverse.val.1 - (-841470984800/10^12 : ℚ)| < 1/10000
#guard |reverse.val.2 - (-459697694100/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 711 in -- measured: 677; +5%
def zeroWidth : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => ((x:ℂ)-1)⁻¹) volume 1 1 ∧
    ‖(∫ x in (1:ℝ)..1, ((x:ℂ)-1)⁻¹)-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |zeroWidth.val.1 - (0/10^12 : ℚ)| < 1/10000
#guard |zeroWidth.val.2 - (0/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 869 in -- measured: 827; +5%
def finiteSet : {p : ℚ × ℚ //
    IntegrableOn (fun x : ℝ => (x:ℂ)+Complex.I) (Set.Icc 0 1) volume ∧
    ‖(∫ x in Set.Icc (0:ℝ) 1, (x:ℂ)+Complex.I)-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |finiteSet.val.1 - (500000000000/10^12 : ℚ)| < 1/10000
#guard |finiteSet.val.2 - (1000000000000/10^12 : ℚ)| < 1/10000

set_option maxHeartbeats 22221 in -- measured: 21162; +5%
def wholeGaussian : {p : ℚ × ℚ //
    Integrable (fun x : ℝ => Complex.exp (-(x:ℂ)^2)*(1+Complex.I)) volume ∧
    ‖(∫ x : ℝ, Complex.exp (-(x:ℂ)^2)*(1+Complex.I))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |wholeGaussian.val.1 - (1772453850900/10^12 : ℚ)| < 1/10000
#guard |wholeGaussian.val.2 - (1772453850900/10^12 : ℚ)| < 1/10000

noncomputable def aliasValue : ℂ := ∫ x in (0:ℝ)..1, Complex.exp ((x:ℂ)*Complex.I)

set_option maxHeartbeats 4779 in -- measured: 4551; +5%
def aliasAnswer : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) volume 0 1 ∧
    ‖aliasValue-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

#guard |aliasAnswer.val.1 - (841470984800/10^12 : ℚ)| < 1/10000
#guard |aliasAnswer.val.2 - (459697694100/10^12 : ℚ)| < 1/10000

set_option lynth.interval.trust "kernel" in
set_option maxHeartbeats 485 in -- measured: 461; +5%
def kernelLinear : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => (x:ℂ)+Complex.I*x) volume 0 1 ∧
    ‖(∫ x in (0:ℝ)..1, (x:ℂ)+Complex.I*x)-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

/-- info: 'ComplexIntervalArith.Integrals.kernelLinear' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernelLinear

set_option maxHeartbeats 26 in -- measured: 24; +5%
theorem preservesInnerConvergence :
    (Intgrl.CParts.mul (.rat 0)
      (.integral .interval (.rat 0) (.rat 1) (.unary .inv (.var 0)))).hasIntegral = true := by
  decide

set_option maxHeartbeats 31 in -- measured: 29; +5%
theorem rejectsErasedPower :
    ¬ (Intgrl.CExpr.pow (.real
      (.integral .interval (.rat 0) (.rat 1) (.unary .inv (.var 0)))) 0).Supported := by
  decide

set_option maxHeartbeats 1163 in -- measured: 1107; +5%
/-- The reciprocal outside the principal square root has negative imaginary part. -/
def inverseOutside : {p : ℚ × ℚ //
    IntervalIntegrable (fun _x : ℝ => (((-1:ℂ)^(1/2:ℂ))⁻¹)) volume 0 1 ∧
    ‖(∫ _x in (0:ℝ)..1, (((-1:ℂ)^(1/2:ℂ))⁻¹))-
      ((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth
#guard inverseOutside.val = (0,-1)

set_option maxHeartbeats 932 in -- measured: 887; +5%
/-- The reciprocal inside the principal square root has positive imaginary part. -/
def inverseInside : {p : ℚ × ℚ //
    IntervalIntegrable (fun _x : ℝ => (((-1:ℂ)⁻¹)^(1/2:ℂ))) volume 0 1 ∧
    ‖(∫ _x in (0:ℝ)..1, (((-1:ℂ)⁻¹)^(1/2:ℂ)))-
      ((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth
#guard inverseInside.val = (0,1)

-- The current pure-imaginary logarithm projection has a reversed argument sign.
-- The theorem's safety condition must reject it through every enclosing binder
-- and arithmetic operation while retaining real logs and nonzero real parts.
#guard !decide (Intgrl.CExpr.unary .log .i).LogProjectionSafe
#guard !decide (Intgrl.CExpr.unary .log (.unary .neg .i)).LogProjectionSafe
#guard !decide (Intgrl.CExpr.unary .exp (.unary .log .i)).LogProjectionSafe
#guard !decide (Intgrl.CExpr.binary .add (.real (.rat 1))
  (.unary .log .i)).LogProjectionSafe
#guard !decide (Intgrl.CExpr.integral .interval (.rat 0) (.rat 1)
  (.unary .log .i)).LogProjectionSafe
#guard decide (Intgrl.CExpr.unary .log (.real (.rat 0))).LogProjectionSafe
#guard decide (Intgrl.CExpr.unary .log (.real (.rat (-1)))).LogProjectionSafe
#guard decide (Intgrl.CExpr.unary .log (.real (.var 0))).LogProjectionSafe
#guard decide (Intgrl.CExpr.unary .log
  (.binary .add (.real (.rat 1)) .i)).LogProjectionSafe

end ComplexIntervalArith.Integrals
