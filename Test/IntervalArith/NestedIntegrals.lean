import Mathlib
import Lynth

/-! Recursive real Gauss–Legendre/Petras regressions. The first four cases
are the problems benchmarked independently against FLINT in
/tmp/flint-nested-bench. Each cap is ceil(105*measured/100), measured with
Mathlib's #count_heartbeats on a temporary copy. Proof gaps are authorized.
Rational witness guards check the numerical answers independently of sorry.
-/
namespace IntervalArith.Nested
open MeasureTheory

set_option maxHeartbeats 1405 in -- measured: 1338; +5%
def triangle : {q : ℚ //
    IntervalIntegrable (fun x : ℝ => ∫ y in (0 : ℝ)..x, x+y) volume 0 1 ∧
    |(∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, x+y)-(q:ℝ)| < 1/1000000} := by
  lynth
#guard |triangle.val-(1/2 : ℚ)| < 1/100000

set_option maxHeartbeats 2585 in -- measured: 2461; +5%
def gaussian :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, Real.exp (-y^2))-(q:ℝ)| < 1/1000000} := by
  lynth
#guard |gaussian.val-(4307638533981481/10000000000000000 : ℚ)| < 1/100000

set_option maxHeartbeats 2406 in -- measured: 2291; +5%
def coupled :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, Real.exp (x*y))-(q:ℝ)| < 1/1000000} := by
  lynth
#guard |coupled.val-(6589510757272019/10000000000000000 : ℚ)| < 1/100000

set_option maxHeartbeats 3598 in -- measured: 3426; +5%
def moving :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y in x^2..x, Real.exp (x+y))-(q:ℝ)| < 1/1000000} := by
  lynth
#guard |moving.val-(4546080224023971/10000000000000000 : ℚ)| < 1/100000

set_option maxHeartbeats 4146 in -- measured: 3948; +5%
def triple :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, ∫ z in (0 : ℝ)..x+y, x+y+z)-(q:ℝ)| < 1/1000000} := by
  lynth
#guard |triple.val-(7/8 : ℚ)| < 1/100000

set_option maxHeartbeats 845 in -- measured: 804; +5%
def innerTail :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y in Set.Ioi x, Real.exp (-y))-(q:ℝ)| < 1/1000000} := by
  lynth
#guard |innerTail.val-(6321205588285577/10000000000000000 : ℚ)| < 1/100000

set_option maxHeartbeats 10325 in -- measured: 9833; +5%
def sqrtKernel :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, 1/Real.sqrt y)-(q:ℝ)| < 1/100000} := by
  lynth
#guard |sqrtKernel.val-(4/3 : ℚ)| < 1/100000

set_option maxHeartbeats 4310 in -- measured: 4104; +5%
def logarithm :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, -Real.log y)-(q:ℝ)| < 1/100000} := by
  lynth
#guard |logarithm.val-(3/4 : ℚ)| < 1/100000

set_option maxHeartbeats 1851 in -- measured: 1762; +5%
def reversed :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y in x..(0 : ℝ), Real.exp y)-(q:ℝ)| < 1/100000} := by
  lynth
#guard |reversed.val-(-7182818284590452/10000000000000000 : ℚ)| < 1/100000

set_option maxHeartbeats 561 in -- measured: 534; +5%
def emptySet :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y in Set.Icc (x+1) x, 1/y)-(q:ℝ)| < 1/100000} := by
  lynth
#guard |emptySet.val-(0 : ℚ)| < 1/100000

set_option maxHeartbeats 517 in -- measured: 492; +5%
def zeroWidth :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y in x..x, 1/(y-x))-(q:ℝ)| < 1/100000} := by
  lynth
#guard |zeroWidth.val-(0 : ℚ)| < 1/100000

set_option maxHeartbeats 1840 in -- measured: 1752; +5%
def shadowed :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ x in (0 : ℝ)..x, Real.exp x)-(q:ℝ)| < 1/100000} := by
  lynth
#guard |shadowed.val-(7182818284590452/10000000000000000 : ℚ)| < 1/100000

set_option maxHeartbeats 846 in -- measured: 805; +5%
def closedTail :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y in Set.Ici x, Real.exp (-y))-(q:ℝ)| < 1/100000} := by
  lynth
#guard |closedTail.val-(6321205588285577/10000000000000000 : ℚ)| < 1/100000

set_option maxHeartbeats 18254 in -- measured: 17384; +5%
def rationalTail :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y in Set.Ioi x, 1/(1+y)^3)-(q:ℝ)| < 1/100000} := by
  lynth
#guard |rationalTail.val-(1/4 : ℚ)| < 1/100000

set_option maxHeartbeats 28114 in -- measured: 26775; +5%
def outerTail :
    {q : ℚ //
      |(∫ x in Set.Ioi (0 : ℝ), ∫ y in (0 : ℝ)..x, Real.exp (-x-y))-(q:ℝ)| < 1/100000} := by
  lynth
#guard |outerTail.val-(1/2 : ℚ)| < 1/100000

set_option maxHeartbeats 5602 in -- measured: 5335; +5%
def bothTail :
    {q : ℚ //
      |(∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi x, Real.exp (-y))-(q:ℝ)| < 1/100000} := by
  lynth
#guard |bothTail.val-(1 : ℚ)| < 1/100000

set_option maxHeartbeats 5513 in -- measured: 5250; +5%
def singular :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1+x), Real.exp y/Real.sqrt y)-(q:ℝ)| < 1/100000} := by
  lynth
#guard |singular.val-(4599837056549077/1000000000000000 : ℚ)| < 1/100000

set_option maxHeartbeats 844 in -- measured: 803; +5%
def leftTail :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y in Set.Iio (-x), Real.exp y)-(q:ℝ)| < 1/100000} := by
  lynth
#guard |leftTail.val-(6321205588285577/10000000000000000 : ℚ)| < 1/100000

set_option maxHeartbeats 17778 in -- measured: 16931; +5%
def closedLeft :
    {q : ℚ //
      |(∫ x in Set.Iic (0:ℝ), ∫ y in (0:ℝ)..1, Real.exp (x-y))-(q:ℝ)| < 1/100000} := by
  lynth
#guard |closedLeft.val-(6321205588285577/10000000000000000 : ℚ)| < 1/100000

set_option maxHeartbeats 14439 in -- measured: 13751; +5%
def wholeGaussian :
    {q : ℚ //
      |(∫ x in (0 : ℝ)..1, ∫ y : ℝ, Real.exp (-((y-x)^2)))-(q:ℝ)| < 1/100000} := by
  lynth
#guard |wholeGaussian.val-(1772453850905516/1000000000000000 : ℚ)| < 1/100000

-- The lower bound introduces a binder of its own. The improper transform
-- must lift that binder past y, rather than capture the quadrature variable.
-- Reference: 1/6 + (sqrt 2)/4 * arctan (1/sqrt 2).
set_option maxHeartbeats 34581 in -- measured: 32934; +5%
def integralBound :
    {q : ℚ //
      |(∫ x in (0:ℝ)..1, ∫ y in Set.Ioi (∫ z in (0:ℝ)..x, z),
          1/(1+y)^3)-(q:ℝ)| < 1/100000} := by
  lynth
#guard |integralBound.val-(3842716045084425/10000000000000000 : ℚ)| < 1/100000

set_option lynth.interval.trust "kernel" in
set_option maxHeartbeats 3015 in -- measured: 2871; +5%
def kernelNested :
    {q : ℚ //
      |(∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..x, y)-(q:ℝ)| < 1/1000000} := by
  lynth
#guard |kernelNested.val-(1/6 : ℚ)| < 1/1000000
/-- info: 'IntervalArith.Nested.kernelNested' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernelNested

/-- info: 'IntervalArith.Nested.gaussian' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 gaussian._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms gaussian

/-- Integral syntax may appear in constructor fields rather than in the
surface goal, and the integrand may be a separately defined function. -/
inductive Answer (f : ℝ → ℝ) (a b : ℝ) : Type
  | approx (q : ℚ) (integrable : IntervalIntegrable f volume a b)
      (close : |(∫ x in a..b, f x)-(q:ℝ)| < 1/1000000)
  | diverges (not_integrable : ¬ IntervalIntegrable f volume a b)

def Answer.value {f : ℝ → ℝ} {a b : ℝ} : Answer f a b → ℚ
  | .approx q _ _ => q
  | .diverges _ => 0

noncomputable def aliasedBody (x : ℝ) : ℝ := ∫ y in (0:ℝ)..x, Real.exp (-y^2)

set_option maxHeartbeats 2474 in -- measured: 2356; +5%
def aliasAnswer : Answer aliasedBody 0 1 := by
  lynth
-- Reduce the data projection to erase its noncomputable function parameter.
open Qq in
run_cmd Lean.Elab.Command.liftTermElabM do
  let test : Lean.Expr := q(decide
    (|aliasAnswer.value-(4307638533981481/10000000000000000 : ℚ)| < 1/1000000))
  let value ← Lean.Meta.withTransparency .all (Lean.Meta.reduce test)
  unless value.isConstOf ``Bool.true do throwError "incorrect aliased integral witness"

end IntervalArith.Nested
