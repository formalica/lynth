import Mathlib
import Lynth
import Test.IntervalArith.SpecialFunctionValues

/-! Real integration of entire special functions. FLINT 25, 26, 30 and 37
retain their original domains; eta also crosses its removable point at one.
Every theorem is reconstructed by lynth, with generic mathematical handoffs.
-/

namespace IntervalArith.SpecialIntegrals

open MeasureTheory
set_option maxRecDepth 10000

set_option maxHeartbeats 746 in -- measured: 710; +5%
def erfUnit : {q : ℚ //
    IntervalIntegrable (fun x : ℝ => Real.erf x) volume (0) (1) ∧
    |(∫ x in (0 : ℝ)..(1), Real.erf x) - (q : ℝ)| < 1/100000} := by
  lynth
#check_special_axioms erfUnit
#guard |erfUnit.val - ((486064958112255934063275308243/10^30) : ℚ)| < 1/100000

set_option maxHeartbeats 643 in -- measured: 612; +5%
def siUnit : {q : ℚ //
    IntervalIntegrable (fun x : ℝ => Real.Si x) volume (0) (1) ∧
    |(∫ x in (0 : ℝ)..(1), Real.Si x) - (q : ℝ)| < 1/100000} := by
  lynth
#check_special_axioms siUnit
#guard |siUnit.val - ((486385376235322732342289921266/10^30) : ℚ)| < 1/100000

set_option maxHeartbeats 810 in -- measured: 771; +5%
def airyUnit : {q : ℚ //
    IntervalIntegrable (fun x : ℝ => Real.airyAi x) volume (0) (1) ∧
    |(∫ x in (0 : ℝ)..(1), Real.airyAi x) - (q : ℝ)| < 1/100000} := by
  lynth
#check_special_axioms airyUnit
#guard |airyUnit.val - ((236317341917109779601896333840/10^30) : ℚ)| < 1/100000

set_option maxHeartbeats 16102 in -- measured: 15335; +5%
def etaRange : {q : ℚ //
    IntervalIntegrable (fun x : ℝ => Real.dirichletEta x) volume (-1) (2) ∧
    |(∫ x in (-1 : ℝ)..(2), Real.dirichletEta x) - (q : ℝ)| < 1/100000} := by
  lynth
#check_special_axioms etaRange
#guard |etaRange.val - ((1743189554401728319250684586370/10^30) : ℚ)| < 1/100000

set_option maxHeartbeats 3997 in -- measured: 3806; +5%
def erfBent : {q : ℚ //
    IntervalIntegrable (fun x : ℝ => Real.erf (x / Real.sqrt (1/5000) * (1/2) + 3/2) * Real.exp (-x)) volume (-1) (1) ∧
    |(∫ x in (-1 : ℝ)..(1), Real.erf (x / Real.sqrt (1/5000) * (1/2) + 3/2) * Real.exp (-x)) - (q : ℝ)| < 1/100000} := by
  lynth
#check_special_axioms erfBent
#guard |erfBent.val - ((-999065350291922475595750121145/10^30) : ℚ)| < 1/100000

set_option maxHeartbeats 4504 in -- measured: 4289; +5%
def airyRange : {q : ℚ //
    IntervalIntegrable (fun x : ℝ => Real.airyAi x) volume (-10) (10) ∧
    |(∫ x in (-10 : ℝ)..(10), Real.airyAi x) - (q : ℝ)| < 1/100000} := by
  lynth
#check_special_axioms airyRange
#guard |airyRange.val - ((1099031736433381933367941235478/10^30) : ℚ)| < 1/100000

set_option maxHeartbeats 5312 in -- measured: 5059; +5%
def airyDamped : {q : ℚ //
    IntegrableOn (fun x : ℝ => Real.exp (-x) * Real.airyAi (-x)) (Set.Ioi 0) ∧
    |(∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * Real.airyAi (-x)) - (q : ℝ)| < 1/100000} := by
  lynth
#check_special_axioms airyDamped
#guard |airyDamped.val - ((378751605379086535000192434479/10^30) : ℚ)| < 1/100000

set_option maxHeartbeats 10920 in -- measured: 10400; +5%
def siRange : {q : ℚ //
    IntervalIntegrable (fun x : ℝ => Real.Si x) volume (0) (1000) ∧
    |(∫ x in (0 : ℝ)..(1000), Real.Si x) - (q : ℝ)| < 1/100000} := by
  lynth
#check_special_axioms siRange
#guard |siRange.val - ((1569795501045061921139041027262940/10^30) : ℚ)| < 1/100000

end IntervalArith.SpecialIntegrals
