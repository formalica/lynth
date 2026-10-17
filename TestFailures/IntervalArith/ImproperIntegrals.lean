import Test.IntervalArith.ImproperIntegrals

/-! The one-dimensional cases now pass. The multivariate cube remains. -/

namespace IntervalArith

/-- **IC09** — `∫_[0,1]^10 (x₁ + ... + x₁₀) dx`; expected value `5`. -/
def cubeSumSubtype :
    { x : Rat //
      MeasureTheory.IntegrableOn cubeSum
          (Set.Icc (0 : Fin 10 → ℝ) (1 : Fin 10 → ℝ)) ∧
      abs ((∫ y in Set.Icc (0 : Fin 10 → ℝ) (1 : Fin 10 → ℝ), cubeSum y) - x) < integralTolerance } := by
  lynth
/-- info: 'IntervalArith.cubeSumSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubeSumSubtype

end IntervalArith
