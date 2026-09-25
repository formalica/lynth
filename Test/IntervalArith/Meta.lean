import Mathlib
import Lynth

namespace IntervalArith

def expNegSquareConverges (a b : ℝ) : Prop :=
  MeasureTheory.IntegrableOn
    (fun y : ℝ => Real.exp (-(y ^ 2)))
    (Set.Icc a b)

def integralExpNegSqMeta :
    { f : Rat → Rat → Rat //
      ∀ a b : Rat,
        if a < b ∧
            expNegSquareConverges (a : ℝ) (b : ℝ) then
          abs ((∫ y in (a : ℝ)..(b : ℝ),
            Real.exp (-(y ^ 2))) - (f a b : ℝ)) <
            1 / 1000
        else
          f a b = 0 } := by
  lynth

def expMeta :
    { f : Rat → Rat //
      ∀ x : Rat,
        abs (Real.exp (x : ℝ) - (f x : ℝ)) <
          1 / 1000 } := by
  lynth

def logExpMeta :
    { f : Rat → Rat //
      ∀ x : Rat,
        abs (Real.log (1 + Real.exp (x : ℝ)) -
          (f x : ℝ)) <
          1 / 1000 } := by
  lynth

def sumExpCosMeta :
    { f : Nat → Rat //
      ∀ n : Nat,
        abs ((∑ k ∈ Finset.range n,
          Real.exp (-(k : ℝ)) * Real.cos (k : ℝ)) -
          (f n : ℝ)) <
          1 / 1000 } := by
  lynth

#eval integralExpNegSqMeta.1 0 1
#eval integralExpNegSqMeta.1 1 2
#eval integralExpNegSqMeta.1 2 1
#eval expMeta.1 0
#eval expMeta.1 1
#eval logExpMeta.1 0
#eval logExpMeta.1 1
#eval sumExpCosMeta.1 0
#eval sumExpCosMeta.1 5

/-- info: 'IntervalArith.expNegSquareConverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expNegSquareConverges

/-- info: 'IntervalArith.integralExpNegSqMeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integralExpNegSqMeta

/-- info: 'IntervalArith.expMeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expMeta

/-- info: 'IntervalArith.logExpMeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logExpMeta

/-- info: 'IntervalArith.sumExpCosMeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sumExpCosMeta

end IntervalArith
