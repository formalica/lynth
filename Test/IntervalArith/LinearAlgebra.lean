import Mathlib
import Lynth

namespace IntervalArith

def Vec3 := Fin 3 → Rat

def linearMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![![2, 1, 1], ![1, 3, -1], ![1, -1, 2]]

def linearRhs : Fin 3 → ℝ :=
  ![5, 1, 7]

/-- L01 — approximate the solution of the 3-by-3 system.
Etalon: `(-2, 3, 6)`. -/
def linearSolveGoal :
    { x : Vec3 //
      ∀ i : Fin 3,
        abs (linearMatrix.mulVec
          (fun j : Fin 3 => (x j : ℝ)) i -
          linearRhs i) < 1 / 1000000 } := by
  lynth

def rotationMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![![0, -1], ![1, 0]]

/-- L02 — approximate the matrix exponential of the rotation matrix.
Etalon: `[[cos 1, -sin 1], [sin 1, cos 1]]`. -/
def matrixExpGoal :
    { M : Fin 2 → Fin 2 → Rat //
      ∀ i j : Fin 2,
        abs ((M i j : ℝ) -
          NormedSpace.exp rotationMatrix i j) <
          1 / 10000 } := by
  lynth

#eval linearSolveGoal.1
#eval matrixExpGoal.1

/-- info: 'IntervalArith.Vec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vec3

/-- info: 'IntervalArith.linearMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linearMatrix

/-- info: 'IntervalArith.linearRhs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linearRhs

/-- info: 'IntervalArith.linearSolveGoal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linearSolveGoal

/-- info: 'IntervalArith.rotationMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rotationMatrix

/-- info: 'IntervalArith.matrixExpGoal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms matrixExpGoal

end IntervalArith
