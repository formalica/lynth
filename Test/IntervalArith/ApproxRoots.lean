import Mathlib
import Lynth

/-!
Approximate roots and inequalities with rational witnesses.  Each root or
inequality goal has two possible constructors: a witness, or a proof that no
witness exists in the requested interval.
-/

namespace ApproxRoots

/-- A data-or-refutation answer for a predicate on a type. -/
def ApproximationOrImpossible {α : Type} (p : α → Prop) : Type :=
  { w : α // p w } ⊕' (∀ w, ¬ p w)

/-- A rational root witness or a proof that no such witness exists. -/
def RootOrNoRoot
    (g : Rat → ℝ) (lo hi tol : ℝ) : Type :=
  ApproximationOrImpossible (fun (x : Rat) =>
    lo ≤ (x : ℝ) ∧ (x : ℝ) ≤ hi ∧ abs (g x) < tol)

/-- A rational inequality witness or a proof that no such witness exists. -/
def InequalityOrNoWitness
    (g : Rat → ℝ) (lo hi tol : ℝ) : Type :=
  ApproximationOrImpossible (fun (x : Rat) =>
    lo ≤ (x : ℝ) ∧ (x : ℝ) ≤ hi ∧ g x < 0 ∧ abs (g x) < tol)

noncomputable def rootTolerance : ℝ := 1 / 100000000

noncomputable def quinticResidual (x : Rat) : ℝ :=
  (x : ℝ) ^ 5 - (x : ℝ) - 1

noncomputable def expCosResidual (x : Rat) : ℝ :=
  Real.exp (Real.cos (x : ℝ)) - (x : ℝ) - 2

noncomputable def cosSquareResidual (x : Rat) : ℝ :=
  Real.cos ((x : ℝ) ^ 2) - (x : ℝ)

noncomputable def expNegSquareResidual (x : Rat) : ℝ :=
  Real.exp (-(x : ℝ) ^ 2) - (x : ℝ)

noncomputable def sinSquareResidual (x : Rat) : ℝ :=
  Real.sin ((x : ℝ) ^ 2) - (x : ℝ) / 2

noncomputable def expSinOffsetResidual (x : Rat) : ℝ :=
  Real.exp (Real.sin (x : ℝ)) - (x : ℝ) - 11 / 10

noncomputable def expCosNoSolutionResidual (x : Rat) : ℝ :=
  Real.exp (Real.cos (x : ℝ)) + 1

noncomputable def cosSquareNoSolutionResidual (x : Rat) : ℝ :=
  Real.cos ((x : ℝ) ^ 2) - ((x : ℝ) ^ 2 + 1)

noncomputable def expSinNoSolutionResidual (x : Rat) : ℝ :=
  Real.exp (Real.sin (x : ℝ)) + (x : ℝ) + 1

noncomputable def sinExpNoSolutionResidual (x : Rat) : ℝ :=
  Real.sin (Real.exp (x : ℝ)) - 2

noncomputable def expCosInequalityResidual (x : Rat) : ℝ :=
  Real.exp (Real.cos (x : ℝ)) - (x : ℝ) - 2

noncomputable def expCosNegativeInequalityResidual (x : Rat) : ℝ :=
  Real.exp (Real.cos (x : ℝ)) + 1

/-- **AR01** — `r^5 - r - 1 = 0` on `[1, 3/2]`. -/
def quinticRoot :
    RootOrNoRoot quinticResidual 1 3/2 rootTolerance := by
  lynth

/-- **C01** — `exp (cos r) = r + 2` on `[0, 1]`. -/
def expCosRoot :
    RootOrNoRoot expCosResidual 0 1 rootTolerance := by
  lynth

/-- **C02** — `cos (r^2) = r` on `[0, 1]`. -/
def cosSquareRoot :
    RootOrNoRoot cosSquareResidual 0 1 rootTolerance := by
  lynth

/-- **C03** — `exp (-r^2) = r` on `[0, 1]`. -/
def expNegSquareRoot :
    RootOrNoRoot expNegSquareResidual 0 1 rootTolerance := by
  lynth

/-- **C04** — `sin (r^2) = r / 2` on `[1/2, 1]`. -/
def sinSquareRoot :
    RootOrNoRoot sinSquareResidual 1/2 1 rootTolerance := by
  lynth

/-- **C05** — `exp (sin r) = r + 11/10` on `[1/10, 1]`. -/
def expSinOffsetRoot :
    RootOrNoRoot expSinOffsetResidual 1/10 1 rootTolerance := by
  lynth

/-- **N01** — `exp (cos r) = -1` has no solution on `[0, 1]`. -/
def expCosNoSolution :
    RootOrNoRoot expCosNoSolutionResidual 0 1 rootTolerance := by
  lynth

/-- **N02** — `cos (r^2) = r^2 + 1` has no solution on `[1/2, 1]`. -/
def cosSquareNoSolution :
    RootOrNoRoot cosSquareNoSolutionResidual 1/2 1 rootTolerance := by
  lynth

/-- **N03** — `exp (sin r) + r = -1` has no solution on `[0, 1]`. -/
def expSinNoSolution :
    RootOrNoRoot expSinNoSolutionResidual 0 1 rootTolerance := by
  lynth

/-- **N04** — `sin (exp r) = 2` has no solution on `[0, 1]`. -/
def sinExpNoSolution :
    RootOrNoRoot sinExpNoSolutionResidual 0 1 rootTolerance := by
  lynth

/-- **I01** — `exp (cos r) - r - 2 < 0` on `[4/5, 1]`. -/
def expCosNegativeInequalitySolution :
    InequalityOrNoWitness expCosInequalityResidual 4/5 1 rootTolerance := by
  lynth

/-- **I02** — `exp (cos r) < -1` has no witness on `[0, 1]`. -/
def expCosNegativeInequalityNoSolution :
    InequalityOrNoWitness expCosNegativeInequalityResidual 0 1 rootTolerance := by
  lynth

-- Axiom footprint checks.
/-- info: 'ApproxRoots.ApproximationOrImpossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ApproximationOrImpossible
/-- info: 'ApproxRoots.RootOrNoRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RootOrNoRoot
/-- info: 'ApproxRoots.InequalityOrNoWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InequalityOrNoWitness
/-- info: 'ApproxRoots.rootTolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootTolerance
/-- info: 'ApproxRoots.quinticResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quinticResidual
/-- info: 'ApproxRoots.expCosResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosResidual
/-- info: 'ApproxRoots.cosSquareResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosSquareResidual
/-- info: 'ApproxRoots.expNegSquareResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expNegSquareResidual
/-- info: 'ApproxRoots.sinSquareResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sinSquareResidual
/-- info: 'ApproxRoots.expSinOffsetResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expSinOffsetResidual
/-- info: 'ApproxRoots.expCosNoSolutionResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosNoSolutionResidual
/-- info: 'ApproxRoots.cosSquareNoSolutionResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosSquareNoSolutionResidual
/-- info: 'ApproxRoots.expSinNoSolutionResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expSinNoSolutionResidual
/-- info: 'ApproxRoots.sinExpNoSolutionResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sinExpNoSolutionResidual
/-- info: 'ApproxRoots.expCosInequalityResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosInequalityResidual
/-- info: 'ApproxRoots.expCosNegativeInequalityResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosNegativeInequalityResidual
/-- info: 'ApproxRoots.quinticRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quinticRoot
/-- info: 'ApproxRoots.expCosRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosRoot
/-- info: 'ApproxRoots.cosSquareRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosSquareRoot
/-- info: 'ApproxRoots.expNegSquareRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expNegSquareRoot
/-- info: 'ApproxRoots.sinSquareRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sinSquareRoot
/-- info: 'ApproxRoots.expSinOffsetRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expSinOffsetRoot
/-- info: 'ApproxRoots.expCosNoSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosNoSolution
/-- info: 'ApproxRoots.cosSquareNoSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosSquareNoSolution
/-- info: 'ApproxRoots.expSinNoSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expSinNoSolution
/-- info: 'ApproxRoots.sinExpNoSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sinExpNoSolution
/-- info: 'ApproxRoots.expCosNegativeInequalitySolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosNegativeInequalitySolution
/-- info: 'ApproxRoots.expCosNegativeInequalityNoSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosNegativeInequalityNoSolution

end ApproxRoots
