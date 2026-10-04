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
/-- info: 'ApproxRoots.ApproximationOrImpossible' does not depend on any axioms -/
#guard_msgs in
#print axioms ApproximationOrImpossible

/-- A rational root witness or a proof that no such witness exists. -/
def RootOrNoRoot
    (g : Rat → ℝ) (lo hi tol : ℝ) : Type :=
  ApproximationOrImpossible (fun (x : Rat) =>
    lo ≤ (x : ℝ) ∧ (x : ℝ) ≤ hi ∧ abs (g x) < tol)
/-- info: 'ApproxRoots.RootOrNoRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RootOrNoRoot

/-- A rational inequality witness or a proof that no such witness exists. -/
def InequalityOrNoWitness
    (g : Rat → ℝ) (lo hi tol : ℝ) : Type :=
  ApproximationOrImpossible (fun (x : Rat) =>
    lo ≤ (x : ℝ) ∧ (x : ℝ) ≤ hi ∧ g x < 0 ∧ abs (g x) < tol)
/-- info: 'ApproxRoots.InequalityOrNoWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InequalityOrNoWitness

noncomputable def rootTolerance : ℝ := 1 / 100000000
/-- info: 'ApproxRoots.rootTolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootTolerance

noncomputable def quinticResidual (x : Rat) : ℝ :=
  (x : ℝ) ^ 5 - (x : ℝ) - 1
/-- info: 'ApproxRoots.quinticResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quinticResidual

noncomputable def expCosResidual (x : Rat) : ℝ :=
  Real.exp (Real.cos (x : ℝ)) - (x : ℝ) - 2
/-- info: 'ApproxRoots.expCosResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosResidual

noncomputable def cosSquareResidual (x : Rat) : ℝ :=
  Real.cos ((x : ℝ) ^ 2) - (x : ℝ)
/-- info: 'ApproxRoots.cosSquareResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosSquareResidual

noncomputable def expNegSquareResidual (x : Rat) : ℝ :=
  Real.exp (-(x : ℝ) ^ 2) - (x : ℝ)
/-- info: 'ApproxRoots.expNegSquareResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expNegSquareResidual

noncomputable def sinSquareResidual (x : Rat) : ℝ :=
  Real.sin ((x : ℝ) ^ 2) - (x : ℝ) / 2
/-- info: 'ApproxRoots.sinSquareResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sinSquareResidual

noncomputable def expSinOffsetResidual (x : Rat) : ℝ :=
  Real.exp (Real.sin (x : ℝ)) - (x : ℝ) - 11 / 10
/-- info: 'ApproxRoots.expSinOffsetResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expSinOffsetResidual

noncomputable def expCosNoSolutionResidual (x : Rat) : ℝ :=
  Real.exp (Real.cos (x : ℝ)) + 1
/-- info: 'ApproxRoots.expCosNoSolutionResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosNoSolutionResidual

noncomputable def cosSquareNoSolutionResidual (x : Rat) : ℝ :=
  Real.cos ((x : ℝ) ^ 2) - ((x : ℝ) ^ 2 + 1)
/-- info: 'ApproxRoots.cosSquareNoSolutionResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosSquareNoSolutionResidual

noncomputable def expSinNoSolutionResidual (x : Rat) : ℝ :=
  Real.exp (Real.sin (x : ℝ)) + (x : ℝ) + 1
/-- info: 'ApproxRoots.expSinNoSolutionResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expSinNoSolutionResidual

noncomputable def sinExpNoSolutionResidual (x : Rat) : ℝ :=
  Real.sin (Real.exp (x : ℝ)) - 2
/-- info: 'ApproxRoots.sinExpNoSolutionResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sinExpNoSolutionResidual

noncomputable def expCosInequalityResidual (x : Rat) : ℝ :=
  Real.exp (Real.cos (x : ℝ)) - (x : ℝ) - 2
/-- info: 'ApproxRoots.expCosInequalityResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosInequalityResidual

noncomputable def expCosNegativeInequalityResidual (x : Rat) : ℝ :=
  Real.exp (Real.cos (x : ℝ)) + 1
/-- info: 'ApproxRoots.expCosNegativeInequalityResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosNegativeInequalityResidual

/-- **AR01** — `r^5 - r - 1 = 0` on `[1, 3/2]`. -/
def quinticRoot :
    RootOrNoRoot quinticResidual 1 (3/2) rootTolerance := by
  lynth
/-- info: 'ApproxRoots.quinticRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quinticRoot

/-- **C01** — `exp (cos r) = r + 2` on `[0, 1]`. -/
def expCosRoot :
    RootOrNoRoot expCosResidual 0 1 rootTolerance := by
  lynth
/-- info: 'ApproxRoots.expCosRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosRoot

/-- **C02** — `cos (r^2) = r` on `[0, 1]`. -/
def cosSquareRoot :
    RootOrNoRoot cosSquareResidual 0 1 rootTolerance := by
  lynth
/-- info: 'ApproxRoots.cosSquareRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosSquareRoot

/-- **C03** — `exp (-r^2) = r` on `[0, 1]`. -/
def expNegSquareRoot :
    RootOrNoRoot expNegSquareResidual 0 1 rootTolerance := by
  lynth
/-- info: 'ApproxRoots.expNegSquareRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expNegSquareRoot

/-- **C04** — `sin (r^2) = r / 2` on `[1/2, 1]`. -/
def sinSquareRoot :
    RootOrNoRoot sinSquareResidual (1/2) 1 rootTolerance := by
  lynth
/-- info: 'ApproxRoots.sinSquareRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sinSquareRoot

/-- **C05** — `exp (sin r) = r + 11/10` on `[1/10, 1]`. -/
def expSinOffsetRoot :
    RootOrNoRoot expSinOffsetResidual (1/10) 1 rootTolerance := by
  lynth
/-- info: 'ApproxRoots.expSinOffsetRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expSinOffsetRoot

/-- **N01** — `exp (cos r) = -1` has no solution on `[0, 1]`. -/
def expCosNoSolution :
    RootOrNoRoot expCosNoSolutionResidual 0 1 rootTolerance := by
  lynth
/-- info: 'ApproxRoots.expCosNoSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosNoSolution

/-- **N02** — `cos (r^2) = r^2 + 1` has no solution on `[1/2, 1]`. -/
def cosSquareNoSolution :
    RootOrNoRoot cosSquareNoSolutionResidual (1/2) 1 rootTolerance := by
  lynth
/-- info: 'ApproxRoots.cosSquareNoSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosSquareNoSolution

/-- **N03** — `exp (sin r) + r = -1` has no solution on `[0, 1]`. -/
def expSinNoSolution :
    RootOrNoRoot expSinNoSolutionResidual 0 1 rootTolerance := by
  lynth
/-- info: 'ApproxRoots.expSinNoSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expSinNoSolution

/-- **N04** — `sin (exp r) = 2` has no solution on `[0, 1]`. -/
def sinExpNoSolution :
    RootOrNoRoot sinExpNoSolutionResidual 0 1 rootTolerance := by
  lynth
/-- info: 'ApproxRoots.sinExpNoSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sinExpNoSolution

/-- **I01** — `exp (cos r) - r - 2 < 0` on `[4/5, 1]`. -/
def expCosNegativeInequalitySolution :
    InequalityOrNoWitness expCosInequalityResidual (4/5) 1 rootTolerance := by
  lynth
/-- info: 'ApproxRoots.expCosNegativeInequalitySolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosNegativeInequalitySolution

/-- **I02** — `exp (cos r) < -1` has no witness on `[0, 1]`. -/
def expCosNegativeInequalityNoSolution :
    InequalityOrNoWitness expCosNegativeInequalityResidual 0 1 rootTolerance := by
  lynth
/-- info: 'ApproxRoots.expCosNegativeInequalityNoSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosNegativeInequalityNoSolution

-- Axiom footprint checks.

end ApproxRoots
