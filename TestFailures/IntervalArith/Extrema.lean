import Mathlib
import Lynth

/-!
Local and global extrema tests.  Each result either supplies a rational
witness satisfying an approximate extremum predicate, or supplies a proof that
no such witness exists.
-/

namespace IntervalArith

/-- A witness or a proof that no witness exists. -/
def ExtremaAnswer {α : Type} (p : α → Prop) : Type :=
  { x : α // p x } ⊕' (∀ x, ¬ p x)
/-- info: 'IntervalArith.ExtremaAnswer' does not depend on any axioms -/
#guard_msgs in
#print axioms ExtremaAnswer

/-- Exact global minimum relative to a rational set. -/
def IsGlobalMinOn (f : Rat → ℝ) (s : Set Rat) (x : Rat) : Prop :=
  x ∈ s ∧ ∀ y, y ∈ s → f x ≤ f y
/-- info: 'IntervalArith.IsGlobalMinOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsGlobalMinOn

/-- Exact global maximum relative to a rational set. -/
def IsGlobalMaxOn (f : Rat → ℝ) (s : Set Rat) (x : Rat) : Prop :=
  x ∈ s ∧ ∀ y, y ∈ s → f y ≤ f x
/-- info: 'IntervalArith.IsGlobalMaxOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsGlobalMaxOn

/-- Approximate global minimum relative to a rational set. -/
def ApproxGlobalMin
    (f : Rat → ℝ) (s : Set Rat) (x : Rat) (tol : ℝ) : Prop :=
  x ∈ s ∧ ∀ y, y ∈ s → f x ≤ f y + tol
/-- info: 'IntervalArith.ApproxGlobalMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ApproxGlobalMin

/-- Approximate global maximum relative to a rational set. -/
def ApproxGlobalMax
    (f : Rat → ℝ) (s : Set Rat) (x : Rat) (tol : ℝ) : Prop :=
  x ∈ s ∧ ∀ y, y ∈ s → f y ≤ f x + tol
/-- info: 'IntervalArith.ApproxGlobalMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ApproxGlobalMax

/-- Exact relative local minimum. -/
def IsLocalMinOn
    (f : Rat → ℝ) (s : Set Rat)
    (x : Rat) (radius : ℝ) : Prop :=
  x ∈ s ∧
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ radius ∧
    ∀ y, y ∈ s →
      abs ((y : ℝ) - (x : ℝ)) < δ →
      f x ≤ f y
/-- info: 'IntervalArith.IsLocalMinOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLocalMinOn

/-- Exact relative local maximum. -/
def IsLocalMaxOn
    (f : Rat → ℝ) (s : Set Rat)
    (x : Rat) (radius : ℝ) : Prop :=
  x ∈ s ∧
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ radius ∧
    ∀ y, y ∈ s →
      abs ((y : ℝ) - (x : ℝ)) < δ →
      f y ≤ f x
/-- info: 'IntervalArith.IsLocalMaxOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLocalMaxOn

/-- Approximate relative local minimum. -/
def ApproxLocalMin
    (f : Rat → ℝ) (s : Set Rat)
    (x : Rat) (radius tol : ℝ) : Prop :=
  x ∈ s ∧
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ radius ∧
    ∀ y, y ∈ s →
      abs ((y : ℝ) - (x : ℝ)) < δ →
      f x ≤ f y + tol
/-- info: 'IntervalArith.ApproxLocalMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ApproxLocalMin

/-- Approximate relative local maximum. -/
def ApproxLocalMax
    (f : Rat → ℝ) (s : Set Rat)
    (x : Rat) (radius tol : ℝ) : Prop :=
  x ∈ s ∧
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ radius ∧
    ∀ y, y ∈ s →
      abs ((y : ℝ) - (x : ℝ)) < δ →
      f y ≤ f x + tol
/-- info: 'IntervalArith.ApproxLocalMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ApproxLocalMax

def GlobalMinOrNoMin
    (f : Rat → ℝ) (s : Set Rat) (tol : ℝ) : Type :=
  ExtremaAnswer (fun x => ApproxGlobalMin f s x tol)
/-- info: 'IntervalArith.GlobalMinOrNoMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GlobalMinOrNoMin

def GlobalMaxOrNoMax
    (f : Rat → ℝ) (s : Set Rat) (tol : ℝ) : Type :=
  ExtremaAnswer (fun x => ApproxGlobalMax f s x tol)
/-- info: 'IntervalArith.GlobalMaxOrNoMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GlobalMaxOrNoMax

def LocalMinOrNoLocal
    (f : Rat → ℝ) (s : Set Rat) (radius tol : ℝ) : Type :=
  ExtremaAnswer (fun x => ApproxLocalMin f s x radius tol)
/-- info: 'IntervalArith.LocalMinOrNoLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LocalMinOrNoLocal

def LocalMaxOrNoLocal
    (f : Rat → ℝ) (s : Set Rat) (radius tol : ℝ) : Type :=
  ExtremaAnswer (fun x => ApproxLocalMax f s x radius tol)
/-- info: 'IntervalArith.LocalMaxOrNoLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LocalMaxOrNoLocal

noncomputable def extremaTolerance : ℝ := 1 / 1000000
/-- info: 'IntervalArith.extremaTolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms extremaTolerance

noncomputable def quadraticMin (x : Rat) : ℝ :=
  ((x : ℝ) - 1 / 3) ^ 2
/-- info: 'IntervalArith.quadraticMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadraticMin

noncomputable def sqrtCompositionMin (x : Rat) : ℝ :=
  ((x : ℝ) - 1 / 2) ^ 2 +
    (Real.sqrt ((x : ℝ) + 1) - 3 / 2) ^ 2
/-- info: 'IntervalArith.sqrtCompositionMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqrtCompositionMin

noncomputable def arctanCompositionMax (x : Rat) : ℝ :=
  Real.arctan ((x : ℝ) + 1) - ((x : ℝ) - 1 / 4) ^ 2
/-- info: 'IntervalArith.arctanCompositionMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arctanCompositionMax

noncomputable def logLocalMin (x : Rat) : ℝ :=
  5 * ((x : ℝ) - 1 / 2) ^ 2 - Real.log ((x : ℝ) + 1)
/-- info: 'IntervalArith.logLocalMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logLocalMin

noncomputable def tanhLocalMax (x : Rat) : ℝ :=
  Real.tanh (x : ℝ) - 5 * ((x : ℝ) - 1 / 2) ^ 2
/-- info: 'IntervalArith.tanhLocalMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tanhLocalMax

noncomputable def identityReal (x : Rat) : ℝ :=
  (x : ℝ)
/-- info: 'IntervalArith.identityReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identityReal

noncomputable def negIdentityReal (x : Rat) : ℝ :=
  -(x : ℝ)
/-- info: 'IntervalArith.negIdentityReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negIdentityReal

noncomputable def cubeReal (x : Rat) : ℝ :=
  (x : ℝ) ^ 3
/-- info: 'IntervalArith.cubeReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubeReal

noncomputable def inverseReal (x : Rat) : ℝ :=
  1 / (x : ℝ)
/-- info: 'IntervalArith.inverseReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inverseReal

/-- **E01** — exact global minimum of `(x - 1/3)^2` on `[0,1]`. -/
def quadraticGlobalMin :
    GlobalMinOrNoMin quadraticMin (Set.Icc (0 : Rat) 1) 0 := by
  lynth
/-- info: 'IntervalArith.quadraticGlobalMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadraticGlobalMin

/-- **E02** — approximate global minimum of
`(x - 1/2)^2 + (sqrt (x+1) - 3/2)^2` on `[0,1]`. -/
def sqrtCompositionGlobalMin :
    GlobalMinOrNoMin sqrtCompositionMin
      (Set.Icc (0 : Rat) 1) extremaTolerance := by
  lynth
/-- info: 'IntervalArith.sqrtCompositionGlobalMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqrtCompositionGlobalMin

/-- **E03** — approximate global maximum of
`arctan (x+1) - (x-1/4)^2` on `[0,1]`. -/
def arctanCompositionGlobalMax :
    GlobalMaxOrNoMax arctanCompositionMax
      (Set.Icc (0 : Rat) 1) extremaTolerance := by
  lynth
/-- info: 'IntervalArith.arctanCompositionGlobalMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arctanCompositionGlobalMax

/-- **E04** — local minimum of `5(x-1/2)^2 - log (x+1)` on `[0,1]`. -/
def logLocalMinimum :
    LocalMinOrNoLocal logLocalMin
      (Set.Icc (0 : Rat) 1) 1 extremaTolerance := by
  lynth
/-- info: 'IntervalArith.logLocalMinimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logLocalMinimum

/-- **E05** — local maximum of `tanh x - 5(x-1/2)^2` on `[0,1]`. -/
def tanhLocalMaximum :
    LocalMaxOrNoLocal tanhLocalMax
      (Set.Icc (0 : Rat) 1) 1 extremaTolerance := by
  lynth
/-- info: 'IntervalArith.tanhLocalMaximum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tanhLocalMaximum

/-- **E06** — no global minimum of `x` on the open interval `(0,1)`. -/
theorem noGlobalMin_openUnit :
    ¬ ∃ x : Rat, IsGlobalMinOn identityReal (Set.Ioo (0 : Rat) 1) x := by
  lynth
/-- info: 'IntervalArith.noGlobalMin_openUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noGlobalMin_openUnit

/-- **E07** — no global maximum of `-x` on the open interval `(0,1)`. -/
theorem noGlobalMax_openUnit :
    ¬ ∃ x : Rat, IsGlobalMaxOn negIdentityReal (Set.Ioo (0 : Rat) 1) x := by
  lynth
/-- info: 'IntervalArith.noGlobalMax_openUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noGlobalMax_openUnit

/-- **E08** — no local minimum of `x^3` on `(0,1)`. -/
def noLocalMin_cube :
    LocalMinOrNoLocal cubeReal (Set.Ioo (0 : Rat) 1) 1 0 := by
  lynth
/-- info: 'IntervalArith.noLocalMin_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noLocalMin_cube

/-- **E09** — no local maximum of `x^3` on `(0,1)`. -/
def noLocalMax_cube :
    LocalMaxOrNoLocal cubeReal (Set.Ioo (0 : Rat) 1) 1 0 := by
  lynth
/-- info: 'IntervalArith.noLocalMax_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noLocalMax_cube

/-- **E10** — no global minimum of `1/x` on `(0,1)`. -/
theorem noGlobalMin_inverse :
    ¬ ∃ x : Rat, IsGlobalMinOn inverseReal (Set.Ioo (0 : Rat) 1) x := by
  lynth
/-- info: 'IntervalArith.noGlobalMin_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noGlobalMin_inverse

/-- **E11** — no global maximum of `1/x` on `(0,1)`. -/
theorem noGlobalMax_inverse :
    ¬ ∃ x : Rat, IsGlobalMaxOn inverseReal (Set.Ioo (0 : Rat) 1) x := by
  lynth
/-- info: 'IntervalArith.noGlobalMax_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noGlobalMax_inverse

-- Axiom footprint checks.

end IntervalArith
