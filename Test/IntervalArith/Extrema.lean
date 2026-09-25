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

/-- Exact global minimum relative to a rational set. -/
def IsGlobalMinOn (f : Rat → ℝ) (s : Set Rat) (x : Rat) : Prop :=
  x ∈ s ∧ ∀ y, y ∈ s → f x ≤ f y

/-- Exact global maximum relative to a rational set. -/
def IsGlobalMaxOn (f : Rat → ℝ) (s : Set Rat) (x : Rat) : Prop :=
  x ∈ s ∧ ∀ y, y ∈ s → f y ≤ f x

/-- Approximate global minimum relative to a rational set. -/
def ApproxGlobalMin
    (f : Rat → ℝ) (s : Set Rat) (x : Rat) (tol : ℝ) : Prop :=
  x ∈ s ∧ ∀ y, y ∈ s → f x ≤ f y + tol

/-- Approximate global maximum relative to a rational set. -/
def ApproxGlobalMax
    (f : Rat → ℝ) (s : Set Rat) (x : Rat) (tol : ℝ) : Prop :=
  x ∈ s ∧ ∀ y, y ∈ s → f y ≤ f x + tol

/-- Exact relative local minimum. -/
def IsLocalMinOn
    (f : Rat → ℝ) (s : Set Rat)
    (x : Rat) (radius : ℝ) : Prop :=
  x ∈ s ∧
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ radius ∧
    ∀ y, y ∈ s →
      abs ((y : ℝ) - (x : ℝ)) < δ →
      f x ≤ f y

/-- Exact relative local maximum. -/
def IsLocalMaxOn
    (f : Rat → ℝ) (s : Set Rat)
    (x : Rat) (radius : ℝ) : Prop :=
  x ∈ s ∧
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ radius ∧
    ∀ y, y ∈ s →
      abs ((y : ℝ) - (x : ℝ)) < δ →
      f y ≤ f x

/-- Approximate relative local minimum. -/
def ApproxLocalMin
    (f : Rat → ℝ) (s : Set Rat)
    (x : Rat) (radius tol : ℝ) : Prop :=
  x ∈ s ∧
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ radius ∧
    ∀ y, y ∈ s →
      abs ((y : ℝ) - (x : ℝ)) < δ →
      f x ≤ f y + tol

/-- Approximate relative local maximum. -/
def ApproxLocalMax
    (f : Rat → ℝ) (s : Set Rat)
    (x : Rat) (radius tol : ℝ) : Prop :=
  x ∈ s ∧
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ radius ∧
    ∀ y, y ∈ s →
      abs ((y : ℝ) - (x : ℝ)) < δ →
      f y ≤ f x + tol

def GlobalMinOrNoMin
    (f : Rat → ℝ) (s : Set Rat) (tol : ℝ) : Type :=
  ExtremaAnswer (fun x => ApproxGlobalMin f s x tol)

def GlobalMaxOrNoMax
    (f : Rat → ℝ) (s : Set Rat) (tol : ℝ) : Type :=
  ExtremaAnswer (fun x => ApproxGlobalMax f s x tol)

def LocalMinOrNoLocal
    (f : Rat → ℝ) (s : Set Rat) (radius tol : ℝ) : Type :=
  ExtremaAnswer (fun x => ApproxLocalMin f s x radius tol)

def LocalMaxOrNoLocal
    (f : Rat → ℝ) (s : Set Rat) (radius tol : ℝ) : Type :=
  ExtremaAnswer (fun x => ApproxLocalMax f s x radius tol)

noncomputable def extremaTolerance : ℝ := 1 / 1000000

noncomputable def quadraticMin (x : Rat) : ℝ :=
  ((x : ℝ) - 1 / 3) ^ 2

noncomputable def sqrtCompositionMin (x : Rat) : ℝ :=
  ((x : ℝ) - 1 / 2) ^ 2 +
    (Real.sqrt ((x : ℝ) + 1) - 3 / 2) ^ 2

noncomputable def arctanCompositionMax (x : Rat) : ℝ :=
  Real.arctan ((x : ℝ) + 1) - ((x : ℝ) - 1 / 4) ^ 2

noncomputable def logLocalMin (x : Rat) : ℝ :=
  5 * ((x : ℝ) - 1 / 2) ^ 2 - Real.log ((x : ℝ) + 1)

noncomputable def tanhLocalMax (x : Rat) : ℝ :=
  Real.tanh (x : ℝ) - 5 * ((x : ℝ) - 1 / 2) ^ 2

noncomputable def identityReal (x : Rat) : ℝ :=
  (x : ℝ)

noncomputable def negIdentityReal (x : Rat) : ℝ :=
  -(x : ℝ)

noncomputable def cubeReal (x : Rat) : ℝ :=
  (x : ℝ) ^ 3

noncomputable def inverseReal (x : Rat) : ℝ :=
  1 / (x : ℝ)

/-- **E01** — exact global minimum of `(x - 1/3)^2` on `[0,1]`. -/
def quadraticGlobalMin :
    GlobalMinOrNoMin quadraticMin (Set.Icc (0 : Rat) 1) 0 := by
  lynth

/-- **E02** — approximate global minimum of
`(x - 1/2)^2 + (sqrt (x+1) - 3/2)^2` on `[0,1]`. -/
def sqrtCompositionGlobalMin :
    GlobalMinOrNoMin sqrtCompositionMin
      (Set.Icc (0 : Rat) 1) extremaTolerance := by
  lynth

/-- **E03** — approximate global maximum of
`arctan (x+1) - (x-1/4)^2` on `[0,1]`. -/
def arctanCompositionGlobalMax :
    GlobalMaxOrNoMax arctanCompositionMax
      (Set.Icc (0 : Rat) 1) extremaTolerance := by
  lynth

/-- **E04** — local minimum of `5(x-1/2)^2 - log (x+1)` on `[0,1]`. -/
def logLocalMinimum :
    LocalMinOrNoLocal logLocalMin
      (Set.Icc (0 : Rat) 1) 1 extremaTolerance := by
  lynth

/-- **E05** — local maximum of `tanh x - 5(x-1/2)^2` on `[0,1]`. -/
def tanhLocalMaximum :
    LocalMaxOrNoLocal tanhLocalMax
      (Set.Icc (0 : Rat) 1) 1 extremaTolerance := by
  lynth

/-- **E06** — no global minimum of `x` on the open interval `(0,1)`. -/
theorem noGlobalMin_openUnit :
    ¬ ∃ x : Rat, IsGlobalMinOn identityReal (Set.Ioo (0 : Rat) 1) x := by
  lynth

/-- **E07** — no global maximum of `-x` on the open interval `(0,1)`. -/
theorem noGlobalMax_openUnit :
    ¬ ∃ x : Rat, IsGlobalMaxOn negIdentityReal (Set.Ioo (0 : Rat) 1) x := by
  lynth

/-- **E08** — no local minimum of `x^3` on `(0,1)`. -/
def noLocalMin_cube :
    LocalMinOrNoLocal cubeReal (Set.Ioo (0 : Rat) 1) 1 0 := by
  lynth

/-- **E09** — no local maximum of `x^3` on `(0,1)`. -/
def noLocalMax_cube :
    LocalMaxOrNoLocal cubeReal (Set.Ioo (0 : Rat) 1) 1 0 := by
  lynth

/-- **E10** — no global minimum of `1/x` on `(0,1)`. -/
theorem noGlobalMin_inverse :
    ¬ ∃ x : Rat, IsGlobalMinOn inverseReal (Set.Ioo (0 : Rat) 1) x := by
  lynth

/-- **E11** — no global maximum of `1/x` on `(0,1)`. -/
theorem noGlobalMax_inverse :
    ¬ ∃ x : Rat, IsGlobalMaxOn inverseReal (Set.Ioo (0 : Rat) 1) x := by
  lynth

-- Axiom footprint checks.
/-- info: 'IntervalArith.ExtremaAnswer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExtremaAnswer
/-- info: 'IntervalArith.IsGlobalMinOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsGlobalMinOn
/-- info: 'IntervalArith.IsGlobalMaxOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsGlobalMaxOn
/-- info: 'IntervalArith.ApproxGlobalMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ApproxGlobalMin
/-- info: 'IntervalArith.ApproxGlobalMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ApproxGlobalMax
/-- info: 'IntervalArith.IsLocalMinOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLocalMinOn
/-- info: 'IntervalArith.IsLocalMaxOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLocalMaxOn
/-- info: 'IntervalArith.ApproxLocalMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ApproxLocalMin
/-- info: 'IntervalArith.ApproxLocalMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ApproxLocalMax
/-- info: 'IntervalArith.GlobalMinOrNoMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GlobalMinOrNoMin
/-- info: 'IntervalArith.GlobalMaxOrNoMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GlobalMaxOrNoMax
/-- info: 'IntervalArith.LocalMinOrNoLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LocalMinOrNoLocal
/-- info: 'IntervalArith.LocalMaxOrNoLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LocalMaxOrNoLocal
/-- info: 'IntervalArith.extremaTolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms extremaTolerance
/-- info: 'IntervalArith.quadraticMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadraticMin
/-- info: 'IntervalArith.sqrtCompositionMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqrtCompositionMin
/-- info: 'IntervalArith.arctanCompositionMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arctanCompositionMax
/-- info: 'IntervalArith.logLocalMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logLocalMin
/-- info: 'IntervalArith.tanhLocalMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tanhLocalMax
/-- info: 'IntervalArith.identityReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identityReal
/-- info: 'IntervalArith.negIdentityReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negIdentityReal
/-- info: 'IntervalArith.cubeReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubeReal
/-- info: 'IntervalArith.inverseReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inverseReal
/-- info: 'IntervalArith.quadraticGlobalMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadraticGlobalMin
/-- info: 'IntervalArith.sqrtCompositionGlobalMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqrtCompositionGlobalMin
/-- info: 'IntervalArith.arctanCompositionGlobalMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arctanCompositionGlobalMax
/-- info: 'IntervalArith.logLocalMinimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logLocalMinimum
/-- info: 'IntervalArith.tanhLocalMaximum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tanhLocalMaximum
/-- info: 'IntervalArith.noGlobalMin_openUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noGlobalMin_openUnit
/-- info: 'IntervalArith.noGlobalMax_openUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noGlobalMax_openUnit
/-- info: 'IntervalArith.noLocalMin_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noLocalMin_cube
/-- info: 'IntervalArith.noLocalMax_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noLocalMax_cube
/-- info: 'IntervalArith.noGlobalMin_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noGlobalMin_inverse
/-- info: 'IntervalArith.noGlobalMax_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noGlobalMax_inverse

end IntervalArith
