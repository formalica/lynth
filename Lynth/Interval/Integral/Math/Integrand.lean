import Mathlib

/-!
Small mathematical expression language used by the integration compiler.
This module depends only on Mathlib; its proof obligations are mirrored in
/tmp/intgrl/Integrand.lean. No interval encodings or tactic internals occur here.
-/

namespace Intgrl

inductive Region where
  | interval | icc | ioc | ico | ioo | ioi | ici | univ
deriving Repr, BEq, Inhabited

noncomputable def Region.set : Region → ℝ → ℝ → Set ℝ
  | .interval, a, b => Set.uIcc a b
  | .icc, a, b => Set.Icc a b | .ioc, a, b => Set.Ioc a b
  | .ico, a, b => Set.Ico a b | .ioo, a, b => Set.Ioo a b
  | .ioi, a, _ => Set.Ioi a | .ici, a, _ => Set.Ici a
  | .univ, _, _ => Set.univ

noncomputable def Region.Converges (k : Region) (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  match k with
  | .interval => IntervalIntegrable f MeasureTheory.volume a b
  | _ => MeasureTheory.IntegrableOn f (k.set a b) MeasureTheory.volume

noncomputable def Region.value (k : Region) (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  match k with
  | .interval => ∫ x in a..b, f x
  | _ => ∫ x in k.set a b, f x

inductive Unary where
  | neg | inv | exp | sin | cos | sinh | cosh | log | sqrt | abs | floor | atan
deriving Repr, BEq, Inhabited

inductive Binary where
  | add | sub | mul | div | max | min
deriving Repr, BEq, Inhabited

inductive Term where
  | var
  | rat (q : ℚ)
  | pi
  | unary (op : Unary) (a : Term)
  | binary (op : Binary) (a b : Term)
  | pow (a : Term) (n : ℕ)
  | rpow (a : Term) (q : ℚ)
deriving Repr, BEq, Inhabited

noncomputable def Unary.real : Unary → ℝ → ℝ
  | .neg => Neg.neg | .inv => Inv.inv | .exp => Real.exp
  | .sin => Real.sin | .cos => Real.cos | .sinh => Real.sinh | .cosh => Real.cosh
  | .log => Real.log | .sqrt => Real.sqrt | .abs => fun x => |x|
  | .floor => fun x => (⌊x⌋ : ℤ) | .atan => Real.arctan

noncomputable def Binary.real : Binary → ℝ → ℝ → ℝ
  | .add => (· + ·) | .sub => (· - ·) | .mul => (· * ·)
  | .div => (· / ·) | .max => Max.max | .min => Min.min

noncomputable def Term.real : Term → ℝ → ℝ
  | .var, x => x | .rat q, _ => q | .pi, _ => Real.pi
  | .unary op a, x => op.real (a.real x)
  | .binary op a b, x => op.real (a.real x) (b.real x)
  | .pow a n, x => a.real x ^ n
  | .rpow a q, x => a.real x ^ (q : ℝ)

noncomputable def Unary.complex : Unary → ℂ → ℂ
  | .neg => Neg.neg | .inv => Inv.inv | .exp => Complex.exp
  | .sin => Complex.sin | .cos => Complex.cos
  | .sinh => Complex.sinh | .cosh => Complex.cosh
  | .log => Complex.log | .sqrt => Complex.sqrt
  | .atan => Complex.arctan
  | .abs => id | .floor => fun _ => 0

noncomputable def Binary.complex : Binary → ℂ → ℂ → ℂ
  | .add => (· + ·) | .sub => (· - ·) | .mul => (· * ·) | .div => (· / ·)
  | .max => fun a _ => a | .min => fun a _ => a

noncomputable def Term.complex : Term → ℂ → ℂ
  | .var, z => z | .rat q, _ => q | .pi, _ => Real.pi
  | .unary op a, z => op.complex (a.complex z)
  | .binary op a b, z => op.complex (a.complex z) (b.complex z)
  | .pow a n, z => a.complex z ^ n
  | .rpow a q, z => a.complex z ^ ((q : ℝ) : ℂ)

/-- Sufficient local domain conditions for a single holomorphic extension. -/
def Term.Regular : Term → Set ℂ → Prop
  | .var, _ | .rat _, _ | .pi, _ => True
  | .pow a _, s => a.Regular s
  | .rpow a _, s => a.Regular s ∧ ∀ z ∈ s, 0 < (a.complex z).re
  | .unary op a, s =>
      a.Regular s ∧ match op with
      | .inv => ∀ z ∈ s, a.complex z ≠ 0
      | .log | .sqrt => ∀ z ∈ s, 0 < (a.complex z).re
      | .abs | .floor | .atan => False
      | _ => True
  | .binary op a b, s =>
      a.Regular s ∧ b.Regular s ∧ match op with
      | .div => ∀ z ∈ s, b.complex z ≠ 0
      | .max | .min => False
      | _ => True

theorem Term.measurable (e : Term) : Measurable e.real := by
  sorry

theorem Term.analytic {e : Term} {s : Set ℂ} (h : e.Regular s) :
    AnalyticOnNhd ℂ e.complex s := by
  sorry

theorem Term.agrees {e : Term} {s : Set ℂ} (h : e.Regular s)
    {x : ℝ} (hx : (x : ℂ) ∈ s) :
    e.complex x = (e.real x : ℂ) := by
  sorry

end Intgrl
