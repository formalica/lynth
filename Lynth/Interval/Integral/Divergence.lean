module

public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Basic.Real.Basic
public import Lynth.Interval.Core.Ctx
public import Lynth.Interval.Integral.Eval
public import Lynth.Interval.Integral.Math.DivergenceRules
public import Lynth.Interval.Integral.Math.Integrand
public import Lynth.Interval.Num.Ival
import all Lynth.Interval.Integral.Cert
import all Lynth.Interval.Integral.Math.DivergenceRules
import all Lynth.Interval.Integral.SyntaxEq

/-! Proof-producing divergence checks, separate from quadrature failure. -/

namespace Lynth.Interval.Integral

open Intgrl

@[expose] public def termEq (a b : Term) : Bool := a == b

@[expose] public def leTermCheck (c : Ctx) (A B : Term) : Bool :=
  termEq A B || Ival.leB (evalR c A Ival.zero) (evalR c B Ival.zero)

@[expose] public def ltTermCheck (c : Ctx) (A B : Term) : Bool :=
  Ival.ltB (evalR c A Ival.zero) (evalR c B Ival.zero)

@[expose] public def conditionCheck (c : Ctx) (r : DivergenceRule) (kind : Region) (A B : Term) : Bool :=
  match r with
  | .invPower n =>
    if kind.isFinite then
      ltTermCheck c A B && leTermCheck c A (.rat 0) && leTermCheck c (.rat 0) B && n > 0
    else if kind == .univ then n > 0
    else n == 1 || (leTermCheck c A (.rat 0) && n > 0)
  | .shiftedInv q =>
    if kind.isFinite then
      ltTermCheck c A B && leTermCheck c A (.rat q) && leTermCheck c (.rat q) B
    else true
  | .tangent =>
    let P : Term := .binary .div .pi (.rat 2)
    if kind.isFinite then
      ltTermCheck c A B && leTermCheck c A P && leTermCheck c P B
    else true
  | _ => !kind.isFinite

@[expose] public def divergenceCheck (c : Ctx) (e A B : Term) (kind : Region) : Bool :=
  match classifyDivergence e with
  | some rule => conditionCheck c rule kind A B
  | none => false

theorem leTermCheck_sound {c : Ctx} (hc : c.Valid) {A B : Term}
    (h : leTermCheck c A B = true) : A.real 0 ≤ B.real 0 := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · have heq : A = B := by simpa [termEq] using h
    subst B
    exact le_rfl
  · exact Ival.le_of_leB (evalR_sound hc A Ival.mem_zero)
      (evalR_sound hc B Ival.mem_zero) h

theorem ltTermCheck_sound {c : Ctx} (hc : c.Valid) {A B : Term}
    (h : ltTermCheck c A B = true) : A.real 0 < B.real 0 :=
  Ival.lt_of_ltB (evalR_sound hc A Ival.mem_zero) (evalR_sound hc B Ival.mem_zero) h

theorem conditionCheck_sound {c : Ctx} (hc : c.Valid)
    {rule : DivergenceRule} {kind : Region} {A B : Term}
    (h : conditionCheck c rule kind A B = true) :
    rule.Condition kind (A.real 0) (B.real 0) := by
  cases rule with
  | invPower n =>
    by_cases hk : kind.isFinite = true
    · simp only [conditionCheck, hk, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [DivergenceRule.Condition, hk, ↓reduceIte]
      exact ⟨ltTermCheck_sound hc h.1.1.1, by simpa [Term.real] using leTermCheck_sound hc h.1.1.2,
        by simpa [Term.real] using leTermCheck_sound hc h.1.2, h.2⟩
    · have hk' : kind.isFinite = false := Bool.eq_false_iff.mpr hk
      by_cases hu : kind == .univ
      · simpa only [conditionCheck, DivergenceRule.Condition, hk', hu, ↓reduceIte, Bool.false_eq_true,
          decide_eq_true_eq] using h
      · simp only [conditionCheck, hk', hu, ↓reduceIte, Bool.false_eq_true,
          Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        simp only [DivergenceRule.Condition, hk', hu, Bool.false_eq_true, ↓reduceIte]
        exact h.imp id (fun h => ⟨by simpa [Term.real] using leTermCheck_sound hc h.1,h.2⟩)
  | shiftedInv q =>
    by_cases hk : kind.isFinite = true
    · simp only [conditionCheck, hk, ↓reduceIte, Bool.and_eq_true] at h
      simp only [DivergenceRule.Condition, hk, ↓reduceIte]
      exact ⟨ltTermCheck_sound hc h.1.1, by simpa [Term.real] using leTermCheck_sound hc h.1.2,
        by simpa [Term.real] using leTermCheck_sound hc h.2⟩
    · simp [DivergenceRule.Condition, hk]
  | tangent =>
    by_cases hk : kind.isFinite = true
    · simp only [conditionCheck, hk, ↓reduceIte, Bool.and_eq_true] at h
      simp only [DivergenceRule.Condition, hk, ↓reduceIte]
      exact ⟨ltTermCheck_sound hc h.1.1,
        by simpa [Term.real, Binary.real] using leTermCheck_sound hc h.1.2,
        by simpa [Term.real, Binary.real] using leTermCheck_sound hc h.2⟩
    · simp [DivergenceRule.Condition, hk]
  | constant q | linear | sine | exponential =>
    simpa only [conditionCheck, DivergenceRule.Condition, Bool.not_eq_true, Bool.not_eq_true'] using h

theorem divergenceCheck_sound {c : Ctx} (hc : c.Valid) {e A B : Term} {kind : Region}
    (h : divergenceCheck c e A B kind = true) :
    ¬ kind.Converges e.real (A.real 0) (B.real 0) := by
  cases he : classifyDivergence e with
  | none => simp [divergenceCheck, he] at h
  | some rule =>
    have hh : conditionCheck c rule kind A B = true := by simpa [divergenceCheck, he] using h
    exact divergenceRule_sound he (conditionCheck_sound hc hh)

public theorem not_converges_of_check {f : ℝ → ℝ} {a b : ℝ} {e A B : Term} {c : Ctx}
    {kind : Region} (hc : c.Valid) (hf : ∀ x, f x = e.real x)
    (ha : a = A.real 0) (hb : b = B.real 0)
    (h : divergenceCheck c e A B kind = true) :
    ¬ kind.Converges f a b := by
  obtain rfl : f = e.real := funext hf
  subst a; subst b
  exact divergenceCheck_sound hc h

end Lynth.Interval.Integral
