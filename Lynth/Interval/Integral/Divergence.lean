import Lynth.Interval.Integral.Cert
import Lynth.Interval.Integral.Math.DivergenceRules

/-! Proof-producing divergence checks, separate from quadrature failure. -/

namespace Lynth.Interval.Integral

open Intgrl

def termEq (a b : Term) : Bool := a == b

def leTermCheck (c : Ctx) (A B : Term) : Bool :=
  termEq A B || Ival.leB (evalR c A Ival.zero) (evalR c B Ival.zero)

def ltTermCheck (c : Ctx) (A B : Term) : Bool :=
  Ival.ltB (evalR c A Ival.zero) (evalR c B Ival.zero)

def conditionCheck (c : Ctx) (r : DivergenceRule) (kind : Region) (A B : Term) : Bool :=
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

def divergenceCheck (c : Ctx) (e A B : Term) (kind : Region) : Bool :=
  match classifyDivergence e with
  | some rule => conditionCheck c rule kind A B
  | none => false

theorem conditionCheck_sound {c : Ctx} (hc : c.Valid)
    {rule : DivergenceRule} {kind : Region} {A B : Term}
    (h : conditionCheck c rule kind A B = true) :
    rule.Condition kind (A.real 0) (B.real 0) := by
  sorry

theorem divergenceCheck_sound {c : Ctx} (hc : c.Valid) {e A B : Term} {kind : Region}
    (h : divergenceCheck c e A B kind = true) :
    ¬ kind.Converges e.real (A.real 0) (B.real 0) := by
  cases he : classifyDivergence e with
  | none => simp [divergenceCheck, he] at h
  | some rule =>
    have hh : conditionCheck c rule kind A B = true := by simpa [divergenceCheck, he] using h
    exact divergenceRule_sound he (conditionCheck_sound hc hh)

theorem not_converges_of_check {f : ℝ → ℝ} {a b : ℝ} {e A B : Term} {c : Ctx}
    {kind : Region} (hc : c.Valid) (hf : ∀ x, f x = e.real x)
    (ha : a = A.real 0) (hb : b = B.real 0)
    (h : divergenceCheck c e A B kind = true) :
    ¬ kind.Converges f a b := by
  obtain rfl : f = e.real := funext hf
  subst a; subst b
  exact divergenceCheck_sound hc h

end Lynth.Interval.Integral
