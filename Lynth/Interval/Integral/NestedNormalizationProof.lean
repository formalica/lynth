module

import all Lynth.Interval.Integral.NestedHalflineProof

/-! Canonical half-line expressions preserve ordinary convergence and values. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl

def normalized (n : Nat) (e : Expr) : Expr :=
  match e with
  | .integral .right a b f =>
    if a.hasIntegral || b.hasIntegral then e else
      .integral .interval (.rat 0) (.rat 1) (transformed n .right a b f)
  | .integral .left a b f =>
    if a.hasIntegral || b.hasIntegral then e else
      .integral .interval (.rat 0) (.rat 1) (transformed n .left a b f)
  | _ => e

theorem key_expr (e : Expr) (env : Array Ival) :
    (key e env).expr = normalized env.size e := rfl

theorem normalized_semantics (e : Expr) (xs : List ℝ) (hs : e.scoped xs.length = true) :
    ((normalized xs.length e).Converges xs ↔ e.Converges xs) ∧
      (e.Converges xs → (normalized xs.length e).real xs = e.real xs) := by
  cases e with
  | var | rat | pi | unary | binary | pow | rpow => exact ⟨Iff.rfl,fun _ => rfl⟩
  | integral k a b f =>
    have hsa : a.scoped xs.length = true :=
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hs).1).1
    cases k <;> try exact ⟨Iff.rfl,fun _ => rfl⟩
    case right =>
      simp only [normalized]
      split
      · exact ⟨Iff.rfl,fun _ => rfl⟩
      · rename_i hn
        have hp : a.hasIntegral = false ∧ b.hasIntegral = false := by simpa using hn
        exact halfline_normalization true a b f xs hp.1 hp.2 hsa
    case left =>
      simp only [normalized]
      split
      · exact ⟨Iff.rfl,fun _ => rfl⟩
      · rename_i hn
        have hp : a.hasIntegral = false ∧ b.hasIntegral = false := by simpa using hn
        exact halfline_normalization false a b f xs hp.1 hp.2 hsa

end Lynth.Interval.Integral.Nested
