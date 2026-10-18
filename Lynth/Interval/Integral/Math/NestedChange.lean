import Lynth.Interval.Integral.Math.NestedSyntax
import Lynth.Interval.Integral.Math.NestedAnalysis

/-! Mathematical scope and substitution obligations for the pure nested
expression language. The complete dependency bundle is mirrored in /tmp/intgrl. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl

def Change.Admissible (how : Change) (kind : NDomain) : Prop :=
  match how with
  | .identity => False
  | .affine => kind.finite = true
  | .power n _ => kind.finite = true ∧ 0 < n
  | .right => kind = .right
  | .left => kind = .left

theorem transformed_scoped {n : Nat} {how : Change} {a b f : Expr}
    (ha : a.scoped n = true) (hb : b.scoped n = true) (hf : f.scoped (n+1) = true) :
    (transformed n how a b f).scoped (n+1) = true := by
  sorry

theorem formula_scoped {n : Nat} {kind : NDomain} {a b f : Expr} {form : Formula}
    (ha : a.scoped n = true) (hb : b.scoped n = true) (hf : f.scoped (n+1) = true)
    (h : formula n kind a b f = some form) :
    form.value.scoped n = true ∧ ∀ g ∈ form.nonnegative, g.scoped n = true := by
  sorry

theorem center_properties {n : Nat} {f : Expr} (hf : f.scoped (n+1) = true) :
    (center n f).scoped n = true ∧ (center n f).hasIntegral = false := by
  sorry

/-- The pointwise convergence predicate is transported together with the
integral value, so a divergent inner integral cannot become a default zero. -/
theorem transformed_integral_transport {xs : List ℝ} {kind : NDomain} {how : Change}
    {a b f : Expr} (hhow : how.Admissible kind)
    (hsa : a.scoped xs.length = true) (hsb : b.scoped xs.length = true)
    (hsf : f.scoped (xs.length+1) = true)
    (ha : a.Converges xs) (hb : b.Converges xs)
    (hab : kind.finite = true → kind ≠ .interval → a.real xs ≤ b.real xs)
    (hE : (NExpr.integral .interval (.rat 0) (.rat 1)
      (transformed xs.length how a b f)).Converges xs) :
    (NExpr.integral kind a b f).Converges xs ∧
      (NExpr.integral kind a b f).real xs =
        (NExpr.integral .interval (.rat 0) (.rat 1)
          (transformed xs.length how a b f)).real xs := by
  sorry

end Lynth.Interval.Integral.Nested
