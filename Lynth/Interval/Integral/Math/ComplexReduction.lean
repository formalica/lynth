import Lynth.Interval.Integral.Math.ComplexBranch

/-! Exact affine-phase antiderivatives used before complex quadrature.
This mathematical syntax transformation has no numerical dependencies. -/
namespace Intgrl
open Lynth.Interval.Integral.Nested

/-- Return the intercept and slope of a real affine expression in level n.
Coefficients contain no integrals and do not depend on the bound variable. -/
def complexAffine (n : Nat) (e : NExpr) : Option (NExpr × NExpr) := do
  if !e.uses n && !e.hasIntegral then return (e,.rat 0)
  match e with
  | .var i => if i == n then some (.rat 0,.rat 1) else none
  | .unary .neg a =>
      let (a,b) ← complexAffine n a
      return (neg a,neg b)
  | .binary op a b =>
      let (a₀,a₁) ← complexAffine n a
      let (b₀,b₁) ← complexAffine n b
      match op with
      | .add => return (add a₀ b₀,add a₁ b₁)
      | .sub => return (sub a₀ b₀,sub a₁ b₁)
      | .mul =>
          if a₁ == .rat 0 then return (mul a₀ b₀,mul a₀ b₁)
          if b₁ == .rat 0 then return (mul a₀ b₀,mul a₁ b₀)
          none
      | .div =>
          if b₁ == .rat 0 then some (div a₀ b₀,div a₁ b₀) else none
      | _ => none
  | _ => none

private def affinePrimitive (op : Unary) (a b p q : NExpr) : NExpr :=
  let atA := add p (mul q a)
  let atB := add p (mul q b)
  let width := sub b a
  if q == .rat 0 then mul width (.unary op p) else
    let num := match op with
      | .sin => sub (.unary .cos atA) (.unary .cos atB)
      | .cos => sub (.unary .sin atB) (.unary .sin atA)
      | _ => sub (.unary .exp atB) (.unary .exp atA)
    let ordinary := div num q
    match q with
    | .rat _ => ordinary
    | _ => add ordinary (mul (CParts.isZero q) (mul width (.unary op p)))

/-- Linearity is applied only to finite interval integrals. A remaining
integral retains its convergence obligation, even with a zero multiplier. -/
def complexFinitePrimitive (n : Nat) (a b : NExpr) (f : NExpr) : NExpr :=
  match f with
  | .binary .add f g => add (complexFinitePrimitive n a b f) (complexFinitePrimitive n a b g)
  | .binary .sub f g => sub (complexFinitePrimitive n a b f) (complexFinitePrimitive n a b g)
  | .unary .neg f => neg (complexFinitePrimitive n a b f)
  | .binary .mul f g =>
      if !f.uses n && !f.hasIntegral then mul f (complexFinitePrimitive n a b g)
      else if !g.uses n && !g.hasIntegral then mul (complexFinitePrimitive n a b f) g
      else .integral .interval a b (.binary .mul f g)
  | .binary .div f g =>
      if !g.uses n && !g.hasIntegral then div (complexFinitePrimitive n a b f) g
      else .integral .interval a b (.binary .div f g)
  | .unary op f =>
      if op == .sin || op == .cos || op == .exp then
        match complexAffine n f with
        | some (p,q) => affinePrimitive op a b p q
        | none => .integral .interval a b (.unary op f)
      else .integral .interval a b (.unary op f)
  | f => .integral .interval a b f

def NExpr.reduceComplexIntegral (n : Nat) : NExpr → NExpr
  | .unary op a => complexCleanUnary op (a.reduceComplexIntegral n)
  | .binary op a b => complexCleanBinary op (a.reduceComplexIntegral n) (b.reduceComplexIntegral n)
  | .pow a m => complexCleanPow (a.reduceComplexIntegral n) m
  | .rpow a q => .rpow (a.reduceComplexIntegral n) q
  | .integral k a b f =>
      let A := a.reduceComplexIntegral n
      let B := b.reduceComplexIntegral n
      let F := f.reduceComplexIntegral (n+1)
      if k == .interval && !A.hasIntegral && !B.hasIntegral then
        match complexBranchIntegral n A B F with
        | some G => G
        | none => complexFinitePrimitive n A B F
      else .integral k A B F
  | e => e

/-- Exact primitives and linearity preserve the original recursive ordinary
convergence. The real variable remains at level env.length throughout. -/
theorem NExpr.reduceComplexIntegral_sound {e : NExpr} {env : List ℝ}
    (hs : e.scoped env.length = true)
    (h : (e.reduceComplexIntegral env.length).Converges env) :
    e.Converges env ∧ e.real env = (e.reduceComplexIntegral env.length).real env := by
  sorry

theorem NExpr.reduceComplexIntegral_result {e : NExpr} {q : ℚ} {tol : ℝ}
    (hs : e.scoped 0 = true)
    (h : (e.reduceComplexIntegral 0).Converges [] ∧
      |(e.reduceComplexIntegral 0).real []-(q:ℝ)| < tol) :
    e.Converges [] ∧ |e.real []-(q:ℝ)| < tol := by
  have hh := e.reduceComplexIntegral_sound (env := []) hs h.1
  refine ⟨hh.1,?_⟩
  rw [hh.2]
  exact h.2
end Intgrl
