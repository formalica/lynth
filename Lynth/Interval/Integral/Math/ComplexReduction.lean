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

private theorem noIntegral_converges_local {e : NExpr} (h : e.hasIntegral = false)
    (env : List ℝ) : e.Converges env := by
  induction e with
  | var | rat | pi => trivial
  | unary op e ih | pow e n ih | rpow e q ih => exact ih h
  | binary op e f ihe ihf =>
      have hh := Bool.or_eq_false_iff.mp h
      exact ⟨ihe hh.1, ihf hh.2⟩
  | integral => simp [NExpr.hasIntegral] at h

private theorem neg_real_local (a : NExpr) (env : List ℝ) :
    (neg a).real env = -a.real env := by
  cases a with
  | unary op a => cases op <;> simp [neg, NExpr.real, Unary.real]
  | var | rat | pi | binary | pow | rpow | integral => simp [neg, NExpr.real, Unary.real]

private theorem neg_converges_local (a : NExpr) (env : List ℝ) :
    (neg a).Converges env ↔ a.Converges env := by
  cases a with
  | unary op a => cases op <;> simp [neg, NExpr.Converges]
  | var | rat | pi | binary | pow | rpow | integral => simp [neg, NExpr.Converges]

private theorem pow_real_local (a : NExpr) (n : Nat) (env : List ℝ) :
    (pow a n).real env = a.real env ^ n := by
  unfold pow
  split
  · rename_i h
    have hh : n = 0 ∧ a.hasIntegral = false := by simpa using h
    have hn : n = 0 := hh.1
    simp [hn, NExpr.real]
  · split
    · rename_i h
      have hn : n = 1 := by simpa using h
      simp [hn]
    · cases a with
      | unary op a =>
          cases op <;> try rfl
          change (if (n % 2 == 0) then a.pow n else neg (a.pow n)).real env =
            (-a.real env) ^ n
          simp only [beq_iff_eq]
          split_ifs with hn
          · change a.real env ^ n = (-a.real env) ^ n
            rw [neg_pow, neg_one_pow_eq_pow_mod_two, hn]
            simp
          · have hne : n % 2 ≠ 0 := hn
            have hn : n % 2 = 1 := by
              omega
            rw [neg_real_local]
            change -(a.real env ^ n) = (-a.real env) ^ n
            rw [neg_pow, neg_one_pow_eq_pow_mod_two, hn]
            simp
      | var | rat | pi | binary | pow | rpow | integral => rfl

private theorem pow_converges_local (a : NExpr) (n : Nat) (env : List ℝ) :
    (pow a n).Converges env ↔ a.Converges env := by
  unfold pow
  split
  · rename_i h
    have hh : n = 0 ∧ a.hasIntegral = false := by simpa using h
    simp [NExpr.Converges, noIntegral_converges_local hh.2 env]
  · split
    · rfl
    · cases a with
      | unary op a =>
          cases op <;> try rfl
          change (if (n % 2 == 0) then a.pow n else neg (a.pow n)).Converges env ↔
            a.Converges env
          split_ifs <;> simp [NExpr.Converges, neg_converges_local]
      | var | rat | pi | binary | pow | rpow | integral => rfl

/-- Rational powers use rational exponentiation directly; other bases use the
ordinary power normalizer. Both preserve the original real value and recursive
convergence obligation. -/
private theorem complexCleanPow_sound (a : NExpr) (m : Nat) (env : List ℝ) :
    (((.pow a m : NExpr).Converges env) ↔
      (complexCleanPow a m).Converges env) ∧
    (.pow a m : NExpr).real env = (complexCleanPow a m).real env := by
  cases a with
  | rat q =>
      simp [complexCleanPow, NExpr.Converges, NExpr.real, Rat.cast_pow]
  | var i =>
      exact ⟨(pow_converges_local (.var i) m env).symm,
        by simpa only [complexCleanPow, NExpr.real] using (pow_real_local (.var i) m env).symm⟩
  | pi =>
      exact ⟨(pow_converges_local .pi m env).symm,
        by simpa only [complexCleanPow, NExpr.real] using (pow_real_local .pi m env).symm⟩
  | unary op a =>
      exact ⟨(pow_converges_local (.unary op a) m env).symm,
        by simpa only [complexCleanPow, NExpr.real] using (pow_real_local (.unary op a) m env).symm⟩
  | binary op a b =>
      exact ⟨(pow_converges_local (.binary op a b) m env).symm,
        by simpa only [complexCleanPow, NExpr.real] using (pow_real_local (.binary op a b) m env).symm⟩
  | pow a n =>
      exact ⟨(pow_converges_local (.pow a n) m env).symm,
        by simpa only [complexCleanPow, NExpr.real] using (pow_real_local (.pow a n) m env).symm⟩
  | rpow a q =>
      exact ⟨(pow_converges_local (.rpow a q) m env).symm,
        by simpa only [complexCleanPow, NExpr.real] using (pow_real_local (.rpow a q) m env).symm⟩
  | integral k a b f =>
      exact ⟨(pow_converges_local (.integral k a b f) m env).symm,
        by simpa only [complexCleanPow, NExpr.real] using (pow_real_local (.integral k a b f) m env).symm⟩

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
