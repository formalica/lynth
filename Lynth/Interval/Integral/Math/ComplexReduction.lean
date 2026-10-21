import Lynth.Interval.Integral.Math.ComplexBranch
import Lynth.Interval.Integral.Math.ComplexLemmasProofs

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
theorem complexAffine_sound {n : Nat} {env : List ℝ} (hn : env.length = n) :
    ∀ (e p q : NExpr), complexAffine n e = some (p, q) →
      e.hasIntegral = false ∧ ∀ x, e.real (env ++ [x]) = p.real env + q.real env * x := by
  have hconst : ∀ e : NExpr, (!e.uses n && !e.hasIntegral) = true →
      e.hasIntegral = false ∧ ∀ x, e.real (env ++ [x]) = e.real env + (NExpr.rat 0).real env * x := by
    intro e he
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at he
    refine ⟨he.2, fun x => ?_⟩
    rw [noInt_real_indep he.2 he.1 hn x]
    simp [NExpr.real]
  intro e
  induction e with
  | var i =>
    intro p q h
    unfold complexAffine at h
    split at h
    · rename_i hc
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hconst _ hc
    · simp only at h
      split_ifs at h with hi
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [beq_iff_eq] at hi
      subst hi
      refine ⟨rfl, fun x => ?_⟩
      simp [NExpr.real, ← hn]
  | rat c =>
    intro p q h
    unfold complexAffine at h
    split at h
    · rename_i hc
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hconst _ hc
    · simp at h
  | pi =>
    intro p q h
    unfold complexAffine at h
    split at h
    · rename_i hc
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hconst _ hc
    · simp at h
  | unary op a ih =>
    intro p q h
    unfold complexAffine at h
    split at h
    · rename_i hc
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hconst _ hc
    · cases op <;> simp only at h
      all_goals try simp at h
      obtain ⟨⟨a0, a1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hai, hav⟩ := ih _ _ ha
      refine ⟨by simpa [NExpr.hasIntegral] using hai, fun x => ?_⟩
      simp only [NExpr.real, Unary.real, neg_real, hav]
      ring
  | binary op a b iha ihb =>
    intro p q h
    unfold complexAffine at h
    split at h
    · rename_i hc
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hconst _ hc
    · simp only at h
      obtain ⟨⟨a0, a1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨b0, b1⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨hai, hav⟩ := iha _ _ ha
      obtain ⟨hbi, hbv⟩ := ihb _ _ hb
      have hI : (NExpr.binary op a b).hasIntegral = false := by
        simp [NExpr.hasIntegral, hai, hbi]
      cases op <;> simp only at h
      · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hI, fun x => ?_⟩
        simp only [NExpr.real, Binary.real, add_real, hav, hbv]; ring
      · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hI, fun x => ?_⟩
        simp only [NExpr.real, Binary.real, sub_real, hav, hbv]; ring
      · split_ifs at h with h1 h2
        · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [beq_iff_eq] at h1; subst h1
          refine ⟨hI, fun x => ?_⟩
          simp only [NExpr.real, Binary.real, mul_real, hav, hbv, Rat.cast_zero]; ring
        · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [beq_iff_eq] at h2; subst h2
          refine ⟨hI, fun x => ?_⟩
          simp only [NExpr.real, Binary.real, mul_real, hav, hbv, Rat.cast_zero]; ring
      · split_ifs at h with h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [beq_iff_eq] at h1; subst h1
        refine ⟨hI, fun x => ?_⟩
        simp only [NExpr.real, Binary.real, div_real, hav, hbv, Rat.cast_zero]; ring
      · simp at h
      · simp at h
  | pow a m ih =>
    intro p q h
    unfold complexAffine at h
    split at h
    · rename_i hc
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hconst _ hc
    · simp at h
  | rpow a c ih =>
    intro p q h
    unfold complexAffine at h
    split at h
    · rename_i hc
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hconst _ hc
    · simp at h
  | integral k a b f iha ihb ihf =>
    intro p q h
    unfold complexAffine at h
    split at h
    · rename_i hc
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hconst _ hc
    · simp at h

theorem int_sin_aff (P Q α β : ℝ) (hQ : Q ≠ 0) :
    ∫ x in α..β, Real.sin (P + Q * x) = (Real.cos (P + Q * α) - Real.cos (P + Q * β)) / Q := by
  rw [intervalIntegral.integral_comp_add_mul (fun x => Real.sin x) hQ, integral_sin]
  simp only [smul_eq_mul]; field_simp

theorem int_cos_aff (P Q α β : ℝ) (hQ : Q ≠ 0) :
    ∫ x in α..β, Real.cos (P + Q * x) = (Real.sin (P + Q * β) - Real.sin (P + Q * α)) / Q := by
  rw [intervalIntegral.integral_comp_add_mul (fun x => Real.cos x) hQ, integral_cos]
  simp only [smul_eq_mul]; field_simp

theorem int_exp_aff (P Q α β : ℝ) (hQ : Q ≠ 0) :
    ∫ x in α..β, Real.exp (P + Q * x) = (Real.exp (P + Q * β) - Real.exp (P + Q * α)) / Q := by
  rw [intervalIntegral.integral_comp_add_mul (fun x => Real.exp x) hQ, integral_exp]
  simp only [smul_eq_mul]; field_simp

theorem affinePrimitive_real (op : Unary) (hop : op = .sin ∨ op = .cos ∨ op = .exp)
    (A B p q : NExpr) (env : List ℝ) :
    (affinePrimitive op A B p q).real env =
      ∫ x in A.real env..B.real env, op.real (p.real env + q.real env * x) := by
  rcases hop with rfl | rfl | rfl
  · unfold affinePrimitive
    simp only
    split_ifs with hq
    · simp only [beq_iff_eq] at hq
      subst hq
      rw [mul_real, sub_real]
      simp [NExpr.real, Unary.real]
    · split
      · rename_i c
        have hc : (c : ℝ) ≠ 0 := by
          intro h0; apply hq; simp at h0; simp [h0]
        simp only [div_real, sub_real, NExpr.real, Unary.real, add_real, mul_real]
        rw [int_sin_aff _ _ _ _ hc]
      · simp only [add_real, div_real, sub_real, NExpr.real, Unary.real, mul_real, isZero_real]
        by_cases hQ : q.real env = 0
        · simp [hQ]
        · rw [int_sin_aff _ _ _ _ hQ]; simp [hQ]
  · unfold affinePrimitive
    simp only
    split_ifs with hq
    · simp only [beq_iff_eq] at hq
      subst hq
      rw [mul_real, sub_real]
      simp [NExpr.real, Unary.real]
    · split
      · rename_i c
        have hc : (c : ℝ) ≠ 0 := by
          intro h0; apply hq; simp at h0; simp [h0]
        simp only [div_real, sub_real, NExpr.real, Unary.real, add_real, mul_real]
        rw [int_cos_aff _ _ _ _ hc]
      · simp only [add_real, div_real, sub_real, NExpr.real, Unary.real, mul_real, isZero_real]
        by_cases hQ : q.real env = 0
        · simp [hQ]
        · rw [int_cos_aff _ _ _ _ hQ]; simp [hQ]
  · unfold affinePrimitive
    simp only
    split_ifs with hq
    · simp only [beq_iff_eq] at hq
      subst hq
      rw [mul_real, sub_real]
      simp [NExpr.real, Unary.real]
    · split
      · rename_i c
        have hc : (c : ℝ) ≠ 0 := by
          intro h0; apply hq; simp at h0; simp [h0]
        simp only [div_real, sub_real, NExpr.real, Unary.real, add_real, mul_real]
        rw [int_exp_aff _ _ _ _ hc]
      · simp only [add_real, div_real, sub_real, NExpr.real, Unary.real, mul_real, isZero_real]
        by_cases hQ : q.real env = 0
        · simp [hQ]
        · rw [int_exp_aff _ _ _ _ hQ]; simp [hQ]

theorem intervalIntegral_converges_iff (A B F : NExpr) (env : List ℝ) :
    (NExpr.integral .interval A B F).Converges env ↔
      A.Converges env ∧ B.Converges env ∧
      IntervalIntegrable (fun x => F.real (env ++ [x])) MeasureTheory.volume
        (A.real env) (B.real env) ∧
      ∀ x ∈ Set.uIoo (A.real env) (B.real env), F.Converges (env ++ [x]) := Iff.rfl

theorem intervalIntegral_real (A B F : NExpr) (env : List ℝ) :
    (NExpr.integral .interval A B F).real env =
      ∫ x in A.real env..B.real env, F.real (env ++ [x]) := rfl

theorem unary_affine_case (op : Unary) (hop : op = .sin ∨ op = .cos ∨ op = .exp)
    {n : Nat} {A B f : NExpr} {env : List ℝ} (hn : env.length = n)
    (hAc : A.Converges env) (hBc : B.Converges env)
    (h : (match complexAffine n f with
      | some (p, q) => affinePrimitive op A B p q
      | none => NExpr.integral .interval A B (.unary op f)).Converges env) :
    (NExpr.integral .interval A B (.unary op f)).Converges env ∧
      (NExpr.integral .interval A B (.unary op f)).real env =
        (match complexAffine n f with
          | some (p, q) => affinePrimitive op A B p q
          | none => NExpr.integral .interval A B (.unary op f)).real env := by
  cases heq : complexAffine n f with
  | none =>
    simp only [heq] at h ⊢
    first | exact ⟨h, rfl⟩ | exact ⟨h, trivial⟩
  | some pq =>
    obtain ⟨p, q⟩ := pq
    simp only [heq] at h ⊢
    obtain ⟨hfi, hfv⟩ := complexAffine_sound hn f p q heq
    have hfun : (fun x => (NExpr.unary op f).real (env ++ [x])) =
        fun x => op.real (p.real env + q.real env * x) := by
      funext x; simp only [NExpr.real, hfv]
    have hcont : Continuous (fun x => op.real (p.real env + q.real env * x)) := by
      rcases hop with rfl | rfl | rfl <;> simp only [Unary.real] <;> fun_prop
    refine ⟨⟨hAc, hBc, ?_, fun x _ => noIntegral_converges (by simpa [NExpr.hasIntegral] using hfi) _⟩, ?_⟩
    · rw [hfun]; exact hcont.intervalIntegrable _ _
    · rw [intervalIntegral_real, hfun, affinePrimitive_real op hop]

theorem finitePrimitive_sound {n : Nat} {A B : NExpr} {env : List ℝ} (hn : env.length = n)
    (hA : A.hasIntegral = false) (hB : B.hasIntegral = false) (F : NExpr)
    (h : (complexFinitePrimitive n A B F).Converges env) :
    (NExpr.integral .interval A B F).Converges env ∧
      (NExpr.integral .interval A B F).real env = (complexFinitePrimitive n A B F).real env := by
  have hAc := noIntegral_converges hA env
  have hBc := noIntegral_converges hB env
  induction F with
  | var i => exact ⟨h, rfl⟩
  | rat c => exact ⟨h, rfl⟩
  | pi => exact ⟨h, rfl⟩
  | pow a m ih => exact ⟨h, rfl⟩
  | rpow a c ih => exact ⟨h, rfl⟩
  | integral k a b f iha ihb ihf => exact ⟨h, rfl⟩
  | unary op f ih =>
    cases op
    case neg =>
      simp only [complexFinitePrimitive] at h ⊢
      rw [neg_converges] at h
      obtain ⟨hc, hv⟩ := ih h
      rw [intervalIntegral_converges_iff] at hc ⊢
      obtain ⟨-, -, hi, hx⟩ := hc
      refine ⟨⟨hAc, hBc, ?_, hx⟩, ?_⟩
      · exact hi.neg
      · rw [neg_real, ← hv, intervalIntegral_real, intervalIntegral_real]
        simp [NExpr.real, Unary.real, intervalIntegral.integral_neg]
    case sin =>
      simp only [complexFinitePrimitive] at h ⊢
      split_ifs at h ⊢ with hc
      · exact unary_affine_case .sin (by simp) hn hAc hBc h
      · exact absurd (by decide) hc
    case cos =>
      simp only [complexFinitePrimitive] at h ⊢
      split_ifs at h ⊢ with hc
      · exact unary_affine_case .cos (by simp) hn hAc hBc h
      · exact absurd (by decide) hc
    case exp =>
      simp only [complexFinitePrimitive] at h ⊢
      split_ifs at h ⊢ with hc
      · exact unary_affine_case .exp (by simp) hn hAc hBc h
      · exact absurd (by decide) hc
    all_goals
      simp only [complexFinitePrimitive] at h ⊢
      split_ifs at h ⊢ with hc
      · exact absurd hc (by decide)
      · exact ⟨h, rfl⟩
  | binary op f g ihf ihg =>
    cases op
    case add =>
      simp only [complexFinitePrimitive] at h ⊢
      rw [add_converges] at h
      obtain ⟨hcf, hvf⟩ := ihf h.1
      obtain ⟨hcg, hvg⟩ := ihg h.2
      rw [intervalIntegral_converges_iff] at hcf hcg ⊢
      refine ⟨⟨hAc, hBc, hcf.2.2.1.add hcg.2.2.1,
        fun x hx => ⟨hcf.2.2.2 x hx, hcg.2.2.2 x hx⟩⟩, ?_⟩
      rw [add_real, ← hvf, ← hvg]
      simp only [NExpr.real, Binary.real]
      exact intervalIntegral.integral_add hcf.2.2.1 hcg.2.2.1
    case sub =>
      simp only [complexFinitePrimitive] at h ⊢
      rw [sub_converges] at h
      obtain ⟨hcf, hvf⟩ := ihf h.1
      obtain ⟨hcg, hvg⟩ := ihg h.2
      rw [intervalIntegral_converges_iff] at hcf hcg ⊢
      refine ⟨⟨hAc, hBc, hcf.2.2.1.sub hcg.2.2.1,
        fun x hx => ⟨hcf.2.2.2 x hx, hcg.2.2.2 x hx⟩⟩, ?_⟩
      rw [sub_real, ← hvf, ← hvg]
      simp only [NExpr.real, Binary.real]
      exact intervalIntegral.integral_sub hcf.2.2.1 hcg.2.2.1
    case mul =>
      simp only [complexFinitePrimitive] at h ⊢
      split_ifs at h ⊢ with h1 h2
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
        rw [mul_converges] at h
        obtain ⟨hcg, hvg⟩ := ihg h.2
        have hfc : ∀ x, f.real (env ++ [x]) = f.real env := noInt_real_indep h1.2 h1.1 hn
        rw [intervalIntegral_converges_iff] at hcg ⊢
        have hfun : (fun x => (NExpr.binary .mul f g).real (env ++ [x])) =
            fun x => f.real env * g.real (env ++ [x]) := by
          funext x; simp only [NExpr.real, Binary.real, hfc]
        refine ⟨⟨hAc, hBc, ?_, fun x hx => ⟨noIntegral_converges h1.2 _, hcg.2.2.2 x hx⟩⟩, ?_⟩
        · rw [hfun]; exact hcg.2.2.1.const_mul _
        · rw [mul_real, ← hvg, intervalIntegral_real, hfun, intervalIntegral_real]
          exact intervalIntegral.integral_const_mul _ _
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
        rw [mul_converges] at h
        obtain ⟨hcf, hvf⟩ := ihf h.1
        have hgc : ∀ x, g.real (env ++ [x]) = g.real env := noInt_real_indep h2.2 h2.1 hn
        rw [intervalIntegral_converges_iff] at hcf ⊢
        have hfun : (fun x => (NExpr.binary .mul f g).real (env ++ [x])) =
            fun x => f.real (env ++ [x]) * g.real env := by
          funext x; simp only [NExpr.real, Binary.real, hgc]
        refine ⟨⟨hAc, hBc, ?_, fun x hx => ⟨hcf.2.2.2 x hx, noIntegral_converges h2.2 _⟩⟩, ?_⟩
        · rw [hfun]; exact hcf.2.2.1.mul_const _
        · rw [mul_real, ← hvf, intervalIntegral_real, hfun, intervalIntegral_real]
          exact intervalIntegral.integral_mul_const _ _
      · exact ⟨h, rfl⟩
    case div =>
      simp only [complexFinitePrimitive] at h ⊢
      split_ifs at h ⊢ with h2
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
        rw [div_converges] at h
        obtain ⟨hcf, hvf⟩ := ihf h.1
        have hgc : ∀ x, g.real (env ++ [x]) = g.real env := noInt_real_indep h2.2 h2.1 hn
        rw [intervalIntegral_converges_iff] at hcf ⊢
        have hfun : (fun x => (NExpr.binary .div f g).real (env ++ [x])) =
            fun x => f.real (env ++ [x]) / g.real env := by
          funext x; simp only [NExpr.real, Binary.real, hgc]
        refine ⟨⟨hAc, hBc, ?_, fun x hx => ⟨hcf.2.2.2 x hx, noIntegral_converges h2.2 _⟩⟩, ?_⟩
        · rw [hfun]; exact hcf.2.2.1.div_const _
        · rw [div_real, ← hvf, intervalIntegral_real, hfun, intervalIntegral_real]
          exact intervalIntegral.integral_div _ _
      · exact ⟨h, rfl⟩
    case max => exact ⟨h, rfl⟩
    case min => exact ⟨h, rfl⟩

theorem integral_transfer {k : NDomain} {a b f A B F : NExpr} {env : List ℝ}
    (hA : A.Converges env → a.Converges env ∧ a.real env = A.real env)
    (hB : B.Converges env → b.Converges env ∧ b.real env = B.real env)
    (hF : ∀ x, F.Converges (env ++ [x]) →
      f.Converges (env ++ [x]) ∧ f.real (env ++ [x]) = F.real (env ++ [x]))
    (h : (NExpr.integral k A B F).Converges env) :
    (NExpr.integral k a b f).Converges env ∧
      (NExpr.integral k a b f).real env = (NExpr.integral k A B F).real env := by
  obtain ⟨hAc, hBc, hk, hx⟩ := h
  obtain ⟨hac, hav⟩ := hA hAc
  obtain ⟨hbc, hbv⟩ := hB hBc
  have heq : ∀ x ∈ (match k with
        | .right => Set.Ioi (A.real env)
        | .left => Set.Iio (A.real env)
        | .whole => Set.univ
        | .interval => Set.uIoo (A.real env) (B.real env)
        | _ => Set.Ioo (A.real env) (B.real env)),
      (fun x => f.real (env ++ [x])) x = (fun x => F.real (env ++ [x])) x :=
    fun x hxs => (hF x (hx x hxs)).2
  have hkc := kind_congr heq
  refine ⟨⟨hac, hbc, ?_, ?_⟩, ?_⟩
  · simp only [hav, hbv]; exact hkc.1.2 hk
  · simp only [hav, hbv]; exact fun x hxs => (hF x (hx x hxs)).1
  · simp only [NExpr.real, hav, hbv]; exact hkc.2

/-- Exact primitives and linearity preserve the original recursive ordinary
convergence. The real variable remains at level env.length throughout. -/

theorem NExpr.reduceComplexIntegral_sound {e : NExpr} {env : List ℝ}
    (hs : e.scoped env.length = true)
    (h : (e.reduceComplexIntegral env.length).Converges env) :
    e.Converges env ∧ e.real env = (e.reduceComplexIntegral env.length).real env := by
  induction e generalizing env with
  | var i => exact ⟨h, rfl⟩
  | rat c => exact ⟨h, rfl⟩
  | pi => exact ⟨h, rfl⟩
  | unary op a ih =>
    simp only [NExpr.scoped] at hs
    simp only [NExpr.reduceComplexIntegral] at h ⊢
    obtain ⟨hv, hc⟩ := cleanUnary_sound op (a.reduceComplexIntegral env.length) env
    obtain ⟨iha, ihv⟩ := ih hs (hc h)
    exact ⟨iha, by rw [hv]; simp only [NExpr.real, ihv]⟩
  | binary op a b iha ihb =>
    simp only [NExpr.scoped, Bool.and_eq_true] at hs
    simp only [NExpr.reduceComplexIntegral] at h ⊢
    obtain ⟨hv, hc⟩ := cleanBinary_sound op (a.reduceComplexIntegral env.length)
      (b.reduceComplexIntegral env.length) env
    obtain ⟨ha1, ha2⟩ := iha hs.1 (hc h).1
    obtain ⟨hb1, hb2⟩ := ihb hs.2 (hc h).2
    exact ⟨⟨ha1, hb1⟩, by rw [hv]; simp only [NExpr.real, ha2, hb2]⟩
  | pow a m ih =>
    simp only [NExpr.scoped] at hs
    simp only [NExpr.reduceComplexIntegral] at h ⊢
    obtain ⟨hv, hc⟩ := cleanPow_sound (a.reduceComplexIntegral env.length) m env
    obtain ⟨iha, ihv⟩ := ih hs (hc h)
    exact ⟨iha, by rw [hv]; simp only [NExpr.real, ihv]⟩
  | rpow a c ih =>
    simp only [NExpr.scoped] at hs
    simp only [NExpr.reduceComplexIntegral] at h ⊢
    obtain ⟨iha, ihv⟩ := ih hs h
    exact ⟨iha, by simp only [NExpr.real, ihv]⟩
  | integral k a b f iha ihb ihf =>
    simp only [NExpr.scoped, Bool.and_eq_true] at hs
    obtain ⟨⟨hsa, hsb⟩, hsf⟩ := hs
    have hA : (a.reduceComplexIntegral env.length).Converges env →
        a.Converges env ∧ a.real env = (a.reduceComplexIntegral env.length).real env :=
      iha hsa
    have hB : (b.reduceComplexIntegral env.length).Converges env →
        b.Converges env ∧ b.real env = (b.reduceComplexIntegral env.length).real env :=
      ihb hsb
    have hF : ∀ x, (f.reduceComplexIntegral (env.length + 1)).Converges (env ++ [x]) →
        f.Converges (env ++ [x]) ∧
          f.real (env ++ [x]) = (f.reduceComplexIntegral (env.length + 1)).real (env ++ [x]) := by
      intro x hx
      have hlen : (env ++ [x]).length = env.length + 1 := by simp
      have := ihf (env := env ++ [x]) (by rw [hlen]; exact hsf) (by rw [hlen]; exact hx)
      rwa [hlen] at this
    simp only [NExpr.reduceComplexIntegral] at h ⊢
    split_ifs at h ⊢ with hk
    · simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hk
      obtain ⟨⟨rfl, hAi⟩, hBi⟩ := hk
      split at h
      · rename_i G hG
        obtain ⟨hc, hv⟩ := complexBranchIntegral_sound rfl hG h
        obtain ⟨hc', hv'⟩ := integral_transfer hA hB hF hc
        exact ⟨hc', hv'.trans hv⟩
      · rename_i hG
        obtain ⟨hc, hv⟩ := finitePrimitive_sound rfl hAi hBi _ h
        obtain ⟨hc', hv'⟩ := integral_transfer hA hB hF hc
        exact ⟨hc', hv'.trans hv⟩
    · exact integral_transfer hA hB hF h

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
