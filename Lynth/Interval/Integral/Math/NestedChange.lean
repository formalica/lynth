import Lynth.Interval.Integral.Math.NestedSyntax
import Lynth.Interval.Integral.Math.NestedAnalysis
import Lynth.Interval.Integral.Math.NestedSyntaxLemmas
import Lynth.Interval.Integral.Math.NestedTransportProofs

/-! Mathematical scope and substitution obligations for the pure nested
expression language. The complete dependency bundle is mirrored in /tmp/intgrl. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl MeasureTheory Set

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
  have hA : (a.shift n 1).scoped (n+1) = true := shift_scoped n 1 ha
  have hB : (b.shift n 1).scoped (n+1) = true := shift_scoped n 1 hb
  have ht : (NExpr.var n).scoped (n+1) = true := by simp [NExpr.scoped]
  have h1 : (NExpr.rat 1).scoped (n+1) = true := rfl
  have hE : (simplify (mul (sub (b.shift n 1) (a.shift n 1))
      (f.replace n (add (a.shift n 1) (mul (sub (b.shift n 1) (a.shift n 1)) (NExpr.var n)))))).scoped
      (n+1) = true :=
    simplify_scoped (mul_scoped (sub_scoped hB hA)
      (replace_scoped n hf (add_scoped hA (mul_scoped (sub_scoped hB hA) ht))))
  cases how with
  | identity => exact hf
  | affine => exact hE
  | power m right =>
    simp only [transformed]
    apply regularize_scoped n (by omega)
    refine mul_scoped (mul_scoped rfl (pow_scoped _ ht)) (replace_scoped n hE ?_)
    split
    · exact sub_scoped h1 (pow_scoped _ ht)
    · exact pow_scoped _ ht
  | right | left =>
    simp only [transformed]
    have hd : (sub (NExpr.rat 1) (NExpr.var n)).scoped (n+1) = true := sub_scoped h1 ht
    have hu : (sub (NExpr.unary .inv (sub (NExpr.rat 1) (NExpr.var n))) (NExpr.rat 1)).scoped
        (n+1) = true := sub_scoped hd h1
    apply simplify_scoped
    refine replace_scoped n (regularize_scoped n (by omega) ?_) hd
    refine simplify_scoped (replace_scoped n ?_ hd)
    refine simplify_scoped (div_scoped (replace_scoped n hf ?_) (pow_scoped _ hd))
    split
    · exact add_scoped hA hu
    · exact sub_scoped hA hu

theorem formula_scoped {n : Nat} {kind : NDomain} {a b f : Expr} {form : Formula}
    (ha : a.scoped n = true) (hb : b.scoped n = true) (hf : f.scoped (n+1) = true)
    (h : formula n kind a b f = some form) :
    form.value.scoped n = true ∧ ∀ g ∈ form.nonnegative, g.scoped n = true := by
  have hsub : (sub b a).scoped n = true := sub_scoped hb ha
  have hpk : ∀ (o : Option ℚ), (o.bind fun q => if q ≤ -1 then none else
      some (Formula.mk (div (rpow (sub b a) (q + 1)) (NExpr.rat (q + 1)))
        (some (sub b a)) none)) = some form →
      form.value.scoped n = true ∧ ∀ g ∈ form.nonnegative, g.scoped n = true := by
    intro o ho
    rw [Option.bind_eq_some_iff] at ho
    obtain ⟨q, _, hq⟩ := ho
    split_ifs at hq
    cases hq
    refine ⟨div_scoped (rpow_scoped _ hsub) rfl, ?_⟩
    intro g hg
    cases hg
    exact hsub
  unfold formula at h
  simp only [Option.pure_def, Option.bind_eq_bind] at h
  split_ifs at h
  · cases h; exact ⟨neg_scoped_of ha, by simp⟩
  · split at h
    · rename_i c y'
      split_ifs at h with hc
      cases h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      simp only [NExpr.scoped, Bool.and_eq_true] at hf
      exact ⟨sub_scoped (scoped_of_not_uses hf.1 hc.1.2 hc.2) ha, by simp⟩
    · cases h
  · cases h; exact ⟨ha, by simp⟩
  · split at h
    · rename_i c y'
      split_ifs at h with hc
      cases h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      simp only [NExpr.scoped, Bool.and_eq_true] at hf
      exact ⟨add_scoped (scoped_of_not_uses hf.1 hc.1.2 hc.2) ha, by simp⟩
    · rename_i y' c
      split_ifs at h with hc
      cases h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      simp only [NExpr.scoped, Bool.and_eq_true] at hf
      exact ⟨sub_scoped ha (scoped_of_not_uses hf.2 hc.1.2 hc.2), by simp⟩
    · cases h
  · cases h
    refine ⟨mul_scoped hb (sub_scoped hb rfl), ?_⟩
    intro g hg; cases hg; exact hb
  · cases h
    refine ⟨mul_scoped hb (sub_scoped rfl hb), ?_⟩
    intro g hg; cases hg; exact hb
  all_goals exact hpk _ h

theorem center_properties {n : Nat} {f : Expr} (hf : f.scoped (n+1) = true) :
    (center n f).scoped n = true ∧ (center n f).hasIntegral = false := by
  induction f with
  | var i =>
    simp only [center]
    exact ⟨rfl, rfl⟩
  | rat | pi => exact ⟨rfl, rfl⟩
  | unary op a ih => exact ih hf
  | pow a k ih => exact ih hf
  | rpow a q ih => exact ih hf
  | binary op a b iha ihb =>
    have hf' := hf
    simp only [NExpr.scoped, Bool.and_eq_true] at hf'
    have hrec : (if center n a == .rat 0 then center n b else center n a).scoped n = true ∧
        (if center n a == .rat 0 then center n b else center n a).hasIntegral = false := by
      split
      · exact ihb hf'.2
      · exact iha hf'.1
    cases op
    case sub =>
      cases a
      case var i =>
        simp only [center]
        split
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
          exact ⟨scoped_of_not_uses hf'.2 hc.1.2 hc.2, hc.2⟩
        · exact ⟨rfl, rfl⟩
      all_goals (simp only [center]; exact hrec)
    all_goals (simp only [center]; exact hrec)
  | integral k a b g => exact ⟨rfl, rfl⟩

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
  have hE' := hE
  simp only [NExpr.Converges, NExpr.real, NDomain.Converges, Rat.cast_zero, Rat.cast_one] at hE'
  obtain ⟨-, -, hint, hconv⟩ := hE'
  rw [ii01_iff] at hint
  replace hconv : ∀ t ∈ Ioo (0:ℝ) 1,
      (transformed xs.length how a b f).Converges (xs ++ [t]) := fun t ht =>
    hconv t (by rw [uIoo_of_le zero_le_one]; exact ht)
  simp only [NExpr.Converges, NExpr.real, NDomain.value, Rat.cast_zero, Rat.cast_one]
  rw [int01]
  cases how with
  | identity => exact hhow.elim
  | right =>
    simp only [Change.Admissible] at hhow
    subst hhow
    obtain ⟨h1, h2, h3⟩ := tail_core true (how := .right) rfl hint hconv
    simp only [↓reduceIte] at h1 h2 h3
    exact ⟨⟨ha, hb, h1, h3⟩, h2⟩
  | left =>
    simp only [Change.Admissible] at hhow
    subst hhow
    obtain ⟨h1, h2, h3⟩ := tail_core false (how := .left) rfl hint hconv
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2 h3
    exact ⟨⟨ha, hb, h1, h3⟩, h2⟩
  | affine | power m r =>
    obtain ⟨h1, h2, h3⟩ := finite_core (xs := xs) (a := a) (b := b) (f := f)
      (by first | exact Or.inl rfl | exact Or.inr ⟨m, r, rfl, hhow.2⟩) hint hconv
    have hfin : kind.finite = true := by
      first | exact hhow | exact hhow.1
    cases kind
    case interval => exact ⟨⟨ha, hb, h1, h3⟩, h2⟩
    case icc =>
      have hle := hab hfin (fun h => by cases h)
      refine ⟨⟨ha, hb, (intervalIntegrable_iff_integrableOn_Icc_of_le hle).1 h1,
        by simpa [uIoo_of_le hle] using h3⟩, ?_⟩
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle, h2]
    case ioc =>
      have hle := hab hfin (fun h => by cases h)
      refine ⟨⟨ha, hb, (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 h1,
        by simpa [uIoo_of_le hle] using h3⟩, ?_⟩
      rw [← intervalIntegral.integral_of_le hle, h2]
    case ico =>
      have hle := hab hfin (fun h => by cases h)
      refine ⟨⟨ha, hb, (intervalIntegrable_iff_integrableOn_Ico_of_le hle).1 h1,
        by simpa [uIoo_of_le hle] using h3⟩, ?_⟩
      rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hle, h2]
    case ioo =>
      have hle := hab hfin (fun h => by cases h)
      refine ⟨⟨ha, hb, (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).1 h1,
        by simpa [uIoo_of_le hle] using h3⟩, ?_⟩
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle, h2]
    all_goals exact absurd hfin (by decide)

end Lynth.Interval.Integral.Nested
