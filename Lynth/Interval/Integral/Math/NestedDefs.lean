import Lynth.Interval.Integral.Math.Integrand

/-! Binder-aware syntax and mathematical semantics for iterated real integrals.
Variables use levels: entering an integral appends one variable. `Scoped`
checks every level before a computational certificate can be accepted.
This file and NestedAnalysis are mirrored in /tmp/intgrl without Lynth imports. -/

namespace Intgrl

inductive NDomain where
  | interval | icc | ioc | ico | ioo | right | left | whole
  deriving Repr, BEq, Inhabited

noncomputable def NDomain.value (k : NDomain) (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  match k with
  | .interval => ∫ x in a..b, f x
  | .icc => ∫ x in Set.Icc a b, f x
  | .ioc => ∫ x in Set.Ioc a b, f x
  | .ico => ∫ x in Set.Ico a b, f x
  | .ioo => ∫ x in Set.Ioo a b, f x
  | .right => ∫ x in Set.Ioi a, f x
  | .left => ∫ x in Set.Iio a, f x
  | .whole => ∫ x, f x

noncomputable def NDomain.Converges (k : NDomain) (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  match k with
  | .interval => IntervalIntegrable f MeasureTheory.volume a b
  | .icc => MeasureTheory.IntegrableOn f (Set.Icc a b)
  | .ioc => MeasureTheory.IntegrableOn f (Set.Ioc a b)
  | .ico => MeasureTheory.IntegrableOn f (Set.Ico a b)
  | .ioo => MeasureTheory.IntegrableOn f (Set.Ioo a b)
  | .right => MeasureTheory.IntegrableOn f (Set.Ioi a)
  | .left => MeasureTheory.IntegrableOn f (Set.Iio a)
  | .whole => MeasureTheory.Integrable f

def NDomain.finite : NDomain → Bool
  | .right | .left | .whole => false
  | _ => true

inductive NExpr where
  | var (level : Nat)
  | rat (q : ℚ)
  | pi
  | unary (op : Unary) (a : NExpr)
  | binary (op : Binary) (a b : NExpr)
  | pow (a : NExpr) (n : Nat)
  | rpow (a : NExpr) (q : ℚ)
  | integral (kind : NDomain) (a b body : NExpr)
  deriving Repr, BEq, Inhabited

def NExpr.scoped (n : Nat) : NExpr → Bool
  | .var i => i < n
  | .rat _ | .pi => true
  | .unary _ a | .pow a _ | .rpow a _ => a.scoped n
  | .binary _ a b => a.scoped n && b.scoped n
  | .integral _ a b f => a.scoped n && b.scoped n && f.scoped (n+1)

noncomputable def NExpr.real : NExpr → List ℝ → ℝ
  | .var i, env => env[i]?.getD 0
  | .rat q, _ => q
  | .pi, _ => Real.pi
  | .unary op a, env => op.real (a.real env)
  | .binary op a b, env => op.real (a.real env) (b.real env)
  | .pow a n, env => a.real env ^ n
  | .rpow a q, env => a.real env ^ (q : ℝ)
  | .integral k a b f, env => k.value (fun x => f.real (env ++ [x])) (a.real env) (b.real env)

/-- Recursive ordinary convergence: a divergent inner integral cannot be
used as the default zero of the Bochner integral. Endpoints are immaterial. -/
noncomputable def NExpr.Converges : NExpr → List ℝ → Prop
  | .var _, _ | .rat _, _ | .pi, _ => True
  | .unary _ a, env | .pow a _, env | .rpow a _, env => a.Converges env
  | .binary _ a b, env => a.Converges env ∧ b.Converges env
  | .integral k a b f, env =>
      a.Converges env ∧ b.Converges env ∧
      k.Converges (fun x => f.real (env ++ [x])) (a.real env) (b.real env) ∧
      (∀ x ∈ (match k with
        | .right => Set.Ioi (a.real env)
        | .left => Set.Iio (a.real env)
        | .whole => Set.univ
        | .interval => Set.uIoo (a.real env) (b.real env)
        | _ => Set.Ioo (a.real env) (b.real env)), f.Converges (env ++ [x]))

theorem NDomain.value_congr (k : NDomain) {f g : ℝ → ℝ} {a b c d : ℝ}
    (hf : ∀ x, f x = g x) (ha : a = c) (hb : b = d) :
    k.value f a b = k.value g c d := by
  rw [funext hf, ha, hb]

/-- Open and closed endpoint conventions agree for Lebesgue measure. -/
theorem NDomain.right_closed (f : ℝ → ℝ) (a : ℝ) :
    (∫ x in Set.Ici a, f x) = NDomain.right.value f a 0 := by
  have key : Set.Ici a \ Set.Ioi a = ({a} : Set ℝ) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_Ioi, Set.mem_singleton_iff, not_lt]
    constructor
    · rintro ⟨h1, h2⟩
      exact (le_antisymm h1 h2).symm
    · rintro rfl
      exact ⟨le_rfl, le_rfl⟩
  have hset : Set.Ici a =ᵐ[MeasureTheory.volume] Set.Ioi a := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · rw [key, Real.volume_singleton]
    · have hsub : (Set.Ioi a : Set ℝ) \ Set.Ici a = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        exact hx.2 (Set.mem_Ici.2 (le_of_lt hx.1))
      rw [hsub, MeasureTheory.measure_empty]
  exact MeasureTheory.setIntegral_congr_set hset

theorem NDomain.left_closed (f : ℝ → ℝ) (a : ℝ) :
    (∫ x in Set.Iic a, f x) = NDomain.left.value f a 0 := by
  have key : Set.Iic a \ Set.Iio a = ({a} : Set ℝ) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Iic, Set.mem_Iio, Set.mem_singleton_iff, not_lt]
    constructor
    · rintro ⟨h1, h2⟩
      exact (le_antisymm h2 h1).symm
    · rintro rfl
      exact ⟨le_rfl, le_rfl⟩
  have hset : Set.Iic a =ᵐ[MeasureTheory.volume] Set.Iio a := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · rw [key, Real.volume_singleton]
    · have hsub : (Set.Iio a : Set ℝ) \ Set.Iic a = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        exact hx.2 (Set.mem_Iic.2 (le_of_lt hx.1))
      rw [hsub, MeasureTheory.measure_empty]
  exact MeasureTheory.setIntegral_congr_set hset

end Intgrl
