import Lynth.Analysis.SpecialFunctions
import Lynth.Analysis.SpecialFunctionsSeriesProofs

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
  | erf | si | eta | airyAi
deriving Repr, BEq, DecidableEq, Inhabited

inductive Binary where
  | add | sub | mul | div | max | min
deriving Repr, BEq, DecidableEq, Inhabited

inductive Term where
  | var
  | rat (q : ℚ)
  | pi
  | unary (op : Unary) (a : Term)
  | binary (op : Binary) (a b : Term)
  | pow (a : Term) (n : ℕ)
  | rpow (a : Term) (q : ℚ)
deriving Repr, BEq, DecidableEq, Inhabited

noncomputable def Unary.real : Unary → ℝ → ℝ
  | .neg => Neg.neg | .inv => Inv.inv | .exp => Real.exp
  | .sin => Real.sin | .cos => Real.cos | .sinh => Real.sinh | .cosh => Real.cosh
  | .log => Real.log | .sqrt => Real.sqrt | .abs => fun x => |x|
  | .floor => fun x => (⌊x⌋ : ℤ) | .atan => Real.arctan
  | .erf => Real.erf | .si => Real.Si | .eta => Real.dirichletEta | .airyAi => Real.airyAi

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
  | .erf => Complex.erf | .si => Complex.Si
  | .eta => Complex.dirichletEta | .airyAi => Complex.airyAi
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
  induction e with
  | var => exact measurable_id
  | rat q => exact measurable_const
  | pi => exact measurable_const
  | unary op a ih =>
    change Measurable (fun x => op.real (a.real x))
    cases op <;> simp only [Unary.real]
    · exact ih.neg
    · exact ih.inv
    · exact Real.measurable_exp.comp ih
    · exact Real.measurable_sin.comp ih
    · exact Real.measurable_cos.comp ih
    · exact Real.measurable_sinh.comp ih
    · exact Real.measurable_cosh.comp ih
    · exact Real.measurable_log.comp ih
    · exact Real.continuous_sqrt.measurable.comp ih
    · exact measurable_abs.comp ih
    · exact (measurable_from_top.comp Int.measurable_floor).comp ih
    · exact Real.continuous_arctan.measurable.comp ih
    · exact Real.continuous_erf.measurable.comp ih
    · exact Real.continuous_Si.measurable.comp ih
    · exact Real.measurable_dirichletEta.comp ih
    · exact Real.continuous_airyAi.measurable.comp ih
  | binary op a b iha ihb =>
    change Measurable (fun x => op.real (a.real x) (b.real x))
    cases op <;> simp only [Binary.real]
    · exact iha.add ihb
    · exact iha.sub ihb
    · exact iha.mul ihb
    · exact iha.div ihb
    · exact iha.max ihb
    · exact iha.min ihb
  | pow a n ih => exact ih.pow_const n
  | rpow a q ih => exact ih.pow_const _

theorem Term.analytic {e : Term} {s : Set ℂ} (h : e.Regular s) :
    AnalyticOnNhd ℂ e.complex s := by
  have slitPlane_ne_zero' : ∀ {z : ℂ}, z ∈ Complex.slitPlane → z ≠ 0 := by
    intro z hz
    intro hz0
    rcases (Complex.mem_slitPlane_iff.1 hz) with hp | hm
    · rw [hz0, Complex.zero_re] at hp
      exact (lt_irrefl 0) hp
    · rw [hz0, Complex.zero_im] at hm
      exact absurd rfl hm
  have analyticAt_sqrt' : ∀ {z : ℂ}, 0 < z.re → AnalyticAt ℂ (fun y : ℂ => y.sqrt) z := by
    intro z hz
    have hslit : z ∈ Complex.slitPlane := (Complex.mem_slitPlane_iff).2 (Or.inl hz)
    have hne : z ≠ 0 := by
      intro hc
      rw [hc, Complex.zero_re] at hz
      exact (lt_irrefl 0) hz
    have hclog : AnalyticAt ℂ Complex.log z := analyticAt_clog hslit
    have hmul : AnalyticAt ℂ (fun y : ℂ => ((2 : ℂ)⁻¹) * Complex.log y) z :=
      AnalyticAt.smul (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)⁻¹) z) hclog
    have hexp : AnalyticAt ℂ (fun y : ℂ => Complex.exp (Complex.log y / 2)) z := by
      convert analyticAt_cexp.comp hmul using 1; simp [div_eq_mul_inv, mul_comm]; rfl
    have hev : (fun y : ℂ => y.sqrt) =ᶠ[nhds z]
        (fun y : ℂ => Complex.exp (Complex.log y / 2)) := by
      filter_upwards [Complex.isOpen_slitPlane.eventually_mem hslit] with y hy
      rw [sqrt_eq_exp (slitPlane_ne_zero' hy)]
    exact analyticWithinAt_univ.mp
      (AnalyticWithinAt.congr_of_eventuallyEq (analyticWithinAt_univ.mpr hexp)
        (hev.filter_mono nhdsWithin_le_nhds) (sqrt_eq_exp hne))
  have h_erf : AnalyticOnNhd ℂ Complex.erf (Set.univ : Set ℂ) := by
    have hx := SpecialFunctions.entire_agrees.1 (f := Complex.erf) (by simp)
    simpa using hx
  have h_si : AnalyticOnNhd ℂ Complex.Si (Set.univ : Set ℂ) := by
    have hx := SpecialFunctions.entire_agrees.1 (f := Complex.Si) (by simp)
    simpa using hx
  have h_eta : AnalyticOnNhd ℂ Complex.dirichletEta (Set.univ : Set ℂ) := by
    have hx := SpecialFunctions.entire_agrees.1 (f := Complex.dirichletEta) (by simp)
    simpa using hx
  have h_airy : AnalyticOnNhd ℂ Complex.airyAi (Set.univ : Set ℂ) := by
    have hx := SpecialFunctions.entire_agrees.1 (f := Complex.airyAi) (by simp)
    simpa using hx
  induction e generalizing s with
  | var => intro x _; exact analyticAt_id
  | rat q => intro x _; exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => ((q : ℚ) : ℂ)) x)
  | pi => intro x _; exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (Real.pi : ℂ)) x)
  | pow a n ih =>
    intro x hx
    exact (ih h x hx).pow n
  | rpow a q ih =>
    intro x hx
    simp only [Term.complex]
    exact (ih h.1 x hx).cpow analyticAt_const
      ((Complex.mem_slitPlane_iff).2 (Or.inl (h.2 x hx)))
  | unary op a ih =>
    cases op with
    | neg =>
      simp only [Term.complex, Unary.complex]
      intro x hx
      exact (ih h.1 x hx).neg
    | inv =>
      simp only [Term.complex, Unary.complex]
      intro x hx
      exact (ih h.1 x hx).inv (h.2 x hx)
    | exp =>
      simp only [Term.complex, Unary.complex]
      intro x hx
      exact analyticAt_cexp.comp (ih h.1 x hx)
    | sin =>
      simp only [Term.complex, Unary.complex]
      intro x hx
      exact Complex.analyticAt_sin.comp (ih h.1 x hx)
    | cos =>
      simp only [Term.complex, Unary.complex]
      intro x hx
      exact Complex.analyticAt_cos.comp (ih h.1 x hx)
    | sinh =>
      simp only [Term.complex, Unary.complex]
      intro x hx
      exact Complex.analyticAt_sinh.comp (ih h.1 x hx)
    | cosh =>
      simp only [Term.complex, Unary.complex]
      intro x hx
      exact Complex.analyticAt_cosh.comp (ih h.1 x hx)
    | log =>
      simp only [Term.complex, Unary.complex]
      intro x hx
      exact (analyticAt_clog ((Complex.mem_slitPlane_iff).2 (Or.inl (h.2 x hx)))).comp (ih h.1 x hx)
    | sqrt =>
      simp only [Term.complex, Unary.complex]
      intro x hx
      exact (analyticAt_sqrt' (h.2 x hx)).comp (ih h.1 x hx)
    | abs => exact h.2.elim
    | floor => exact h.2.elim
    | atan => exact h.2.elim
    | erf =>
      simp only [Term.complex, Unary.complex]
      intro x hx
      show AnalyticAt ℂ (fun z : ℂ => Complex.erf (a.complex z)) x
      exact (h_erf (a.complex x) (Set.mem_univ _)).comp (ih h.1 x hx)
    | si =>
      simp only [Term.complex, Unary.complex]
      intro x hx
      show AnalyticAt ℂ (fun z : ℂ => Complex.Si (a.complex z)) x
      exact (h_si (a.complex x) (Set.mem_univ _)).comp (ih h.1 x hx)
    | eta =>
      simp only [Term.complex, Unary.complex]
      intro x hx
      show AnalyticAt ℂ (fun z : ℂ => Complex.dirichletEta (a.complex z)) x
      exact (h_eta (a.complex x) (Set.mem_univ _)).comp (ih h.1 x hx)
    | airyAi =>
      simp only [Term.complex, Unary.complex]
      intro x hx
      show AnalyticAt ℂ (fun z : ℂ => Complex.airyAi (a.complex z)) x
      exact (h_airy (a.complex x) (Set.mem_univ _)).comp (ih h.1 x hx)
  | binary op a b iha ihb =>
    cases op with
    | add =>
      simp only [Term.complex, Binary.complex]
      intro x hx
      exact (iha h.1 x hx).add (ihb h.2.1 x hx)
    | sub =>
      simp only [Term.complex, Binary.complex]
      intro x hx
      exact (iha h.1 x hx).sub (ihb h.2.1 x hx)
    | mul =>
      simp only [Term.complex, Binary.complex]
      intro x hx
      exact (iha h.1 x hx).mul (ihb h.2.1 x hx)
    | div =>
      simp only [Term.complex, Binary.complex]
      intro x hx
      exact (iha h.1 x hx).div (ihb h.2.1 x hx) (h.2.2 x hx)
    | max => exact h.2.2.elim
    | min => exact h.2.2.elim
theorem Term.agrees {e : Term} {s : Set ℂ} (h : e.Regular s)
    {x : ℝ} (hx : (x : ℂ) ∈ s) :
    e.complex x = (e.real x : ℂ) := by
  induction e generalizing s with
  | var => rfl
  | rat q => exact_mod_cast rfl
  | pi => rfl
  | pow a n ih =>
    have hx' : a.complex x = (a.real x : ℂ) := ih h hx
    show a.complex x ^ (n : ℕ) = ((a.real x ^ (n : ℕ) : ℝ) : ℂ)
    rw [hx', Complex.ofReal_pow]
  | rpow a q ih =>
    have ha : a.Regular s := h.1
    have hx' : a.complex x = (a.real x : ℂ) := ih ha hx
    have hy : 0 < a.real x := by
      have hz := h.2 (x : ℂ) hx
      rw [hx'] at hz
      exact_mod_cast hz
    show a.complex x ^ (((q : ℚ) : ℝ) : ℂ) = ((a.real x ^ ((q : ℚ) : ℝ) : ℝ) : ℂ)
    rw [hx', Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), Real.rpow_def_of_pos hy]
    rw [← Complex.ofReal_log hy.le]
    rw [Complex.ofReal_exp]
    rw [Complex.ofReal_mul]
  | unary op a ih =>
    have ha : a.Regular s := h.1
    have hx' : a.complex x = (a.real x : ℂ) := ih ha hx
    cases op with
    | neg => show -a.complex x = ((-a.real x : ℝ) : ℂ); rw [hx', Complex.ofReal_neg]
    | inv => show (a.complex x)⁻¹ = (((a.real x)⁻¹ : ℝ) : ℂ); rw [hx', Complex.ofReal_inv]
    | exp => show Complex.exp (a.complex x) = ((Real.exp (a.real x) : ℝ) : ℂ); rw [hx', Complex.ofReal_exp]
    | sin => show Complex.sin (a.complex x) = ((Real.sin (a.real x) : ℝ) : ℂ); rw [hx', Complex.ofReal_sin]
    | cos => show Complex.cos (a.complex x) = ((Real.cos (a.real x) : ℝ) : ℂ); rw [hx', Complex.ofReal_cos]
    | sinh => show Complex.sinh (a.complex x) = ((Real.sinh (a.real x) : ℝ) : ℂ); rw [hx', Complex.ofReal_sinh]
    | cosh => show Complex.cosh (a.complex x) = ((Real.cosh (a.real x) : ℝ) : ℂ); rw [hx', Complex.ofReal_cosh]
    | log =>
      have hy : 0 < a.real x := by
        have hz := h.2 (x : ℂ) hx
        rw [hx'] at hz
        exact_mod_cast hz
      show Complex.log (a.complex x) = ((Real.log (a.real x) : ℝ) : ℂ)
      rw [hx', Complex.ofReal_log hy.le]  -- log
    | sqrt =>
      have hy : 0 < a.real x := by
        have hz := h.2 (x : ℂ) hx
        rw [hx'] at hz
        exact_mod_cast hz
      show Complex.sqrt (a.complex x) = ((Real.sqrt (a.real x) : ℝ) : ℂ)
      rw [hx', Complex.sqrt_of_nonneg (by exact_mod_cast hy.le)]
      rw [Complex.ofReal_re]
    | abs => exact h.2.elim
    | floor => exact h.2.elim
    | atan => show Complex.arctan (a.complex x) = ((Real.arctan (a.real x) : ℝ) : ℂ); rw [hx', Complex.ofReal_arctan]
    | erf => show Complex.erf (a.complex x) = ((Real.erf (a.real x) : ℝ) : ℂ); rw [hx']; exact ((SpecialFunctions.entire_agrees.2 (a.real x)).1)
    | si => show Complex.Si (a.complex x) = ((Real.Si (a.real x) : ℝ) : ℂ); rw [hx']; exact ((SpecialFunctions.entire_agrees.2 (a.real x)).2.1)
    | eta => show Complex.dirichletEta (a.complex x) = ((Real.dirichletEta (a.real x) : ℝ) : ℂ); rw [hx']; exact ((SpecialFunctions.entire_agrees.2 (a.real x)).2.2.1)
    | airyAi => show Complex.airyAi (a.complex x) = ((Real.airyAi (a.real x) : ℝ) : ℂ); rw [hx']; exact ((SpecialFunctions.entire_agrees.2 (a.real x)).2.2.2)
  | binary op a b iha ihb =>
    have ha : a.Regular s := h.1
    have hb : b.Regular s := h.2.1
    have hxa : a.complex x = (a.real x : ℂ) := iha ha hx
    have hxb : b.complex x = (b.real x : ℂ) := ihb hb hx
    cases op with
    | add => show a.complex x + b.complex x = ((a.real x + b.real x : ℝ) : ℂ); rw [hxa, hxb, Complex.ofReal_add]
    | sub => show a.complex x - b.complex x = ((a.real x - b.real x : ℝ) : ℂ); rw [hxa, hxb, Complex.ofReal_sub]
    | mul => show a.complex x * b.complex x = ((a.real x * b.real x : ℝ) : ℂ); rw [hxa, hxb, Complex.ofReal_mul]
    | div => show a.complex x / b.complex x = ((a.real x / b.real x : ℝ) : ℂ); rw [hxa, hxb, Complex.ofReal_div]
    | max => exact h.2.2.elim
    | min => exact h.2.2.elim

end Intgrl
