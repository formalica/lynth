import Lynth.Interval.Integral.Math.NestedSyntaxProof

/-! Mathematical specification of complex-valued integrals over real variables.
No interval encodings, numerical evaluators or tactic implementation occur here.
The real projections are verified below, including recursive convergence. -/
namespace Intgrl
open Lynth.Interval.Integral.Nested

noncomputable def NDomain.cvalue (k : NDomain) (f : ℝ → ℂ) (a b : ℝ) : ℂ :=
  match k with
  | .interval => ∫ x in a..b, f x
  | .icc => ∫ x in Set.Icc a b, f x
  | .ioc => ∫ x in Set.Ioc a b, f x
  | .ico => ∫ x in Set.Ico a b, f x
  | .ioo => ∫ x in Set.Ioo a b, f x
  | .right => ∫ x in Set.Ioi a, f x
  | .left => ∫ x in Set.Iio a, f x
  | .whole => ∫ x, f x

noncomputable def NDomain.CConverges (k : NDomain) (f : ℝ → ℂ) (a b : ℝ) : Prop :=
  match k with
  | .interval => IntervalIntegrable f MeasureTheory.volume a b
  | .icc => MeasureTheory.IntegrableOn f (Set.Icc a b)
  | .ioc => MeasureTheory.IntegrableOn f (Set.Ioc a b)
  | .ico => MeasureTheory.IntegrableOn f (Set.Ico a b)
  | .ioo => MeasureTheory.IntegrableOn f (Set.Ioo a b)
  | .right => MeasureTheory.IntegrableOn f (Set.Ioi a)
  | .left => MeasureTheory.IntegrableOn f (Set.Iio a)
  | .whole => MeasureTheory.Integrable f

inductive CExpr where
  | real (a : NExpr)
  | i
  | unary (op : Unary) (a : CExpr)
  | binary (op : Binary) (a b : CExpr)
  | pow (a : CExpr) (n : Nat)
  | positivePower (base : ℚ) (a : CExpr)
  | integral (kind : NDomain) (a b : NExpr) (body : CExpr)
  deriving Repr, Inhabited

noncomputable def CExpr.value : CExpr → List ℝ → ℂ
  | .real a, env => a.real env
  | .i, _ => Complex.I
  | .unary op a, env => op.complex (a.value env)
  | .binary op a b, env => op.complex (a.value env) (b.value env)
  | .pow a n, env => a.value env ^ n
  | .positivePower b a, env => (b : ℂ) ^ a.value env
  | .integral k a b f, env =>
      k.cvalue (fun x => f.value (env ++ [x])) (a.real env) (b.real env)

namespace CParts
abbrev Parts := NExpr × NExpr
private def zero : NExpr := .rat 0
private def one : NExpr := .rat 1

/-- Simplify only arithmetic free of integrals. In particular, multiplying
by zero must not erase a divergent inner integral's convergence obligation. -/
def clean (e : NExpr) : NExpr := if e.hasIntegral then e else simplify e

def add (a b : NExpr) : NExpr := clean (.binary .add a b)
def sub (a b : NExpr) : NExpr := clean (.binary .sub a b)
def mul (a b : NExpr) : NExpr := clean (.binary .mul a b)
def div (a b : NExpr) : NExpr := clean (.binary .div a b)
def neg (a : NExpr) : NExpr := clean (.unary .neg a)
def un (op : Unary) (a : NExpr) : NExpr :=
  match a with
  | .rat 0 => match op with
    | .exp | .cos | .cosh => .rat 1
    | .neg | .inv | .sin | .sinh | .sqrt | .log | .abs | .floor | .atan => .rat 0
    | _ => clean (.unary op a)
  | .rat q => match op with
    | .neg => .rat (-q) | .inv => .rat q⁻¹ | .abs => .rat |q|
    | .floor => .rat (Int.floor q) | _ => clean (.unary op a)
  | _ => clean (.unary op a)
def sq (a : NExpr) : NExpr := clean (.pow a 2)

def plus (a b : Parts) : Parts := (add a.1 b.1, add a.2 b.2)
def minus (a b : Parts) : Parts := (sub a.1 b.1, sub a.2 b.2)
def times (a b : Parts) : Parts :=
  (sub (mul a.1 b.1) (mul a.2 b.2), add (mul a.1 b.2) (mul a.2 b.1))

def inverse (a : Parts) : Parts :=
  if a.2 == zero then (un .inv a.1, zero)
  else if a.1 == zero then (zero, neg (un .inv a.2))
  else let d := add (sq a.1) (sq a.2)
       (div a.1 d, neg (div a.2 d))

/-- -1 on negative inputs, 0 otherwise. Bounded arithmetic avoids an
unbounded intermediate inverse at the branch crossing. -/
def negative (a : NExpr) : NExpr :=
  un .floor (div a (un .sqrt (add one (sq a))))

def signUpper (a : NExpr) : NExpr := add one (mul (.rat 2) (negative a))
def isZero (a : NExpr) : NExpr := add one (add (negative a) (negative (neg a)))

def squareRoot (a : Parts) : Parts :=
  if a.2 == zero then (un .sqrt a.1, un .sqrt (neg a.1))
  else let r := un .sqrt (add (sq a.1) (sq a.2))
       (un .sqrt (div (add r a.1) (.rat 2)),
        mul (signUpper a.2) (un .sqrt (div (sub r a.1) (.rat 2))))

def logarithm (a : Parts) : Parts :=
  if a.2 == zero then (un .log a.1, neg (mul .pi (negative a.1)))
  else
    let r := un .sqrt (add (sq a.1) (sq a.2))
    if let .rat q := a.1 then
      if q != 0 then
        let angle := un .atan (div a.2 a.1)
        let angle := if q < 0 then add angle (mul .pi (signUpper a.2)) else angle
        (un .log r, angle)
      else (un .log r, mul (div .pi (.rat 2)) (sub (negative (neg a.2)) (negative a.2)))
    else
    let halfPi := div .pi (.rat 2)
    let arg := mul (signUpper a.2)
      (sub halfPi (un .atan (div a.1 (un .abs a.2))))
    let onAxis := sub (neg (mul .pi (negative a.1))) halfPi
    (un .log r, add arg (mul (isZero a.2) onAxis))

def exponential (a : Parts) : Parts :=
  (mul (un .exp a.1) (un .cos a.2), mul (un .exp a.1) (un .sin a.2))

def unary (op : Unary) (a : Parts) : Parts :=
  match op with
  | .neg => (neg a.1, neg a.2)
  | .inv => inverse a
  | .exp => exponential a
  | .sqrt => squareRoot a
  | .log => logarithm a
  | .sin => (mul (un .sin a.1) (un .cosh a.2), mul (un .cos a.1) (un .sinh a.2))
  | .cos => (mul (un .cos a.1) (un .cosh a.2), neg (mul (un .sin a.1) (un .sinh a.2)))
  | .sinh => (mul (un .sinh a.1) (un .cos a.2), mul (un .cosh a.1) (un .sin a.2))
  | .cosh => (mul (un .cosh a.1) (un .cos a.2), mul (un .sinh a.1) (un .sin a.2))
  | _ => a -- Not emitted by the compiler; excluded by Supported below.

def binary (op : Binary) (a b : Parts) : Parts :=
  match op with
  | .add => plus a b | .sub => minus a b | .mul => times a b
  | .div => times a (inverse b)
  | _ => a

def power (a : Parts) : Nat → Parts
  | 0 => (one,zero)
  | n+1 => times a (power a n)
end CParts

open CParts in
def CExpr.parts : CExpr → NExpr × NExpr
  | .real a => (a,.rat 0)
  | .i => (.rat 0,.rat 1)
  | .unary .inv (.unary .sqrt a) =>
      let A := a.parts
      if A.2 == .rat 0 then (un .sqrt (un .inv A.1), CParts.neg (un .sqrt (un .inv (CParts.neg A.1))))
      else CParts.unary .inv (CParts.unary .sqrt A)
  | .unary op a => CParts.unary op a.parts
  | .binary op a b => CParts.binary op a.parts b.parts
  | .pow a n =>
      let A := a.parts
      if A.2 == .rat 0 then (clean (.pow A.1 n),.rat 0) else power A n
  | .positivePower b a =>
      exponential (times (un .log (.rat b),.rat 0) a.parts)
  | .integral k a b f =>
      (.integral k a b f.parts.1, .integral k a b f.parts.2)

def CExpr.Supported : CExpr → Prop
  | .real _ | .i => True
  | .unary op a => a.Supported ∧ (match op with
      | .neg | .inv | .exp | .sqrt | .log | .sin | .cos | .sinh | .cosh => true
      | _ => false) = true
  | .binary op a b => a.Supported ∧ b.Supported ∧ (match op with
      | .add | .sub | .mul | .div => true | _ => false) = true
  | .pow a n => a.Supported ∧ (n = 0 → a.parts.1.hasIntegral = false ∧ a.parts.2.hasIntegral = false)
  | .positivePower b a => 0 < b ∧ a.Supported
  | .integral _ _ _ f => f.Supported

set_option maxSynthPendingDepth 64 in
def CExpr.decSupported : (e : CExpr) → Decidable e.Supported
  | .real _ | .i => isTrue trivial
  | .unary _ a => by
      letI := a.decSupported
      unfold CExpr.Supported
      infer_instance
  | .binary _ a b => by
      letI := a.decSupported
      letI := b.decSupported
      unfold CExpr.Supported
      infer_instance
  | .pow a _ => by
      letI := a.decSupported
      unfold CExpr.Supported
      infer_instance
  | .positivePower _ a => by
      letI := a.decSupported
      unfold CExpr.Supported
      infer_instance
  | .integral _ _ _ f => f.decSupported

instance (e : CExpr) : Decidable e.Supported := e.decSupported

/-- Every logarithm avoids the projection's faulty pure-imaginary branch.
When the real projection is syntactically zero, the imaginary projection must
also be syntactically zero, so `CParts.logarithm` takes its real-axis branch.
The condition is required recursively, including inside integral bodies. -/
def CExpr.LogProjectionSafe : CExpr → Prop
  | .real _ | .i => True
  | .unary op a => a.LogProjectionSafe ∧
      (op = .log → (a.parts.1 == .rat 0) = true → (a.parts.2 == .rat 0) = true)
  | .binary _ a b => a.LogProjectionSafe ∧ b.LogProjectionSafe
  | .pow a _ | .positivePower _ a => a.LogProjectionSafe
  | .integral _ _ _ f => f.LogProjectionSafe

set_option maxSynthPendingDepth 64 in
def CExpr.decLogProjectionSafe : (e : CExpr) → Decidable e.LogProjectionSafe
  | .real _ | .i => isTrue trivial
  | .unary _ a => by
      letI := a.decLogProjectionSafe
      unfold CExpr.LogProjectionSafe
      infer_instance
  | .binary _ a b => by
      letI := a.decLogProjectionSafe
      letI := b.decLogProjectionSafe
      unfold CExpr.LogProjectionSafe
      infer_instance
  | .pow a _ | .positivePower _ a => a.decLogProjectionSafe
  | .integral _ _ _ f => f.decLogProjectionSafe

instance (e : CExpr) : Decidable e.LogProjectionSafe := e.decLogProjectionSafe

noncomputable def CExpr.Converges : CExpr → List ℝ → Prop
  | .real a, env => a.Converges env
  | .i, _ => True
  | .unary _ a, env | .pow a _, env | .positivePower _ a, env => a.Converges env
  | .binary _ a b, env => a.Converges env ∧ b.Converges env
  | .integral k a b f, env =>
      a.Converges env ∧ b.Converges env ∧
      k.CConverges (fun x => f.value (env++[x])) (a.real env) (b.real env) ∧
      (∀ x ∈ (match k with
        | .right => Set.Ioi (a.real env) | .left => Set.Iio (a.real env)
        | .whole => Set.univ | .interval => Set.uIoo (a.real env) (b.real env)
        | _ => Set.Ioo (a.real env) (b.real env)), f.Converges (env++[x]))

namespace CParts

@[simp] theorem clean_real (a : NExpr) (env : List ℝ) :
    (clean a).real env = a.real env := by
  simp only [clean]
  split
  · rfl
  · rw [(simplify_semantics a).1]

@[simp] theorem clean_converges (a : NExpr) (env : List ℝ) :
    (clean a).Converges env ↔ a.Converges env := by
  simp only [clean]
  split
  · rfl
  · rw [(simplify_semantics a).2]

@[simp] theorem add_real (a b : NExpr) (env : List ℝ) :
    (add a b).real env = a.real env + b.real env := by
  simp [add, NExpr.real, Binary.real]

@[simp] theorem sub_real (a b : NExpr) (env : List ℝ) :
    (sub a b).real env = a.real env - b.real env := by
  simp [sub, NExpr.real, Binary.real]

@[simp] theorem mul_real (a b : NExpr) (env : List ℝ) :
    (mul a b).real env = a.real env * b.real env := by
  simp [mul, NExpr.real, Binary.real]

@[simp] theorem div_real (a b : NExpr) (env : List ℝ) :
    (div a b).real env = a.real env / b.real env := by
  simp [div, NExpr.real, Binary.real]

@[simp] theorem neg_real (a : NExpr) (env : List ℝ) :
    (neg a).real env = -a.real env := by
  simp [neg, NExpr.real, Unary.real]

@[simp] theorem sq_real (a : NExpr) (env : List ℝ) :
    (sq a).real env = a.real env ^ 2 := by
  simp [sq, NExpr.real]

@[simp] theorem add_converges (a b : NExpr) (env : List ℝ) :
    (add a b).Converges env ↔ a.Converges env ∧ b.Converges env := by
  simp [add, NExpr.Converges]

@[simp] theorem sub_converges (a b : NExpr) (env : List ℝ) :
    (sub a b).Converges env ↔ a.Converges env ∧ b.Converges env := by
  simp [sub, NExpr.Converges]

@[simp] theorem mul_converges (a b : NExpr) (env : List ℝ) :
    (mul a b).Converges env ↔ a.Converges env ∧ b.Converges env := by
  simp [mul, NExpr.Converges]

@[simp] theorem div_converges (a b : NExpr) (env : List ℝ) :
    (div a b).Converges env ↔ a.Converges env ∧ b.Converges env := by
  simp [div, NExpr.Converges]

@[simp] theorem neg_converges (a : NExpr) (env : List ℝ) :
    (neg a).Converges env ↔ a.Converges env := by
  simp [neg, NExpr.Converges]

@[simp] theorem sq_converges (a : NExpr) (env : List ℝ) :
    (sq a).Converges env ↔ a.Converges env := by
  simp [sq, NExpr.Converges]

private theorem un_zero (op : Unary) : un op (.rat 0) =
    match op with
    | .exp | .cos | .cosh => .rat 1
    | .neg | .inv | .sin | .sinh | .sqrt | .log | .abs | .floor | .atan => .rat 0
    | _ => clean (.unary op (.rat 0)) := by
  cases op <;> rfl

@[simp] theorem un_real (op : Unary) (a : NExpr) (env : List ℝ) :
    (un op a).real env = op.real (a.real env) := by
  cases a with
  | rat q =>
    by_cases h : q = 0
    · subst q
      rw [un_zero]
      cases op <;> simp [NExpr.real, Unary.real]
    · cases op <;> simp [un, h, NExpr.real, Unary.real]
  | var | pi | unary | binary | pow | rpow | integral =>
    simp [un, NExpr.real]

@[simp] theorem un_converges (op : Unary) (a : NExpr) (env : List ℝ) :
    (un op a).Converges env ↔ a.Converges env := by
  cases a with
  | rat q =>
    by_cases h : q = 0
    · subst q
      rw [un_zero]
      cases op <;> simp [NExpr.Converges]
    · cases op <;> simp [un, h, NExpr.Converges]
  | var | pi | unary | binary | pow | rpow | integral =>
    simp [un, NExpr.Converges]

end CParts

namespace CParts

theorem floor_normalized (x : ℝ) :
    (⌊x / Real.sqrt (1 + x ^ 2)⌋ : ℝ) = if x < 0 then -1 else 0 := by
  have hs : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hb : -Real.sqrt (1 + x ^ 2) < x ∧ x < Real.sqrt (1 + x ^ 2) :=
    Real.sq_lt.1 (by linarith : x ^ 2 < 1 + x ^ 2)
  by_cases hx : x < 0
  · have hf : ⌊x / Real.sqrt (1 + x ^ 2)⌋ = (-1 : ℤ) := by
      apply Int.floor_eq_iff.2
      constructor
      · norm_num
        exact (le_div_iff₀ hs).2 (by linarith [hb.1])
      · simpa using (div_neg_of_neg_of_pos hx hs)
    simp [hx, hf]
  · have hf : ⌊x / Real.sqrt (1 + x ^ 2)⌋ = (0 : ℤ) := by
      apply Int.floor_eq_iff.2
      constructor
      · simpa using div_nonneg (le_of_not_gt hx) hs.le
      · simpa using (div_lt_one hs).2 hb.2
    simp [hx, hf]

theorem arg_of_re_pos (x y : ℝ) (hx : 0 < x) :
    Complex.arg ((x : ℂ) + (y : ℂ) * Complex.I) = Real.arctan (y / x) := by
  have ha : |Complex.arg ((x : ℂ) + (y : ℂ) * Complex.I)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by simpa using hx))
  obtain ⟨hl, hu⟩ := abs_lt.1 ha
  have h := Real.arctan_tan hl hu
  rw [Complex.tan_arg] at h
  simpa using h.symm

theorem arg_of_re_neg (x y : ℝ) (hx : x < 0) :
    Complex.arg ((x : ℂ) + (y : ℂ) * Complex.I) =
      Real.arctan (y / x) + Real.pi * (if y < 0 then -1 else 1) := by
  have h := arg_of_re_pos (-x) (-y) (neg_pos.2 hx)
  have hz : ((-x : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I =
      -((x : ℂ) + (y : ℂ) * Complex.I) := by push_cast; ring
  rw [hz] at h
  by_cases hy : y < 0
  · rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using hy)] at h
    simp only [neg_div_neg_eq, hy, ↓reduceIte, mul_neg, mul_one] at h ⊢
    linarith
  · by_cases hy0 : y = 0
    · subst y
      simp [Complex.arg_ofReal_of_neg hx]
    · have hy' : 0 < y := lt_of_le_of_ne (le_of_not_gt hy) (Ne.symm hy0)
      rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos (by simpa using hy')] at h
      simp only [neg_div_neg_eq, hy, ↓reduceIte, mul_one] at h ⊢
      linarith

theorem arg_of_im_pos (x y : ℝ) (hy : 0 < y) :
    Complex.arg ((x : ℂ) + (y : ℂ) * Complex.I) =
      Real.pi / 2 - Real.arctan (x / y) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [arg_of_re_neg x y hx, if_neg (not_lt_of_gt hy), mul_one]
    have h := Real.arctan_inv_of_neg (div_neg_of_neg_of_pos hx hy)
    rw [inv_div] at h
    linarith
  · subst x
    have h : Complex.arg ((0 : ℂ) + (y : ℂ) * Complex.I) = Real.pi / 2 :=
      Complex.arg_eq_pi_div_two_iff.2 (by simp [hy])
    simpa using h
  · rw [arg_of_re_pos x y hx]
    have h := Real.arctan_inv_of_pos (div_pos hx hy)
    simpa only [inv_div] using h

theorem arg_vertical (x y : ℝ) :
    Complex.arg ((x : ℂ) + (y : ℂ) * Complex.I) =
      (if y < 0 then -1 else 1) * (Real.pi / 2 - Real.arctan (x / |y|)) +
      (if y = 0 then 1 else 0) *
        (-(Real.pi * (if x < 0 then -1 else 0)) - Real.pi / 2) := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have h := arg_of_im_pos (-x) (-y) (neg_pos.2 hy)
    have hz : ((-x : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I =
        -((x : ℂ) + (y : ℂ) * Complex.I) := by push_cast; ring
    rw [hz, Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using hy)] at h
    simp only [neg_div_neg_eq] at h
    simp only [hy, ↓reduceIte, ne_of_lt hy, abs_of_neg hy, div_neg, Real.arctan_neg,
      neg_div_neg_eq, zero_mul, add_zero, neg_one_mul]
    linarith
  · subst y
    by_cases hx : x < 0
    · simp [hx, Complex.arg_ofReal_of_neg hx]
    · simp [hx, Complex.arg_ofReal_of_nonneg (le_of_not_gt hx)]
  · simp only [not_lt_of_gt hy, ↓reduceIte, ne_of_gt hy, abs_of_pos hy,
      one_mul, zero_mul, add_zero]
    exact arg_of_im_pos x y hy

end CParts

namespace CParts

@[simp] theorem negative_real (a : NExpr) (env : List ℝ) :
    (negative a).real env = if a.real env < 0 then -1 else 0 := by
  change (un .floor (div a (un .sqrt (add (.rat 1) (sq a))))).real env = _
  simpa only [un_real, div_real, add_real, sq_real, NExpr.real, Unary.real,
    Rat.cast_one] using floor_normalized (a.real env)

@[simp] theorem negative_converges (a : NExpr) (env : List ℝ) :
    (negative a).Converges env ↔ a.Converges env := by
  change (un .floor (div a (un .sqrt (add (.rat 1) (sq a))))).Converges env ↔ _
  simp [NExpr.Converges]

@[simp] theorem signUpper_real (a : NExpr) (env : List ℝ) :
    (signUpper a).real env = if a.real env < 0 then -1 else 1 := by
  change (add (.rat 1) (mul (.rat 2) (negative a))).real env = _
  by_cases h : a.real env < 0 <;> norm_num [h, NExpr.real]

@[simp] theorem signUpper_converges (a : NExpr) (env : List ℝ) :
    (signUpper a).Converges env ↔ a.Converges env := by
  change (add (.rat 1) (mul (.rat 2) (negative a))).Converges env ↔ _
  simp [NExpr.Converges]

@[simp] theorem isZero_real (a : NExpr) (env : List ℝ) :
    (isZero a).real env = if a.real env = 0 then 1 else 0 := by
  change (add (.rat 1) (add (negative a) (negative (neg a)))).real env = _
  simp only [add_real, negative_real, neg_real, NExpr.real, Rat.cast_one]
  rcases lt_trichotomy (a.real env) 0 with hx | hx | hx
  · norm_num [hx, not_lt_of_ge hx.le, ne_of_lt hx]
  · simp [hx]
  · norm_num [hx, not_lt_of_ge hx.le, ne_of_gt hx]

@[simp] theorem isZero_converges (a : NExpr) (env : List ℝ) :
    (isZero a).Converges env ↔ a.Converges env := by
  change (add (.rat 1) (add (negative a) (negative (neg a)))).Converges env ↔ _
  simp [NExpr.Converges]

theorem plus_value (a b : Parts) (env : List ℝ) :
    ((a.1.real env : ℂ) + (a.2.real env : ℂ) * Complex.I) +
      ((b.1.real env : ℂ) + (b.2.real env : ℂ) * Complex.I) =
    ((plus a b).1.real env : ℂ) + ((plus a b).2.real env : ℂ) * Complex.I := by
  simp only [plus, add_real, Complex.ofReal_add]
  ring

theorem minus_value (a b : Parts) (env : List ℝ) :
    ((a.1.real env : ℂ) + (a.2.real env : ℂ) * Complex.I) -
      ((b.1.real env : ℂ) + (b.2.real env : ℂ) * Complex.I) =
    ((minus a b).1.real env : ℂ) + ((minus a b).2.real env : ℂ) * Complex.I := by
  simp only [minus, sub_real, Complex.ofReal_sub]
  ring

theorem times_value (a b : Parts) (env : List ℝ) :
    ((a.1.real env : ℂ) + (a.2.real env : ℂ) * Complex.I) *
      ((b.1.real env : ℂ) + (b.2.real env : ℂ) * Complex.I) =
    ((times a b).1.real env : ℂ) + ((times a b).2.real env : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [times, Complex.mul_re, Complex.mul_im] <;> ring

@[simp] theorem plus_converges (a b : Parts) (env : List ℝ) :
    ((plus a b).1.Converges env ∧ (plus a b).2.Converges env) ↔
      (a.1.Converges env ∧ a.2.Converges env) ∧
      (b.1.Converges env ∧ b.2.Converges env) := by
  simp only [plus, add_converges]
  tauto

@[simp] theorem minus_converges (a b : Parts) (env : List ℝ) :
    ((minus a b).1.Converges env ∧ (minus a b).2.Converges env) ↔
      (a.1.Converges env ∧ a.2.Converges env) ∧
      (b.1.Converges env ∧ b.2.Converges env) := by
  simp only [minus, sub_converges]
  tauto

@[simp] theorem times_converges (a b : Parts) (env : List ℝ) :
    ((times a b).1.Converges env ∧ (times a b).2.Converges env) ↔
      (a.1.Converges env ∧ a.2.Converges env) ∧
      (b.1.Converges env ∧ b.2.Converges env) := by
  simp only [times, add_converges, sub_converges, mul_converges]
  tauto

private theorem inverse_eq (p q : NExpr) : inverse (p, q) =
    if q == .rat 0 then (un .inv p, .rat 0)
    else if p == .rat 0 then (.rat 0, neg (un .inv q))
    else (div p (add (sq p) (sq q)), neg (div q (add (sq p) (sq q)))) := rfl

theorem inverse_value (a : Parts) (env : List ℝ) :
    ((a.1.real env : ℂ) + (a.2.real env : ℂ) * Complex.I)⁻¹ =
    ((inverse a).1.real env : ℂ) + ((inverse a).2.real env : ℂ) * Complex.I := by
  rcases a with ⟨p, q⟩
  simp only [inverse_eq]
  by_cases hq : q = .rat 0
  · subst q
    simp [Unary.real, NExpr.real]
  · by_cases hp : p = .rat 0
    · subst p
      simp [hq, Unary.real, NExpr.real, mul_inv_rev, mul_comm]
    · simp only [beq_iff_eq, hq, hp, ↓reduceIte, Prod.fst, Prod.snd,
        div_real, add_real, sq_real, neg_real]
      apply Complex.ext <;> simp only [Complex.inv_re, Complex.inv_im, Complex.normSq_apply,
        Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.neg_re, Complex.neg_im, mul_zero, zero_mul, mul_one, zero_add,
        add_zero, sub_zero, zero_sub, pow_two, neg_div]

@[simp] theorem inverse_converges (a : Parts) (env : List ℝ) :
    ((inverse a).1.Converges env ∧ (inverse a).2.Converges env) ↔
      a.1.Converges env ∧ a.2.Converges env := by
  rcases a with ⟨p, q⟩
  simp only [inverse_eq]
  by_cases hq : q = .rat 0
  · subst q
    simp [NExpr.Converges]
  · by_cases hp : p = .rat 0
    · subst p
      simp [hq, NExpr.Converges]
    · simp [hq, hp]
      tauto

end CParts

namespace CParts

theorem sqrt_real_eq (x : ℝ) :
    Complex.sqrt (x : ℂ) = (Real.sqrt x : ℂ) + (Real.sqrt (-x) : ℂ) * Complex.I := by
  rw [Complex.sqrt_eq_real_add_ite]
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re, Complex.ofReal_im,
    le_refl, ↓reduceIte, one_mul]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, show (x + x) / 2 = x by ring]
    simp [Real.sqrt_eq_zero_of_nonpos (neg_nonpos.2 hx)]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    rw [show (-x + x) / 2 = 0 by ring, show (-x - x) / 2 = -x by ring]
    simp [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx)]

theorem inverse_sqrt_real_eq (x : ℝ) :
    (Complex.sqrt (x : ℂ))⁻¹ =
      (Real.sqrt x⁻¹ : ℂ) + (-Real.sqrt (-x)⁻¹ : ℂ) * Complex.I := by
  rw [sqrt_real_eq, Real.sqrt_inv, Real.sqrt_inv]
  by_cases hx : 0 ≤ x
  · simp [Real.sqrt_eq_zero_of_nonpos (neg_nonpos.2 hx), Real.sqrt_inv]
  · simp [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx), Real.sqrt_inv, mul_inv_rev, mul_comm]

theorem log_real_eq (x : ℝ) :
    Complex.log (x : ℂ) = (Real.log x : ℂ) +
      ((-(Real.pi * (if x < 0 then -1 else 0)) : ℝ) : ℂ) * Complex.I := by
  rw [Complex.log]
  by_cases hx : x < 0
  · simp [hx, Complex.arg_ofReal_of_neg hx]
  · simp [hx, Complex.arg_ofReal_of_nonneg (le_of_not_gt hx)]

private theorem squareRoot_eq (p q : NExpr) : squareRoot (p, q) =
    if q == .rat 0 then (un .sqrt p, un .sqrt (neg p))
    else (un .sqrt (div (add (un .sqrt (add (sq p) (sq q))) p) (.rat 2)),
      mul (signUpper q) (un .sqrt (div (sub (un .sqrt (add (sq p) (sq q))) p) (.rat 2)))) := rfl

theorem squareRoot_value (a : Parts) (env : List ℝ) :
    Complex.sqrt ((a.1.real env : ℂ) + (a.2.real env : ℂ) * Complex.I) =
    ((squareRoot a).1.real env : ℂ) + ((squareRoot a).2.real env : ℂ) * Complex.I := by
  rcases a with ⟨p, q⟩
  simp only [squareRoot_eq]
  by_cases hq : q = .rat 0
  · subst q
    simpa [NExpr.real, Unary.real] using sqrt_real_eq (p.real env)
  · simp only [beq_iff_eq, hq, ↓reduceIte, Prod.fst, Prod.snd, un_real, div_real,
      add_real, sq_real, sub_real, mul_real, signUpper_real, NExpr.real, Unary.real,
      Rat.cast_ofNat]
    rw [Complex.sqrt_eq_real_add_ite, Complex.norm_eq_sqrt_sq_add_sq]
    by_cases hy : q.real env < 0 <;> simp [hy, le_of_not_gt, Complex.ofReal_mul,
      not_le_of_gt, *]

@[simp] theorem squareRoot_converges (a : Parts) (env : List ℝ) :
    ((squareRoot a).1.Converges env ∧ (squareRoot a).2.Converges env) ↔
      a.1.Converges env ∧ a.2.Converges env := by
  rcases a with ⟨p, q⟩
  simp only [squareRoot_eq]
  by_cases hq : q = .rat 0
  · subst q
    simp [NExpr.Converges]
  · simp [hq]
    tauto

theorem exponential_value (a : Parts) (env : List ℝ) :
    Complex.exp ((a.1.real env : ℂ) + (a.2.real env : ℂ) * Complex.I) =
    ((exponential a).1.real env : ℂ) + ((exponential a).2.real env : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [exponential, Unary.real, Complex.exp_re, Complex.exp_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]

@[simp] theorem exponential_converges (a : Parts) (env : List ℝ) :
    ((exponential a).1.Converges env ∧ (exponential a).2.Converges env) ↔
      a.1.Converges env ∧ a.2.Converges env := by
  simp [exponential]

end CParts

namespace CParts

theorem log_horizontal (x y : ℝ) (hx : x ≠ 0) :
    Complex.log ((x : ℂ) + (y : ℂ) * Complex.I) =
      (Real.log (Real.sqrt (x ^ 2 + y ^ 2)) : ℂ) +
      ((Real.arctan (y / x) +
        if x < 0 then Real.pi * (if y < 0 then -1 else 1) else 0 : ℝ) : ℂ) * Complex.I := by
  rw [Complex.log]
  have hn : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
    simp [Complex.norm_eq_sqrt_sq_add_sq]
  rw [hn]
  by_cases hn : x < 0
  · rw [arg_of_re_neg x y hn]
    simp [hn]
  · have hp : 0 < x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hx)
    rw [arg_of_re_pos x y hp]
    simp [hn]

theorem log_vertical (x y : ℝ) :
    Complex.log ((x : ℂ) + (y : ℂ) * Complex.I) =
      (Real.log (Real.sqrt (x ^ 2 + y ^ 2)) : ℂ) +
      (((if y < 0 then -1 else 1) * (Real.pi / 2 - Real.arctan (x / |y|)) +
        (if y = 0 then 1 else 0) *
          (-(Real.pi * (if x < 0 then -1 else 0)) - Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
  rw [Complex.log, arg_vertical]
  congr 3
  simp [Complex.norm_eq_sqrt_sq_add_sq]

private theorem logarithm_eq (p q : NExpr) : logarithm (p, q) =
    if q == .rat 0 then (un .log p, neg (mul .pi (negative p)))
    else
      let r := un .sqrt (add (sq p) (sq q))
      if let .rat c := p then
        if c != 0 then
          let angle := un .atan (div q p)
          let angle := if c < 0 then add angle (mul .pi (signUpper q)) else angle
          (un .log r, angle)
        else (un .log r, mul (div .pi (.rat 2)) (sub (negative (neg q)) (negative q)))
      else
        let halfPi := div .pi (.rat 2)
        let arg := mul (signUpper q) (sub halfPi (un .atan (div p (un .abs q))))
        let onAxis := sub (neg (mul .pi (negative p))) halfPi
        (un .log r, add arg (mul (isZero q) onAxis)) := rfl

theorem logarithm_value (a : Parts) (env : List ℝ)
    (hsafe : (a.1 == .rat 0) = true → (a.2 == .rat 0) = true) :
    Complex.log ((a.1.real env : ℂ) + (a.2.real env : ℂ) * Complex.I) =
    ((logarithm a).1.real env : ℂ) + ((logarithm a).2.real env : ℂ) * Complex.I := by
  rcases a with ⟨p, q⟩
  simp only [logarithm_eq]
  split
  · rename_i hq
    have hq' : q = .rat 0 := by simpa only [beq_iff_eq] using hq
    subst q
    simp only [un_real, neg_real, mul_real, negative_real, NExpr.real, Unary.real,
      Rat.cast_zero, Complex.ofReal_zero, zero_mul, add_zero]
    exact log_real_eq (p.real env)
  · rename_i hq
    split
    · rename_i r
      have hr : r ≠ 0 := by
        intro hr
        subst r
        exact hq (hsafe (by simp))
      rw [if_pos (by simpa using hr)]
      dsimp only
      simp only [un_real, add_real, mul_real, div_real, sq_real, signUpper_real,
        NExpr.real, Unary.real]
      have hh : (r : ℝ) ≠ 0 := by exact_mod_cast hr
      have hv := log_horizontal (r : ℝ) (q.real env) hh
      by_cases hrn : r < 0
      · have hn : (r : ℝ) < 0 := by exact_mod_cast hrn
        simpa [hrn, hn, NExpr.real, Unary.real] using hv
      · have hn : ¬(r : ℝ) < 0 := by exact_mod_cast hrn
        simpa [hrn, hn, NExpr.real, Unary.real] using hv
    · dsimp only
      simp only [un_real, add_real, mul_real, sub_real, div_real, sq_real,
        signUpper_real, isZero_real, neg_real, negative_real, NExpr.real, Unary.real,
        Rat.cast_ofNat]
      exact log_vertical (p.real env) (q.real env)

@[simp] theorem logarithm_converges (a : Parts) (env : List ℝ) :
    ((logarithm a).1.Converges env ∧ (logarithm a).2.Converges env) ↔
      a.1.Converges env ∧ a.2.Converges env := by
  rcases a with ⟨p, q⟩
  simp only [logarithm_eq]
  split
  · rename_i hq
    have hq' : q = .rat 0 := by simpa only [beq_iff_eq] using hq
    subst q
    simp [NExpr.Converges]
  · split
    · split_ifs <;> simp [NExpr.Converges]
    · simp
      tauto

end CParts

namespace CParts

theorem unary_value (op : Unary) (a : Parts) (env : List ℝ)
    (hs : (match op with
      | .neg | .inv | .exp | .sqrt | .log | .sin | .cos | .sinh | .cosh => true
      | _ => false) = true)
    (hlog : op = .log → (a.1 == .rat 0) = true → (a.2 == .rat 0) = true) :
    op.complex ((a.1.real env : ℂ) + (a.2.real env : ℂ) * Complex.I) =
    ((unary op a).1.real env : ℂ) + ((unary op a).2.real env : ℂ) * Complex.I := by
  cases op with
  | neg => simp [unary, Unary.complex]; ring
  | inv => exact inverse_value a env
  | exp => exact exponential_value a env
  | sqrt => exact squareRoot_value a env
  | log => exact logarithm_value a env (hlog rfl)
  | sin =>
    simp only [unary, Unary.complex, mul_real, un_real, Unary.real]
    rw [Complex.sin_eq]
    simp
  | cos =>
    simp only [unary, Unary.complex, neg_real, mul_real, un_real, Unary.real]
    rw [Complex.cos_eq]
    simp
    ring
  | sinh =>
    simp only [unary, Unary.complex, mul_real, un_real, Unary.real]
    rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
    simp [mul_assoc]
  | cosh =>
    simp only [unary, Unary.complex, mul_real, un_real, Unary.real]
    rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
    simp [mul_assoc]
  | abs | floor | atan | erf | si | eta | airyAi => cases hs

@[simp] theorem unary_converges (op : Unary) (a : Parts) (env : List ℝ) :
    ((unary op a).1.Converges env ∧ (unary op a).2.Converges env) ↔
      a.1.Converges env ∧ a.2.Converges env := by
  cases op <;> simp [unary]

theorem binary_value (op : Binary) (a b : Parts) (env : List ℝ)
    (hs : (match op with | .add | .sub | .mul | .div => true | _ => false) = true) :
    op.complex ((a.1.real env : ℂ) + (a.2.real env : ℂ) * Complex.I)
      ((b.1.real env : ℂ) + (b.2.real env : ℂ) * Complex.I) =
    ((binary op a b).1.real env : ℂ) + ((binary op a b).2.real env : ℂ) * Complex.I := by
  cases op with
  | add => exact plus_value a b env
  | sub => exact minus_value a b env
  | mul => exact times_value a b env
  | div =>
    change _ / _ = _
    rw [div_eq_mul_inv, inverse_value b env]
    exact times_value a (inverse b) env
  | max | min => cases hs

@[simp] theorem binary_converges (op : Binary) (a b : Parts) (env : List ℝ)
    (hs : (match op with | .add | .sub | .mul | .div => true | _ => false) = true) :
    ((binary op a b).1.Converges env ∧ (binary op a b).2.Converges env) ↔
      (a.1.Converges env ∧ a.2.Converges env) ∧
      (b.1.Converges env ∧ b.2.Converges env) := by
  cases op <;> simp_all [binary]

theorem power_value (a : Parts) (n : Nat) (env : List ℝ) :
    ((a.1.real env : ℂ) + (a.2.real env : ℂ) * Complex.I) ^ n =
    ((power a n).1.real env : ℂ) + ((power a n).2.real env : ℂ) * Complex.I := by
  induction n with
  | zero =>
    change _ ^ 0 = ((NExpr.rat 1).real env : ℂ) + ((NExpr.rat 0).real env : ℂ) * Complex.I
    simp [NExpr.real]
  | succ n ih =>
    rw [pow_succ', ih]
    exact times_value a (power a n) env

@[simp] theorem power_converges (a : Parts) (n : Nat) (env : List ℝ) :
    ((power a n).1.Converges env ∧ (power a n).2.Converges env) ↔
      n = 0 ∨ (a.1.Converges env ∧ a.2.Converges env) := by
  induction n with
  | zero =>
    change (True ∧ True) ↔ _
    simp
  | succ n ih =>
    simp only [power, times_converges, ih, Nat.succ_ne_zero, false_or]
    tauto

end CParts

section ComplexProjectionIntegral
open MeasureTheory

private theorem integral_components {μ : Measure ℝ} {f : ℝ → ℂ} {g h : ℝ → ℝ}
    (hg : Integrable g μ) (hh : Integrable h μ)
    (heq : f =ᵐ[μ] fun x => (g x : ℂ) + (h x : ℂ) * Complex.I) :
    Integrable f μ ∧
      (∫ x, f x ∂μ) = ((∫ x, g x ∂μ : ℝ) : ℂ) + ((∫ x, h x ∂μ : ℝ) : ℂ) * Complex.I := by
  have hgc : Integrable (fun x => (g x : ℂ)) μ := hg.ofReal
  have hhc : Integrable (fun x => (h x : ℂ) * Complex.I) μ := hh.ofReal.mul_const _
  refine ⟨(hgc.add hhc).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_add hgc hhc, integral_mul_const]
  simp only [integral_complex_ofReal]

theorem NDomain.components_sound (k : NDomain) {f : ℝ → ℂ} {g h : ℝ → ℝ} {a b : ℝ}
    (hg : k.Converges g a b) (hh : k.Converges h a b)
    (heq : ∀ x ∈ (match k with
      | .right => Set.Ioi a | .left => Set.Iio a | .whole => Set.univ
      | .interval => Set.uIoo a b | _ => Set.Ioo a b),
      f x = (g x : ℂ) + (h x : ℂ) * Complex.I) :
    k.CConverges f a b ∧
      k.cvalue f a b = (k.value g a b : ℂ) + (k.value h a b : ℂ) * Complex.I := by
  cases k with
  | interval =>
    have hgc : IntervalIntegrable (fun x => (g x : ℂ)) volume a b :=
      ⟨hg.1.ofReal, hg.2.ofReal⟩
    have hhc : IntervalIntegrable (fun x => (h x : ℂ)) volume a b :=
      ⟨hh.1.ofReal, hh.2.ofReal⟩
    refine ⟨(hgc.add (hhc.mul_const Complex.I)).congr_uIoo (fun x hx => (heq x hx).symm), ?_⟩
    change (∫ x in a..b, f x) = _
    rw [intervalIntegral.integral_congr_uIoo heq,
      intervalIntegral.integral_add hgc (hhc.mul_const Complex.I),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal]
    rfl
  | icc =>
    simp only [NDomain.Converges, NDomain.CConverges, NDomain.value, NDomain.cvalue,
      IntegrableOn, ← restrict_Ioo_eq_restrict_Icc] at hg hh ⊢
    exact integral_components hg hh (ae_restrict_of_forall_mem measurableSet_Ioo heq)
  | ioc =>
    simp only [NDomain.Converges, NDomain.CConverges, NDomain.value, NDomain.cvalue,
      IntegrableOn, ← restrict_Ioo_eq_restrict_Ioc] at hg hh ⊢
    exact integral_components hg hh (ae_restrict_of_forall_mem measurableSet_Ioo heq)
  | ico =>
    simp only [NDomain.Converges, NDomain.CConverges, NDomain.value, NDomain.cvalue,
      IntegrableOn, ← restrict_Ioo_eq_restrict_Ico] at hg hh ⊢
    exact integral_components hg hh (ae_restrict_of_forall_mem measurableSet_Ioo heq)
  | ioo =>
    exact integral_components hg hh (ae_restrict_of_forall_mem measurableSet_Ioo heq)
  | right =>
    exact integral_components hg hh (ae_restrict_of_forall_mem measurableSet_Ioi heq)
  | left =>
    exact integral_components hg hh (ae_restrict_of_forall_mem measurableSet_Iio heq)
  | whole =>
    exact integral_components hg hh (ae_of_all _ (fun x => heq x (Set.mem_univ x)))
end ComplexProjectionIntegral

theorem CExpr.parts_unary_converges (op : Unary) (a : CExpr) (env : List ℝ) :
    ((CExpr.unary op a).parts.1.Converges env ∧
      (CExpr.unary op a).parts.2.Converges env) ↔
      a.parts.1.Converges env ∧ a.parts.2.Converges env := by
  cases op <;> try (exact CParts.unary_converges _ _ _)
  case inv =>
    cases a with
    | unary op a =>
      cases op <;> try (exact CParts.unary_converges _ _ _)
      case sqrt =>
        simp only [CExpr.parts]
        split
        · rename_i hq
          have hq' : a.parts.2 = .rat 0 := by simpa only [beq_iff_eq] using hq
          simp only [CParts.unary_converges, CParts.un_converges, CParts.neg_converges]
          simp [hq', NExpr.Converges]
        · simp only [CParts.unary_converges]
    | real | i | binary | pow | positivePower | integral =>
      exact CParts.unary_converges _ _ _

theorem CExpr.parts_unary_value (op : Unary) (a : CExpr) (env : List ℝ)
    (hs : (match op with
      | .neg | .inv | .exp | .sqrt | .log | .sin | .cos | .sinh | .cosh => true
      | _ => false) = true)
    (hlog : op = .log → (a.parts.1 == .rat 0) = true → (a.parts.2 == .rat 0) = true) :
    op.complex ((a.parts.1.real env : ℂ) + (a.parts.2.real env : ℂ) * Complex.I) =
    ((CExpr.unary op a).parts.1.real env : ℂ) +
      ((CExpr.unary op a).parts.2.real env : ℂ) * Complex.I := by
  cases op <;> try (exact CParts.unary_value _ _ _ hs hlog)
  case inv =>
    cases a with
    | unary op a =>
      cases op <;> try (exact CParts.unary_value _ _ _ hs hlog)
      case sqrt =>
        simp only [CExpr.parts]
        split
        · rename_i hq
          have hq' : a.parts.2 = .rat 0 := by simpa only [beq_iff_eq] using hq
          change (((CParts.squareRoot a.parts).1.real env : ℂ) +
            ((CParts.squareRoot a.parts).2.real env : ℂ) * Complex.I)⁻¹ = _
          rw [← CParts.squareRoot_value]
          simpa only [hq', CParts.un_real, CParts.neg_real, NExpr.real, Unary.real,
            Rat.cast_zero, Complex.ofReal_zero, Complex.ofReal_neg, zero_mul, add_zero] using
            CParts.inverse_sqrt_real_eq (a.parts.1.real env)
        · exact CParts.inverse_value (CParts.unary .sqrt a.parts) env
    | real | i | binary | pow | positivePower | integral =>
      exact CParts.unary_value _ _ _ hs hlog

theorem CExpr.parts_pow_value (a : CExpr) (n : Nat) (env : List ℝ) :
    ((a.parts.1.real env : ℂ) + (a.parts.2.real env : ℂ) * Complex.I) ^ n =
    ((CExpr.pow a n).parts.1.real env : ℂ) +
      ((CExpr.pow a n).parts.2.real env : ℂ) * Complex.I := by
  simp only [CExpr.parts]
  split
  · rename_i hq
    have hq' : a.parts.2 = .rat 0 := by simpa only [beq_iff_eq] using hq
    simp [hq', NExpr.real]
  · exact CParts.power_value a.parts n env

theorem CExpr.parts_pow_converges (a : CExpr) (n : Nat) (env : List ℝ)
    (hs : n = 0 → a.parts.1.hasIntegral = false ∧ a.parts.2.hasIntegral = false) :
    ((CExpr.pow a n).parts.1.Converges env ∧ (CExpr.pow a n).parts.2.Converges env) ↔
      a.parts.1.Converges env ∧ a.parts.2.Converges env := by
  simp only [CExpr.parts]
  split
  · rename_i hq
    have hq' : a.parts.2 = .rat 0 := by simpa only [beq_iff_eq] using hq
    simp [hq', NExpr.Converges]
  · rw [CParts.power_converges]
    constructor
    · rintro (h0 | h)
      · exact ⟨converges_of_noIntegral (hs h0).1 env,
          converges_of_noIntegral (hs h0).2 env⟩
      · exact h
    · exact Or.inr

theorem CExpr.parts_positivePower_converges (b : ℚ) (a : CExpr) (env : List ℝ) :
    ((CExpr.positivePower b a).parts.1.Converges env ∧
      (CExpr.positivePower b a).parts.2.Converges env) ↔
      a.parts.1.Converges env ∧ a.parts.2.Converges env := by
  simp [CExpr.parts, NExpr.Converges]

theorem CExpr.parts_positivePower_value (b : ℚ) (a : CExpr) (env : List ℝ) (hb : 0 < b) :
    (b : ℂ) ^ ((a.parts.1.real env : ℂ) + (a.parts.2.real env : ℂ) * Complex.I) =
    ((CExpr.positivePower b a).parts.1.real env : ℂ) +
      ((CExpr.positivePower b a).parts.2.real env : ℂ) * Complex.I := by
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  have hblog : Complex.log (b : ℂ) = (Real.log (b : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_ratCast] using (Complex.ofReal_log hbR.le).symm
  rw [Complex.cpow_def_of_ne_zero hbC, hblog]
  have ht := CParts.times_value (CParts.un .log (.rat b), .rat 0) a.parts env
  simp only [CParts.un_real, NExpr.real, Unary.real, Rat.cast_zero,
    Complex.ofReal_zero, zero_mul, add_zero] at ht
  rw [ht]
  exact CParts.exponential_value _ env

/-- Projection commutes with integration only after convergence of both
components is established, including all recursively used inner integrals.
The log-safety hypothesis excludes the known incorrect pure-imaginary branch
of the current projection formula. -/
theorem CExpr.parts_sound {e : CExpr} {env : List ℝ} (hs : e.Supported)
    (hlog : e.LogProjectionSafe)
    (hr : e.parts.1.Converges env) (hi : e.parts.2.Converges env) :
    e.Converges env ∧
      e.value env = (e.parts.1.real env : ℂ) + (e.parts.2.real env : ℂ)*Complex.I := by
  induction e generalizing env with
  | real a =>
    refine ⟨hr, ?_⟩
    simp [CExpr.parts, CExpr.value, NExpr.real]
  | i => simp [CExpr.parts, CExpr.value, CExpr.Converges, NExpr.real]
  | unary op a ih =>
    have hp := (CExpr.parts_unary_converges op a env).1 ⟨hr, hi⟩
    obtain ⟨hc, hv⟩ := ih hs.1 hlog.1 hp.1 hp.2
    refine ⟨hc, ?_⟩
    change op.complex (a.value env) = _
    rw [hv]
    exact CExpr.parts_unary_value op a env hs.2 hlog.2
  | binary op a b iha ihb =>
    have hp := (CParts.binary_converges op a.parts b.parts env hs.2.2).1 ⟨hr, hi⟩
    obtain ⟨hca, hva⟩ := iha hs.1 hlog.1 hp.1.1 hp.1.2
    obtain ⟨hcb, hvb⟩ := ihb hs.2.1 hlog.2 hp.2.1 hp.2.2
    refine ⟨⟨hca, hcb⟩, ?_⟩
    change op.complex (a.value env) (b.value env) = _
    rw [hva, hvb]
    exact CParts.binary_value op a.parts b.parts env hs.2.2
  | pow a n ih =>
    have hp := (CExpr.parts_pow_converges a n env hs.2).1 ⟨hr, hi⟩
    obtain ⟨hc, hv⟩ := ih hs.1 hlog hp.1 hp.2
    refine ⟨hc, ?_⟩
    change a.value env ^ n = _
    rw [hv]
    exact CExpr.parts_pow_value a n env
  | positivePower b a ih =>
    have hp := (CExpr.parts_positivePower_converges b a env).1 ⟨hr, hi⟩
    obtain ⟨hc, hv⟩ := ih hs.2 hlog hp.1 hp.2
    refine ⟨hc, ?_⟩
    change (b : ℂ) ^ a.value env = _
    rw [hv]
    exact CExpr.parts_positivePower_value b a env hs.1
  | integral k a b f ih =>
    simp only [CExpr.parts, NExpr.Converges] at hr hi
    have hp := NDomain.components_sound k hr.2.2.1 hi.2.2.1
      (fun x hx => (ih hs hlog (hr.2.2.2 x hx) (hi.2.2.2 x hx)).2)
    exact ⟨⟨hr.1, hr.2.1, hp.1,
      fun x hx => (ih hs hlog (hr.2.2.2 x hx) (hi.2.2.2 x hx)).1⟩, hp.2⟩

theorem NDomain.cvalue_congr (k : NDomain) {f g : ℝ → ℂ} {a b c d : ℝ}
    (hf : ∀ x, f x = g x) (ha : a = c) (hb : b = d) :
    k.cvalue f a b = k.cvalue g c d := by rw [funext hf,ha,hb]

/-- Componentwise certified errors imply a strict complex norm error. -/
theorem CExpr.close_of_parts {e : CExpr} {env : List ℝ} {q r : ℚ} {tol : ℝ}
    (hs : e.Supported) (hlog : e.LogProjectionSafe)
    (hr : e.parts.1.Converges env ∧ |e.parts.1.real env-(q:ℝ)| < tol/4)
    (hi : e.parts.2.Converges env ∧ |e.parts.2.real env-(r:ℝ)| < tol/4) :
    e.Converges env ∧ ‖e.value env-((q:ℂ)+(r:ℂ)*Complex.I)‖ < tol := by
  obtain ⟨hc,hv⟩ := e.parts_sound hs hlog hr.1 hi.1
  refine ⟨hc,?_⟩
  have hn := Complex.norm_le_abs_re_add_abs_im
    (e.value env-((q:ℂ)+(r:ℂ)*Complex.I))
  rw [hv] at hn ⊢
  simp only [Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.ratCast_re,Complex.ratCast_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,zero_mul,zero_add,add_zero,sub_zero] at hn
  have hp : 0 < tol := by linarith [abs_nonneg (e.parts.1.real env-(q:ℝ))]
  exact lt_of_le_of_lt hn (by linarith [hr.2,hi.2])

theorem complex_result_of_parts {f : ℝ → ℂ} {a b tol : ℝ}
    {e : CExpr} {A B : NExpr} {k : NDomain} {q r : ℚ}
    (hs : e.Supported) (hlog : e.LogProjectionSafe) (hf : ∀ x, f x = e.value [x])
    (ha : a = A.real []) (hb : b = B.real [])
    (hr : (CExpr.integral k A B e).parts.1.Converges [] ∧
      |(CExpr.integral k A B e).parts.1.real []-(q:ℝ)| < tol/4)
    (hi : (CExpr.integral k A B e).parts.2.Converges [] ∧
      |(CExpr.integral k A B e).parts.2.real []-(r:ℝ)| < tol/4) :
    k.CConverges f a b ∧ ‖k.cvalue f a b-((q:ℂ)+(r:ℂ)*Complex.I)‖ < tol := by
  obtain rfl : f = fun x => e.value [x] := funext hf
  subst a; subst b
  have h := CExpr.close_of_parts (e := .integral k A B e) hs hlog hr hi
  exact ⟨h.1.2.2.1,h.2⟩

end Intgrl
