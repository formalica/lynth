import Lynth.Interval.Integral.Math.NestedSyntax

/-! Mathematical specification of complex-valued integrals over real variables.
No interval encodings, numerical evaluators or tactic implementation occur here.
The admitted projection theorem is mirrored in /tmp/intgrl. -/
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

/-- Projection commutes with integration only after convergence of both
components is established, including all recursively used inner integrals. -/
theorem CExpr.parts_sound {e : CExpr} {env : List ℝ} (hs : e.Supported)
    (hr : e.parts.1.Converges env) (hi : e.parts.2.Converges env) :
    e.Converges env ∧
      e.value env = (e.parts.1.real env : ℂ) + (e.parts.2.real env : ℂ)*Complex.I := by
  sorry

theorem NDomain.cvalue_congr (k : NDomain) {f g : ℝ → ℂ} {a b c d : ℝ}
    (hf : ∀ x, f x = g x) (ha : a = c) (hb : b = d) :
    k.cvalue f a b = k.cvalue g c d := by rw [funext hf,ha,hb]

/-- Componentwise certified errors imply a strict complex norm error. -/
theorem CExpr.close_of_parts {e : CExpr} {env : List ℝ} {q r : ℚ} {tol : ℝ}
    (hs : e.Supported)
    (hr : e.parts.1.Converges env ∧ |e.parts.1.real env-(q:ℝ)| < tol/4)
    (hi : e.parts.2.Converges env ∧ |e.parts.2.real env-(r:ℝ)| < tol/4) :
    e.Converges env ∧ ‖e.value env-((q:ℂ)+(r:ℂ)*Complex.I)‖ < tol := by
  obtain ⟨hc,hv⟩ := e.parts_sound hs hr.1 hi.1
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
    (hs : e.Supported) (hf : ∀ x, f x = e.value [x])
    (ha : a = A.real []) (hb : b = B.real [])
    (hr : (CExpr.integral k A B e).parts.1.Converges [] ∧
      |(CExpr.integral k A B e).parts.1.real []-(q:ℝ)| < tol/4)
    (hi : (CExpr.integral k A B e).parts.2.Converges [] ∧
      |(CExpr.integral k A B e).parts.2.real []-(r:ℝ)| < tol/4) :
    k.CConverges f a b ∧ ‖k.cvalue f a b-((q:ℂ)+(r:ℂ)*Complex.I)‖ < tol := by
  obtain rfl : f = fun x => e.value [x] := funext hf
  subst a; subst b
  have h := CExpr.close_of_parts (e := .integral k A B e) hs hr hi
  exact ⟨h.1.2.2.1,h.2⟩

end Intgrl
