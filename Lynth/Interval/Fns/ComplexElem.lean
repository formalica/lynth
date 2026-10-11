import Lynth.Interval.Fns.Exp
import Lynth.Interval.Fns.Trig
import Lynth.Interval.Fns.Elem

/-!
# Complex elementary functions via real/imaginary components.

`exp/sin/cos/sinh/cosh` evaluate through the existing real interval
evaluators on the rectangle's projections; `tan/tanh` divide the boxes.
Each function gets a complex-level equation (proved by `ring` from the
addition laws) plus `re`/`im` projections; every entry's soundness is
proved inline (no sorries).
-/

namespace Complex

/-- `sin` as real combination plus `I` part. -/
theorem sin_of (x : ℂ) :
    Complex.sin x = ((Real.sin x.re * Real.cosh x.im : ℝ) : ℂ)
      + ((Real.cos x.re * Real.sinh x.im : ℝ) : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im x]
  rw [Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  push_cast
  ring

/-- `sin` real part. -/
theorem sin_re_of (x : ℂ) :
    (Complex.sin x).re = Real.sin x.re * Real.cosh x.im := by
  rw [sin_of]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, one_mul,
    sub_zero, add_zero] <;> ring

/-- `sin` imaginary part. -/
theorem sin_im_of (x : ℂ) :
    (Complex.sin x).im = Real.cos x.re * Real.sinh x.im := by
  rw [sin_of]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, one_mul,
    sub_zero, add_zero, zero_add] <;> ring

/-- `cos` as real combination plus `I` part. -/
theorem cos_of (x : ℂ) :
    Complex.cos x = ((Real.cos x.re * Real.cosh x.im : ℝ) : ℂ)
      + ((-Real.sin x.re * Real.sinh x.im : ℝ) : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im x]
  rw [Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  push_cast
  ring

/-- `cos` real part. -/
theorem cos_re_of (x : ℂ) :
    (Complex.cos x).re = Real.cos x.re * Real.cosh x.im := by
  rw [cos_of]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, one_mul,
    sub_zero, add_zero] <;> ring

/-- `cos` imaginary part. -/
theorem cos_im_of (x : ℂ) :
    (Complex.cos x).im = -(Real.sin x.re * Real.sinh x.im) := by
  rw [cos_of]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, one_mul,
    sub_zero, add_zero, zero_add] <;> ring

/-- `sinh` as real combination plus `I` part. -/
theorem sinh_of (x : ℂ) :
    Complex.sinh x = ((Real.sinh x.re * Real.cos x.im : ℝ) : ℂ)
      + ((Real.cosh x.re * Real.sin x.im : ℝ) : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im x]
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  push_cast
  ring

/-- `sinh` real part. -/
theorem sinh_re_of (x : ℂ) :
    (Complex.sinh x).re = Real.sinh x.re * Real.cos x.im := by
  rw [sinh_of]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, one_mul,
    sub_zero, add_zero] <;> ring

/-- `sinh` imaginary part. -/
theorem sinh_im_of (x : ℂ) :
    (Complex.sinh x).im = Real.cosh x.re * Real.sin x.im := by
  rw [sinh_of]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, one_mul,
    sub_zero, add_zero, zero_add] <;> ring

/-- `cosh` as real combination plus `I` part. -/
theorem cosh_of (x : ℂ) :
    Complex.cosh x = ((Real.cosh x.re * Real.cos x.im : ℝ) : ℂ)
      + ((Real.sinh x.re * Real.sin x.im : ℝ) : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im x]
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  push_cast
  ring

/-- `cosh` real part. -/
theorem cosh_re_of (x : ℂ) :
    (Complex.cosh x).re = Real.cosh x.re * Real.cos x.im := by
  rw [cosh_of]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, one_mul,
    sub_zero, add_zero] <;> ring

/-- `cosh` imaginary part. -/
theorem cosh_im_of (x : ℂ) :
    (Complex.cosh x).im = Real.sinh x.re * Real.sin x.im := by
  rw [cosh_of]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, one_mul,
    sub_zero, add_zero, zero_add] <;> ring

end Complex

namespace Lynth.Interval.Fns

open Lynth.Interval

/-- `exp` on rectangles. -/
def expBox (c : Ctx) (B : CBox) : CBox :=
  ⟨Ival.mul c.prec (expIval c B.re) (cosIval c B.im),
   Ival.mul c.prec (expIval c B.re) (sinIval c B.im)⟩

theorem mem_expBox (c : Ctx) (hc : c.Valid) {x : ℂ} {B : CBox} (hx : x ∈ B) :
    Complex.exp x ∈ expBox c B := by
  show (Complex.exp x).re ∈ _ ∧ (Complex.exp x).im ∈ _
  rw [Complex.exp_re, Complex.exp_im]
  exact ⟨Ival.mem_mul (mem_expIval c hx.1) (mem_cosIval hc hx.2),
    Ival.mem_mul (mem_expIval c hx.1) (mem_sinIval hc hx.2)⟩

/-- `sin` on rectangles. -/
def sinBox (c : Ctx) (B : CBox) : CBox :=
  ⟨Ival.mul c.prec (sinIval c B.re) (coshIval c B.im),
   Ival.mul c.prec (cosIval c B.re) (sinhIval c B.im)⟩

theorem mem_sinBox (c : Ctx) (hc : c.Valid) {x : ℂ} {B : CBox} (hx : x ∈ B) :
    Complex.sin x ∈ sinBox c B := by
  show (Complex.sin x).re ∈ _ ∧ (Complex.sin x).im ∈ _
  rw [Complex.sin_re_of, Complex.sin_im_of]
  exact ⟨Ival.mem_mul (mem_sinIval hc hx.1) (mem_coshIval c hx.2),
    Ival.mem_mul (mem_cosIval hc hx.1) (mem_sinhIval c hx.2)⟩

/-- `cos` on rectangles. -/
def cosBox (c : Ctx) (B : CBox) : CBox :=
  ⟨Ival.mul c.prec (cosIval c B.re) (coshIval c B.im),
   Ival.neg (Ival.mul c.prec (sinIval c B.re) (sinhIval c B.im))⟩

theorem mem_cosBox (c : Ctx) (hc : c.Valid) {x : ℂ} {B : CBox} (hx : x ∈ B) :
    Complex.cos x ∈ cosBox c B := by
  show (Complex.cos x).re ∈ _ ∧ (Complex.cos x).im ∈ _
  rw [Complex.cos_re_of, Complex.cos_im_of]
  exact ⟨Ival.mem_mul (mem_cosIval hc hx.1) (mem_coshIval c hx.2),
    Ival.mem_neg (Ival.mem_mul (mem_sinIval hc hx.1) (mem_sinhIval c hx.2))⟩

/-- `sinh` on rectangles. -/
def sinhBox (c : Ctx) (B : CBox) : CBox :=
  ⟨Ival.mul c.prec (sinhIval c B.re) (cosIval c B.im),
   Ival.mul c.prec (coshIval c B.re) (sinIval c B.im)⟩

theorem mem_sinhBox (c : Ctx) (hc : c.Valid) {x : ℂ} {B : CBox} (hx : x ∈ B) :
    Complex.sinh x ∈ sinhBox c B := by
  show (Complex.sinh x).re ∈ _ ∧ (Complex.sinh x).im ∈ _
  rw [Complex.sinh_re_of, Complex.sinh_im_of]
  exact ⟨Ival.mem_mul (mem_sinhIval c hx.1) (mem_cosIval hc hx.2),
    Ival.mem_mul (mem_coshIval c hx.1) (mem_sinIval hc hx.2)⟩

/-- `cosh` on rectangles. -/
def coshBox (c : Ctx) (B : CBox) : CBox :=
  ⟨Ival.mul c.prec (coshIval c B.re) (cosIval c B.im),
   Ival.mul c.prec (sinhIval c B.re) (sinIval c B.im)⟩

theorem mem_coshBox (c : Ctx) (hc : c.Valid) {x : ℂ} {B : CBox} (hx : x ∈ B) :
    Complex.cosh x ∈ coshBox c B := by
  show (Complex.cosh x).re ∈ _ ∧ (Complex.cosh x).im ∈ _
  rw [Complex.cosh_re_of, Complex.cosh_im_of]
  exact ⟨Ival.mem_mul (mem_coshIval c hx.1) (mem_cosIval hc hx.2),
    Ival.mem_mul (mem_sinhIval c hx.1) (mem_sinIval hc hx.2)⟩

@[lynth_cfn] def expC : Fn1 .cplx .cplx where
  name := "Complex.exp"
  graph x y := y = Complex.exp x
  exu := exu_eq _
  ev c B := expBox c B
  sound := fun c _ _ _ hc hy hx => by
    obtain rfl := hy
    exact mem_expBox c hc hx
  cost := 100

@[lynth_cfn] def sinC : Fn1 .cplx .cplx where
  name := "Complex.sin"
  graph x y := y = Complex.sin x
  exu := exu_eq _
  ev c B := sinBox c B
  sound := fun c _ _ _ hc hy hx => by
    obtain rfl := hy
    exact mem_sinBox c hc hx
  cost := 100

@[lynth_cfn] def cosC : Fn1 .cplx .cplx where
  name := "Complex.cos"
  graph x y := y = Complex.cos x
  exu := exu_eq _
  ev c B := cosBox c B
  sound := fun c _ _ _ hc hy hx => by
    obtain rfl := hy
    exact mem_cosBox c hc hx
  cost := 100

@[lynth_cfn] def tanC : Fn1 .cplx .cplx where
  name := "Complex.tan"
  graph x y := y = Complex.tan x
  exu := exu_eq _
  ev c B := CBox.div c.prec (sinBox c B) (cosBox c B)
  sound := fun c _ _ _ hc hy hx => by
    obtain rfl := hy
    rw [Complex.tan_eq_sin_div_cos]
    exact CBox.mem_div (mem_sinBox c hc hx) (mem_cosBox c hc hx)
  cost := 100

@[lynth_cfn] def sinhC : Fn1 .cplx .cplx where
  name := "Complex.sinh"
  graph x y := y = Complex.sinh x
  exu := exu_eq _
  ev c B := sinhBox c B
  sound := fun c _ _ _ hc hy hx => by
    obtain rfl := hy
    exact mem_sinhBox c hc hx
  cost := 100

@[lynth_cfn] def coshC : Fn1 .cplx .cplx where
  name := "Complex.cosh"
  graph x y := y = Complex.cosh x
  exu := exu_eq _
  ev c B := coshBox c B
  sound := fun c _ _ _ hc hy hx => by
    obtain rfl := hy
    exact mem_coshBox c hc hx
  cost := 100

@[lynth_cfn] def tanhC : Fn1 .cplx .cplx where
  name := "Complex.tanh"
  graph x y := y = Complex.tanh x
  exu := exu_eq _
  ev c B := CBox.div c.prec (sinhBox c B) (coshBox c B)
  sound := fun c _ _ _ hc hy hx => by
    obtain rfl := hy
    rw [Complex.tanh_eq_sinh_div_cosh]
    exact CBox.mem_div (mem_sinhBox c hc hx) (mem_coshBox c hc hx)
  cost := 100

end Lynth.Interval.Fns
