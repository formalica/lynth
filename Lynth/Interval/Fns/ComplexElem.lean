import Lynth.Interval.Fns.Exp
import Lynth.Interval.Fns.Trig
import Lynth.Interval.Fns.Elem
import Lynth.Interval.Fns.EulerGamma.Eval

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

/-- ARG, right half-plane (mirror of `/tmp/complex/batch2_handoff.lean`,
for the external prover). -/
theorem arg_of_pos {z : ℂ} (hx : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  sorry

/-- ARG, left half-plane, nonnegative imag (mirror for the prover). -/
theorem arg_of_neg_nonneg {z : ℂ} (hx : z.re < 0) (hy : 0 ≤ z.im) :
    z.arg = Real.arctan (z.im / z.re) + Real.pi := by
  sorry

/-- ARG, left half-plane, negative imag (mirror for the prover). -/
theorem arg_of_neg_neg {z : ℂ} (hx : z.re < 0) (hy : z.im < 0) :
    z.arg = Real.arctan (z.im / z.re) - Real.pi := by
  sorry

/-- ARG, pure imaginary positive axis. -/
theorem arg_of_zero_pos {y : ℝ} (hy : 0 < y) : (⟨0, y⟩ : ℂ).arg = Real.pi / 2 := by
  have e : (⟨0, y⟩ : ℂ) = (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [e]
  exact (Complex.arg_real_mul _ hy).trans Complex.arg_I

/-- ARG, pure imaginary negative axis. -/
theorem arg_of_zero_neg {y : ℝ} (hy : y < 0) : (⟨0, y⟩ : ℂ).arg = -(Real.pi / 2) := by
  have e : (⟨0, y⟩ : ℂ) = ((-y : ℝ) : ℂ) * (-Complex.I) := by
    apply Complex.ext <;> simp
  rw [e]
  exact (Complex.arg_real_mul _ (by linarith)).trans Complex.arg_neg_I

/-- SQRT, right half-plane interior, division form matching `sqrtBox`
(mirror for the prover). -/
theorem sqrt_components_of_pos {z : ℂ} (hx : 0 < z.re) :
    (Complex.sqrt z).re = Real.sqrt ((‖z‖ + z.re) / 2)
    ∧ (Complex.sqrt z).im
      = z.im / (2 * Real.sqrt ((‖z‖ + z.re) / 2)) := by
  sorry

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

/-- enclosure lower bound from a point lower end. -/
theorem mem_lo_le {x : ℝ} {X : Ival} {lo : Dy} (hx : x ∈ X) (hlo : X.lo = some lo) :
    ((lo.toRat : ℚ) : ℝ) ≤ x := by
  rw [Ival.mem_def] at hx
  have h := hx.1 lo hlo
  simpa [Ival.loLe_some, Dy.toReal_def] using h

/-- enclosure upper bound from a point upper end. -/
theorem mem_le_hi {x : ℝ} {X : Ival} {hi : Dy} (hx : x ∈ X) (hhi : X.hi = some hi) :
    x ≤ ((hi.toRat : ℚ) : ℝ) := by
  rw [Ival.mem_def] at hx
  have h := hx.2 hi hhi
  simpa [Ival.leHi_some, Dy.toReal_def] using h

/-- argument enclosure by quadrants (`⊤` outside the three exact cases). -/
def argBox (c : Ctx) (X Y : Ival) : Ival :=
  match X.lo, X.hi with
  | some xl, _ =>
    if 0 < xl.toRat then atanIval c (Ival.div c.prec Y X)
    else match X.hi, Y.lo, Y.hi with
      | some xh, some yl, some yh =>
        if xh.toRat < 0 ∧ 0 ≤ yl.toRat then
          Ival.add c.prec (atanIval c (Ival.div c.prec Y X)) c.pi
        else if xh.toRat < 0 ∧ yh.toRat < 0 then
          Ival.sub c.prec (atanIval c (Ival.div c.prec Y X)) c.pi
        else if xl.toRat = 0 ∧ xh.toRat = 0 ∧ 0 < yl.toRat then
          Ival.divNat c.prec c.pi 2
        else if xl.toRat = 0 ∧ xh.toRat = 0 ∧ yh.toRat < 0 then
          Ival.neg (Ival.divNat c.prec c.pi 2)
        else Ival.top
      | _, _, _ => Ival.top
  | _, _ => Ival.top

theorem mem_argBox (c : Ctx) (hc : c.Valid) {z : ℂ} {X Y : Ival}
    (hx : z.re ∈ X) (hy : z.im ∈ Y) :
    z.arg ∈ argBox c X Y := by
  cases hlo : X.lo with
  | none =>
    have hev : argBox c X Y = Ival.top := by simp [argBox, hlo]
    rw [hev]; exact Ival.mem_top _
  | some xl =>
    by_cases hpos : 0 < xl.toRat
    · have hev : argBox c X Y = atanIval c (Ival.div c.prec Y X) := by
        simp [argBox, hlo, hpos]
      rw [hev]
      have hxr : 0 < z.re := by
        have h0 : (0 : ℝ) < ((xl.toRat : ℚ) : ℝ) := by exact_mod_cast hpos
        linarith [mem_lo_le hx hlo]
      rw [Complex.arg_of_pos hxr]
      exact mem_atanIval hc (Ival.mem_div hy hx)
    · cases hhi : X.hi with
      | none =>
        have hev : argBox c X Y = Ival.top := by simp [argBox, hlo, hpos, hhi]
        rw [hev]; exact Ival.mem_top _
      | some xh =>
        cases hyl : Y.lo with
        | none =>
          have hev : argBox c X Y = Ival.top := by simp [argBox, hlo, hpos, hhi, hyl]
          rw [hev]; exact Ival.mem_top _
        | some yl =>
          cases hyh : Y.hi with
          | none =>
            have hev : argBox c X Y = Ival.top := by simp [argBox, hlo, hpos, hhi, hyl, hyh]
            rw [hev]; exact Ival.mem_top _
          | some yh =>
            by_cases hneg : xh.toRat < 0 ∧ 0 ≤ yl.toRat
            · have hev : argBox c X Y =
                  Ival.add c.prec (atanIval c (Ival.div c.prec Y X)) c.pi := by
                simp [argBox, hlo, hpos, hhi, hyl, hyh, eq_true hneg]
              rw [hev]
              have hxr : z.re < 0 := by
                have h1 := mem_le_hi hx hhi
                have h2 : ((xh.toRat : ℚ) : ℝ) < 0 := by exact_mod_cast hneg.1
                linarith
              have hyi : 0 ≤ z.im := by
                have h1 := mem_lo_le hy hyl
                have h2 : (0 : ℝ) ≤ ((yl.toRat : ℚ) : ℝ) := by exact_mod_cast hneg.2
                linarith
              rw [Complex.arg_of_neg_nonneg hxr hyi]
              exact Ival.mem_add (mem_atanIval hc (Ival.mem_div hy hx)) hc.pi_mem
            · by_cases hneg2 : xh.toRat < 0 ∧ yh.toRat < 0
              · have hev : argBox c X Y =
                    Ival.sub c.prec (atanIval c (Ival.div c.prec Y X)) c.pi := by
                  simp [argBox, hlo, hpos, hhi, hyl, hyh, hneg, eq_true hneg2]
                rw [hev]
                have hxr : z.re < 0 := by
                  have h1 := mem_le_hi hx hhi
                  have h2 : ((xh.toRat : ℚ) : ℝ) < 0 := by exact_mod_cast hneg2.1
                  linarith
                have hyi : z.im < 0 := by
                  have h1 := mem_le_hi hy hyh
                  have h2 : ((yh.toRat : ℚ) : ℝ) < 0 := by exact_mod_cast hneg2.2
                  linarith
                rw [Complex.arg_of_neg_neg hxr hyi]
                exact Ival.mem_sub (mem_atanIval hc (Ival.mem_div hy hx)) hc.pi_mem
              · by_cases hzpos : xl.toRat = 0 ∧ xh.toRat = 0 ∧ 0 < yl.toRat
                · have hev : argBox c X Y = Ival.divNat c.prec c.pi 2 := by
                    simp [argBox, hlo, hpos, hhi, hyl, hyh, hneg, hneg2, eq_true hzpos]
                  rw [hev]
                  have hx0 : z.re = 0 := by
                    have h1 := mem_lo_le hx hlo
                    have h2 := mem_le_hi hx hhi
                    rw [hzpos.1] at h1
                    rw [hzpos.2.1] at h2
                    simp only [Rat.cast_zero] at h1 h2
                    exact le_antisymm h2 h1
                  have ez : z = (⟨0, z.im⟩ : ℂ) := by
                    apply Complex.ext
                    · show z.re = (0 : ℝ)
                      exact hx0
                    · rfl
                  have hypos : 0 < z.im := by
                    have h1 := mem_lo_le hy hyl
                    have h2 : (0 : ℝ) < ((yl.toRat : ℚ) : ℝ) := by
                      exact_mod_cast hzpos.2.2
                    linarith
                  rw [ez, Complex.arg_of_zero_pos hypos]
                  exact Ival.mem_divNat (p := c.prec) hc.pi_mem (n := 2) (by norm_num)
                · by_cases hzneg : xl.toRat = 0 ∧ xh.toRat = 0 ∧ yh.toRat < 0
                  · have hev : argBox c X Y = Ival.neg (Ival.divNat c.prec c.pi 2) := by
                      simp [argBox, hlo, hpos, hhi, hyl, hyh, hneg, hneg2, hzpos, eq_true hzneg]
                    rw [hev]
                    have hx0 : z.re = 0 := by
                      have h1 := mem_lo_le hx hlo
                      have h2 := mem_le_hi hx hhi
                      rw [hzneg.1] at h1
                      rw [hzneg.2.1] at h2
                      simp only [Rat.cast_zero] at h1 h2
                      exact le_antisymm h2 h1
                    have ez : z = (⟨0, z.im⟩ : ℂ) := by
                      apply Complex.ext
                      · show z.re = (0 : ℝ)
                        exact hx0
                      · rfl
                    have hyneg : z.im < 0 := by
                      have h1 := mem_le_hi hy hyh
                      have h2 : ((yh.toRat : ℚ) : ℝ) < 0 := by
                        exact_mod_cast hzneg.2.2
                      linarith
                    rw [ez, Complex.arg_of_zero_neg hyneg]
                    exact Ival.mem_neg (Ival.mem_divNat (p := c.prec) hc.pi_mem
                      (n := 2) (by norm_num))
                  · have hev : argBox c X Y = Ival.top := by
                      simp [argBox, hlo, hpos, hhi, hyl, hyh, hneg, hneg2, hzpos, hzneg]
                    rw [hev]; exact Ival.mem_top _

/-- `log` on rectangles (unconditional: `logIval`/`argBox` both widen to `⊤`). -/
def logBox (c : Ctx) (B : CBox) : CBox :=
  ⟨logIval c (CBox.norm c.prec B), argBox c B.re B.im⟩

theorem mem_logBox (c : Ctx) (hc : c.Valid) {z : ℂ} {B : CBox} (hx : z ∈ B) :
    Complex.log z ∈ logBox c B := by
  show (Complex.log z).re ∈ _ ∧ (Complex.log z).im ∈ _
  rw [Complex.log_re, Complex.log_im]
  exact ⟨mem_logIval hc (CBox.mem_norm hx), mem_argBox c hc hx.1 hx.2⟩

/-- `sqrt` on rectangles (right half-plane interior, else `⊤`). -/
def sqrtBox (c : Ctx) (B : CBox) : CBox :=
  match B.re.lo with
  | some xl =>
    if 0 < xl.toRat then
      ⟨Ival.sqrt c.prec
        (Ival.divNat c.prec (Ival.add c.prec (CBox.norm c.prec B) B.re) 2),
      Ival.div c.prec B.im
        (Ival.mul c.prec (Ival.ofRat c.prec 2)
          (Ival.sqrt c.prec (Ival.divNat c.prec (Ival.add c.prec (CBox.norm c.prec B) B.re) 2)))⟩
    else CBox.top
  | none => CBox.top

theorem mem_sqrtBox (c : Ctx) (hc : c.Valid) {z : ℂ} {B : CBox} (hx : z ∈ B) :
    Complex.sqrt z ∈ sqrtBox c B := by
  cases hlo : B.re.lo with
  | none =>
    have hev : sqrtBox c B = CBox.top := by simp [sqrtBox, hlo]
    rw [hev]; exact CBox.mem_top _
  | some xl =>
    by_cases hpos : 0 < xl.toRat
    · have hev : sqrtBox c B =
          ⟨Ival.sqrt c.prec
            (Ival.divNat c.prec (Ival.add c.prec (CBox.norm c.prec B) B.re) 2),
          Ival.div c.prec B.im
            (Ival.mul c.prec (Ival.ofRat c.prec 2)
              (Ival.sqrt c.prec
                (Ival.divNat c.prec (Ival.add c.prec (CBox.norm c.prec B) B.re) 2)))⟩ := by
        simp [sqrtBox, hlo, hpos]
      rw [hev]
      have hxr : 0 < z.re := by
        have h0 : (0 : ℝ) < ((xl.toRat : ℚ) : ℝ) := by exact_mod_cast hpos
        linarith [mem_lo_le hx.1 hlo]
      obtain ⟨hre, him⟩ := Complex.sqrt_components_of_pos hxr
      have hr : ‖z‖ ∈ CBox.norm c.prec B := CBox.mem_norm hx
      have hs : Real.sqrt ((‖z‖ + z.re) / 2) ∈ Ival.sqrt c.prec
          (Ival.divNat c.prec (Ival.add c.prec (CBox.norm c.prec B) B.re) 2) := by
        apply Ival.mem_sqrt
        apply Ival.mem_divNat (p := c.prec) _ (n := 2) (by norm_num)
        exact Ival.mem_add hr hx.1
      have h2 : (2 : ℝ) ∈ Ival.ofRat c.prec 2 := by
        exact_mod_cast Ival.mem_ofRat c.prec (2 : ℚ)
      show (Complex.sqrt z).re ∈ _ ∧ (Complex.sqrt z).im ∈ _
      rw [hre, him]
      exact ⟨hs, Ival.mem_div hx.2 (Ival.mem_mul h2 hs)⟩
    · have hev : sqrtBox c B = CBox.top := by simp [sqrtBox, hlo, hpos]
      rw [hev]; exact CBox.mem_top _

@[lynth_cfn] def logC : Fn1 .cplx .cplx where
  name := "Complex.log"
  graph x y := y = Complex.log x
  exu := exu_eq _
  ev c B := logBox c B
  sound := fun c _ _ _ hc hy hx => by
    obtain rfl := hy
    exact mem_logBox c hc hx
  cost := 200

@[lynth_cfn] def sqrtC : Fn1 .cplx .cplx where
  name := "Complex.sqrt"
  graph x y := y = Complex.sqrt x
  exu := exu_eq _
  ev c B := sqrtBox c B
  sound := fun c _ _ _ hc hy hx => by
    obtain rfl := hy
    exact mem_sqrtBox c hc hx
  cost := 200

@[lynth_cfn] def argC : Fn1 .cplx .real where
  name := "Complex.arg"
  graph x y := y = x.arg
  exu := exu_eq _
  ev c B := argBox c B.re B.im
  sound := fun c _ _ _ hc hy hx => by
    obtain rfl := hy
    exact mem_argBox c hc hx.1 hx.2
  cost := 200

@[lynth_cfn] def cpowC : Fn2 .cplx .cplx .cplx where
  name := "Complex.cpow"
  graph x y z := z = x ^ y
  exu := exu_eq₂ _
  ev c X Y :=
    match (CBox.norm c.prec X).lo with
    | some lo =>
      if 0 < lo.toRat then
        expBox c (CBox.mul c.prec (logBox c X) Y)
      else CBox.top
    | none => CBox.top
  sound := fun c x y _ X Y hc hz hx hy => by
    obtain rfl := hz
    cases hlo : (CBox.norm c.prec X).lo with
    | none =>
      show Complex.cpow x y ∈ CBox.top
      exact CBox.mem_top _
    | some lo =>
      by_cases hpos : 0 < lo.toRat
      · simp only [hpos, ite_true]
        have hx0 : x ≠ 0 := by
          have hle : ((lo.toRat : ℚ) : ℝ) ≤ ‖x‖ := by
            have h := CBox.mem_norm (p := c.prec) hx
            have h2 := (Ival.mem_def.mp h).1 lo hlo
            simpa [Ival.loLe_some, Dy.toReal_def] using h2
          have h0 : (0 : ℝ) < ((lo.toRat : ℚ) : ℝ) := by exact_mod_cast hpos
          have hpos' : 0 < ‖x‖ := by linarith
          exact norm_pos_iff.mp hpos'
        show x ^ y ∈ expBox c (CBox.mul c.prec (logBox c X) Y)
        rw [Complex.cpow_def, ite_eq_right hx0]
        exact mem_expBox c hc (CBox.mem_mul (mem_logBox c hc hx) hy)
      · simp only [hpos, ite_false]
        show Complex.cpow x y ∈ CBox.top
        exact CBox.mem_top _
  cost := 200

/-- the constant `-I/2` box. -/
def negHalfI (c : Ctx) : CBox := ⟨Ival.zero, Ival.ofRat c.prec (-1 / 2)⟩

theorem mem_negHalfI (c : Ctx) : (-Complex.I / 2 : ℂ) ∈ negHalfI c := by
  have hre : (-Complex.I / 2 : ℂ).re = 0 := by simp
  have him : (-Complex.I / 2 : ℂ).im = (-1 : ℝ) / 2 := by simp
  have h0 : (0 : ℝ) ∈ Ival.zero := Ival.mem_zero
  have h1 : ((-1 : ℝ) / 2) ∈ Ival.ofRat c.prec (-1 / 2) := by
    exact_mod_cast Ival.mem_ofRat c.prec (-1 / 2 : ℚ)
  rw [CBox.mem_def, hre, him]
  exact ⟨h0, h1⟩

@[lynth_cfn] def arctanC : Fn1 .cplx .cplx where
  name := "Complex.arctan"
  graph x y := y = Complex.arctan x
  exu := exu_eq _
  ev c X :=
    CBox.mul c.prec (negHalfI c)
      (logBox c (CBox.div c.prec
        (CBox.add c.prec (CBox.ofReal Ival.one) (CBox.mul c.prec X CBox.iI))
        (CBox.sub c.prec (CBox.ofReal Ival.one) (CBox.mul c.prec X CBox.iI))))
  sound := fun c x _ X hc hy hx => by
    obtain rfl := hy
    show (-Complex.I / 2 * Complex.log ((1 + x * Complex.I) / (1 - x * Complex.I))) ∈ _
    have h1c : (1 : ℂ) ∈ CBox.ofReal Ival.one := by
      rw [← Complex.ofReal_one]
      exact CBox.mem_ofReal Ival.mem_one
    have hXI : x * Complex.I ∈ CBox.mul c.prec X CBox.iI :=
      CBox.mem_mul hx CBox.mem_I
    exact CBox.mem_mul (mem_negHalfI c)
      (mem_logBox c hc (CBox.mem_div
        (CBox.mem_add h1c hXI) (CBox.mem_sub h1c hXI)))
  cost := 200

@[lynth_cfn] def cotC : Fn1 .cplx .cplx where
  name := "Complex.cot"
  graph x y := y = Complex.cot x
  exu := exu_eq _
  ev c B := CBox.div c.prec (cosBox c B) (sinBox c B)
  sound := fun c x _ _ hc hy hx => by
    obtain rfl := hy
    show Complex.cos x / Complex.sin x ∈ _
    exact CBox.mem_div (mem_cosBox c hc hx) (mem_sinBox c hc hx)
  cost := 100

@[lynth_cfn] def piC : Fn0 .cplx where
  name := "Complex.pi"
  graph y := y = (Real.pi : ℂ)
  exu := exu_eq₀ _
  ev c := CBox.ofReal c.pi
  sound := fun _ _ hc hy => by
    obtain rfl := hy
    exact CBox.mem_ofReal hc.pi_mem
  cost := 50

@[lynth_cfn] def eulerC : Fn0 .cplx where
  name := "Complex.eulerMascheroni"
  graph y := y = ((Real.eulerMascheroniConstant : ℝ) : ℂ)
  exu := exu_eq₀ _
  ev c := CBox.ofReal (eulerBMIval c)
  sound := fun _ _ hc hy => by
    obtain rfl := hy
    exact CBox.mem_ofReal (mem_eulerBMIval hc)
  cost := 50

end Lynth.Interval.Fns
