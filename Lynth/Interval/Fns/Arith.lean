module

public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Prelude
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Lynth.Interval.Core.Expr
public import Lynth.Interval.Core.Asy
public import Lynth.Interval.Core.Ctx
public import Lynth.Interval.Core.Fn
public import Lynth.Interval.Core.Ty
public import Lynth.Interval.Num.CBox
public import Lynth.Interval.Num.Dy
public import Lynth.Interval.Num.Ival
public import Lynth.Interval.Num.NIval
public import Lynth.Interval.Num.ZIval
public import Lynth.Interval.Series.AsyOps
import all Lynth.Interval.Reify.Registry
import all Lynth.Interval.Series.AsyOps
import Mathlib.Data.Nat.Fib.Basic

/-!
# Arithmetic registry entries (ℕ, ℝ, ℂ)

Field operations, natural powers, absolute value, min/max, square root,
casts, and the complex structure maps.  See `docs/interval/04-functions.md §1`.
-/

namespace Lynth.Interval.Fns

open Lynth.Interval

/-! ### Real field operations -/

@[expose, lynth_cfn] public def addR : Fn2 .real .real .real where
  name := "+"
  graph x y z := z = x + y
  exu := by exact exu_eq₂ _
  ev c X Y := Ival.add c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact Ival.mem_add hx hy
  asy c N A B := RAsy.add c.prec N A B
  asy_sound := fun _ _ _ _ f g h _ hg hA hB => by
    obtain rfl : h = fun k => f k + g k := funext fun k => hg k
    exact RAsy.add_holds hA hB

@[expose, lynth_cfn] public def subR : Fn2 .real .real .real where
  name := "-"
  graph x y z := z = x - y
  exu := by exact exu_eq₂ _
  ev c X Y := Ival.sub c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact Ival.mem_sub hx hy
  asy c N A B := RAsy.add c.prec N A (RAsy.neg B)
  asy_sound := fun _ _ _ _ f g h _ hg hA hB => by
    obtain rfl : h = fun k => f k + -g k := funext fun k => (hg k).trans (sub_eq_add_neg _ _)
    exact RAsy.add_holds hA (RAsy.neg_holds hB)

@[expose, lynth_cfn] public def mulR : Fn2 .real .real .real where
  name := "*"
  graph x y z := z = x * y
  exu := by exact exu_eq₂ _
  ev c X Y := Ival.mul c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact Ival.mem_mul hx hy
  asy c N A B := RAsy.mul c.prec N A B
  asy_sound := fun _ _ _ _ f g h _ hg hA hB => by
    obtain rfl : h = fun k => f k * g k := funext fun k => hg k
    exact RAsy.mul_holds hA hB

@[expose, lynth_cfn] public def divR : Fn2 .real .real .real where
  name := "/"
  graph x y z := z = x / y
  exu := by exact exu_eq₂ _
  ev c X Y := Ival.div c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact Ival.mem_div hx hy
  asy c N A B := RAsy.mul c.prec N A (RAsy.inv c.prec B)
  asy_sound := fun _ _ _ _ f g h _ hg hA hB => by
    obtain rfl : h = fun k => f k * (g k)⁻¹ := funext fun k => (hg k).trans (div_eq_mul_inv _ _)
    exact RAsy.mul_holds hA (RAsy.inv_holds hB)

@[expose, lynth_cfn] public def negR : Fn1 .real .real where
  name := "neg"
  graph x y := y = -x
  exu := by exact exu_eq _
  ev _ X := Ival.neg X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact Ival.mem_neg hx
  asy _ _ A := RAsy.neg A
  asy_sound := fun _ _ _ f g _ hg hA => by
    obtain rfl : g = fun k => -f k := funext fun k => hg k
    exact RAsy.neg_holds hA

@[expose, lynth_cfn] public def invR : Fn1 .real .real where
  name := "inv"
  graph x y := y = x⁻¹
  exu := by exact exu_eq _
  ev c X := Ival.inv c.prec X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact Ival.mem_inv hx
  asy c _ A := RAsy.inv c.prec A
  asy_sound := fun _ _ _ f g _ hg hA => by
    obtain rfl : g = fun k => (f k)⁻¹ := funext fun k => hg k
    exact RAsy.inv_holds hA

@[expose, lynth_cfn] public def npowR : Fn2 .real .nat .real where
  name := "^ℕ"
  graph x n z := z = x ^ n
  exu := by exact exu_eq₂ _
  ev c X N := match NIval.isPoint N with
    | some n => Ival.npow c.prec X n
    | none => Ival.top
  sound := fun c x n z X N _ hz hx hn => by
    obtain rfl := hz
    show _ ∈ (match NIval.isPoint N with
      | some n => Ival.npow c.prec X n
      | none => Ival.top)
    split
    · rename_i m hm
      rw [NIval.eq_of_isPoint hn hm]; exact Ival.mem_npow hx m
    · exact Ival.mem_top _
  asy c N A B := match B with
    | .const n => RAsy.npowC c.prec n A
    | .affine b => RAsy.npowK c.prec N b A
    | _ => RAsy.top
  asy_sound := fun c N A B f g h _ hg hA hB => by
    obtain rfl : h = fun k => f k ^ g k := funext fun k => hg k
    cases B with
    | const n =>
      exact RAsy.holds_congr (RAsy.npowC_holds (p := c.prec) (n := n) hA)
        (fun k hk => by show f k ^ n = f k ^ g k; rw [hB k hk])
    | affine b =>
      exact RAsy.holds_congr (RAsy.npowK_holds (p := c.prec) (b := b) hA)
        (fun k hk => by show f k ^ (k + b) = f k ^ g k; rw [hB k hk])
    | grow => trivial
    | top => trivial

@[expose, lynth_cfn] public def absR : Fn1 .real .real where
  name := "abs"
  graph x y := y = |x|
  exu := by exact exu_eq _
  ev _ X := Ival.abs X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact Ival.mem_abs hx
  asy _ _ A := RAsy.abs A
  asy_sound := fun _ _ _ f g _ hg hA => by
    obtain rfl : g = fun k => |f k| := funext fun k => hg k
    exact RAsy.abs_holds hA

@[expose, lynth_cfn] public def maxR : Fn2 .real .real .real where
  name := "max"
  graph x y z := z = max x y
  exu := by exact exu_eq₂ _
  ev _ X Y := Ival.max X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact Ival.mem_max hx hy

@[expose, lynth_cfn] public def minR : Fn2 .real .real .real where
  name := "min"
  graph x y z := z = min x y
  exu := by exact exu_eq₂ _
  ev _ X Y := Ival.min X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact Ival.mem_min hx hy

@[expose, lynth_cfn] public def sqrtR : Fn1 .real .real where
  name := "sqrt"
  graph x y := y = Real.sqrt x
  exu := by exact exu_eq _
  ev c X := Ival.sqrt c.prec X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact Ival.mem_sqrt hx

/-! ### Natural numbers -/

@[expose, lynth_cfn] public def natCastR : Fn1 .nat .real where
  name := "ℕ→ℝ"
  graph n x := x = (n : ℝ)
  exu := by exact exu_eq _
  ev _ N := NIval.toIval N
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact NIval.mem_toIval hx
  asy _ N A := RAsy.natCast N A
  asy_sound := fun _ _ _ f g _ hg hA => by
    obtain rfl : g = fun k => (f k : ℝ) := funext fun k => hg k
    exact RAsy.natCast_holds hA

@[expose, lynth_cfn] public def addN : Fn2 .nat .nat .nat where
  name := "+ℕ"
  graph x y z := z = x + y
  exu := by exact exu_eq₂ _
  ev _ X Y := NIval.add X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact NIval.mem_add hx hy
  asy _ _ A B := NAsy.add A B
  asy_sound := fun _ _ _ _ f g h _ hg hA hB => by
    obtain rfl : h = fun k => f k + g k := funext fun k => hg k
    exact NAsy.add_holds hA hB

@[expose, lynth_cfn] public def mulN : Fn2 .nat .nat .nat where
  name := "*ℕ"
  graph x y z := z = x * y
  exu := by exact exu_eq₂ _
  ev _ X Y := NIval.mul X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact NIval.mem_mul hx hy

@[expose, lynth_cfn] public def subN : Fn2 .nat .nat .nat where
  name := "-ℕ"
  graph x y z := z = x - y
  exu := by exact exu_eq₂ _
  ev _ X Y := NIval.sub X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact NIval.mem_sub hx hy

@[expose, lynth_cfn] public def factorialN : Fn1 .nat .nat where
  name := "factorial"
  graph n m := m = Nat.factorial n
  exu := by exact exu_eq _
  ev _ N := NIval.mapMono Nat.factorial N
  sound := fun _ _ _ _ _ hy hx => by
    obtain rfl := hy; exact NIval.mem_mapMono Nat.monotone_factorial hx
  asy _ N A := NAsy.factorial N A
  asy_sound := fun _ _ _ f g _ hg hA => by
    obtain rfl : g = fun k => (f k).factorial := funext fun k => hg k
    exact NAsy.factorial_holds hA

@[expose, lynth_cfn] public def fibN : Fn1 .nat .nat where
  name := "fib"
  graph n m := m = Nat.fib n
  exu := by exact exu_eq _
  ev _ N := NIval.mapMono Nat.fib N
  sound := fun _ _ _ _ _ hy hx => by
    obtain rfl := hy; exact NIval.mem_mapMono Nat.fib_mono hx
  asy _ N A := NAsy.fib N A
  asy_sound := fun _ _ _ f g _ hg hA => by
    obtain rfl : g = fun k => Nat.fib (f k) := funext fun k => hg k
    exact NAsy.fib_holds hA

@[expose, lynth_cfn] public def powN : Fn2 .nat .nat .nat where
  name := "^ℕℕ"
  graph b n m := m = b ^ n
  exu := by exact exu_eq₂ _
  ev _ B N := match NIval.isPoint B, NIval.isPoint N with
    | some b, some n => NIval.pt (b ^ n)
    | _, _ => NIval.top
  sound := fun _ b n m B N _ hm hb hn => by
    obtain rfl := hm
    show _ ∈ (match NIval.isPoint B, NIval.isPoint N with
      | some b, some n => NIval.pt (b ^ n)
      | _, _ => NIval.top)
    split
    · rename_i b' n' hb' hn'
      rw [NIval.eq_of_isPoint hb hb', NIval.eq_of_isPoint hn hn']; exact NIval.mem_pt _
    · exact NIval.mem_top _

/-! ### Integers -/

@[expose, lynth_cfn] public def natCastI : Fn1 .nat .int where
  name := "ℕ→ℤ"
  graph n z := z = (n : ℤ)
  exu := by exact exu_eq _
  ev _ N := ZIval.ofNatIval N
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact ZIval.mem_ofNatIval hx

@[expose, lynth_cfn] public def intCastR : Fn1 .int .real where
  name := "ℤ→ℝ"
  graph z x := x = (z : ℝ)
  exu := by exact exu_eq _
  ev _ Z := ZIval.toIval Z
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact ZIval.mem_toIval hx

@[expose, lynth_cfn] public def addI : Fn2 .int .int .int where
  name := "+ℤ"
  graph x y z := z = x + y
  exu := by exact exu_eq₂ _
  ev _ X Y := ZIval.add X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact ZIval.mem_add hx hy

@[expose, lynth_cfn] public def subI : Fn2 .int .int .int where
  name := "-ℤ"
  graph x y z := z = x - y
  exu := by exact exu_eq₂ _
  ev _ X Y := ZIval.sub X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact ZIval.mem_sub hx hy

@[expose, lynth_cfn] public def mulI : Fn2 .int .int .int where
  name := "*ℤ"
  graph x y z := z = x * y
  exu := by exact exu_eq₂ _
  ev _ X Y := ZIval.mul X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact ZIval.mem_mul hx hy

@[expose, lynth_cfn] public def negI : Fn1 .int .int where
  name := "-ℤ"
  graph x y := y = -x
  exu := by exact exu_eq _
  ev _ X := ZIval.neg X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact ZIval.mem_neg hx

/-! ### Complex numbers -/

@[expose, lynth_cfn] public def addC : Fn2 .cplx .cplx .cplx where
  name := "+ℂ"
  graph x y z := z = x + y
  exu := by exact exu_eq₂ _
  ev c X Y := CBox.add c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact CBox.mem_add hx hy

@[expose, lynth_cfn] public def subC : Fn2 .cplx .cplx .cplx where
  name := "-ℂ"
  graph x y z := z = x - y
  exu := by exact exu_eq₂ _
  ev c X Y := CBox.sub c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact CBox.mem_sub hx hy

@[expose, lynth_cfn] public def mulC : Fn2 .cplx .cplx .cplx where
  name := "*ℂ"
  graph x y z := z = x * y
  exu := by exact exu_eq₂ _
  ev c X Y := CBox.mul c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact CBox.mem_mul hx hy

@[expose, lynth_cfn] public def divC : Fn2 .cplx .cplx .cplx where
  name := "/ℂ"
  graph x y z := z = x / y
  exu := by exact exu_eq₂ _
  ev c X Y := CBox.div c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact CBox.mem_div hx hy

@[expose, lynth_cfn] public def negC : Fn1 .cplx .cplx where
  name := "negℂ"
  graph x y := y = -x
  exu := by exact exu_eq _
  ev _ X := CBox.neg X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact CBox.mem_neg hx

@[expose, lynth_cfn] public def invC : Fn1 .cplx .cplx where
  name := "invℂ"
  graph x y := y = x⁻¹
  exu := by exact exu_eq _
  ev c X := CBox.inv c.prec X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact CBox.mem_inv hx

@[expose, lynth_cfn] public def npowC : Fn2 .cplx .nat .cplx where
  name := "^ℕℂ"
  graph x n z := z = x ^ n
  exu := by exact exu_eq₂ _
  ev c X N := match NIval.isPoint N with
    | some n => CBox.npow c.prec X n
    | none => CBox.top
  sound := fun c x n z X N _ hz hx hn => by
    obtain rfl := hz
    show _ ∈ (match NIval.isPoint N with
      | some n => CBox.npow c.prec X n
      | none => CBox.top)
    split
    · rename_i m hm
      rw [NIval.eq_of_isPoint hn hm]; exact CBox.mem_npow hx m
    · exact CBox.mem_top _

@[expose, lynth_cfn] public def ofRealC : Fn1 .real .cplx where
  name := "ℝ→ℂ"
  graph x z := z = (x : ℂ)
  exu := by exact exu_eq _
  ev _ X := CBox.ofReal X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact CBox.mem_ofReal hx

@[expose, lynth_cfn] public def natCastC : Fn1 .nat .cplx where
  name := "ℕ→ℂ"
  graph n z := z = (n : ℂ)
  exu := by exact exu_eq _
  ev _ N := CBox.ofReal (NIval.toIval N)
  sound := fun _ n _ _ _ hy hx => by
    obtain rfl := hy
    have := CBox.mem_ofReal (NIval.mem_toIval hx)
    rw [Complex.ofReal_natCast] at this
    exact this

@[expose, lynth_cfn] public def intCastC : Fn1 .int .cplx where
  name := "ℤ→ℂ"
  graph z w := w = (z : ℂ)
  exu := by exact exu_eq _
  ev _ Z := CBox.ofReal (ZIval.toIval Z)
  sound := fun _ _ _ _ _ hy hx => by
    obtain rfl := hy
    have := CBox.mem_ofReal (ZIval.mem_toIval hx)
    rw [Complex.ofReal_intCast] at this
    exact this

@[expose, lynth_cfn] public def iC : Fn0 .cplx where
  name := "I"
  graph z := z = Complex.I
  exu := by exact exu_eq₀ _
  ev _ := CBox.iI
  sound := fun _ _ _ hy => by obtain rfl := hy; exact CBox.mem_I

@[expose, lynth_cfn] public def reC : Fn1 .cplx .real where
  name := "re"
  graph z x := x = z.re
  exu := by exact exu_eq _
  ev _ X := X.re
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact hx.1

@[expose, lynth_cfn] public def imC : Fn1 .cplx .real where
  name := "im"
  graph z x := x = z.im
  exu := by exact exu_eq _
  ev _ X := X.im
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact hx.2

@[expose, lynth_cfn] public def normC : Fn1 .cplx .real where
  name := "norm"
  graph z x := x = ‖z‖
  exu := by exact exu_eq _
  ev c X := CBox.norm c.prec X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact CBox.mem_norm hx

@[expose, lynth_cfn] public def conjC : Fn1 .cplx .cplx where
  name := "conj"
  graph z w := w = (starRingEnd ℂ) z
  exu := by exact exu_eq _
  ev _ X := CBox.conj X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact CBox.mem_conj hx

end Lynth.Interval.Fns
