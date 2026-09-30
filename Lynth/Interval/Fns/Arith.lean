import Lynth.Interval.Reify.Registry
import Mathlib.Data.Nat.Fib.Basic

/-!
# Arithmetic registry entries (ℕ, ℝ, ℂ)

Field operations, natural powers, absolute value, min/max, square root,
casts, and the complex structure maps.  See `docs/interval/04-functions.md §1`.
-/

namespace Lynth.Interval.Fns

open Lynth.Interval

/-! ### Real field operations -/

@[lynth_fn] def addR : Fn2 .real .real .real where
  name := "+"
  graph x y z := z = x + y
  exu := exu_eq₂ _
  ev c X Y := Ival.add c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact Ival.mem_add hx hy

@[lynth_fn] def subR : Fn2 .real .real .real where
  name := "-"
  graph x y z := z = x - y
  exu := exu_eq₂ _
  ev c X Y := Ival.sub c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact Ival.mem_sub hx hy

@[lynth_fn] def mulR : Fn2 .real .real .real where
  name := "*"
  graph x y z := z = x * y
  exu := exu_eq₂ _
  ev c X Y := Ival.mul c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact Ival.mem_mul hx hy

@[lynth_fn] def divR : Fn2 .real .real .real where
  name := "/"
  graph x y z := z = x / y
  exu := exu_eq₂ _
  ev c X Y := Ival.div c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact Ival.mem_div hx hy

@[lynth_fn] def negR : Fn1 .real .real where
  name := "neg"
  graph x y := y = -x
  exu := exu_eq _
  ev _ X := Ival.neg X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact Ival.mem_neg hx

@[lynth_fn] def invR : Fn1 .real .real where
  name := "inv"
  graph x y := y = x⁻¹
  exu := exu_eq _
  ev c X := Ival.inv c.prec X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact Ival.mem_inv hx

@[lynth_fn] def npowR : Fn2 .real .nat .real where
  name := "^ℕ"
  graph x n z := z = x ^ n
  exu := exu_eq₂ _
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

@[lynth_fn] def absR : Fn1 .real .real where
  name := "abs"
  graph x y := y = |x|
  exu := exu_eq _
  ev _ X := Ival.abs X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact Ival.mem_abs hx

@[lynth_fn] def maxR : Fn2 .real .real .real where
  name := "max"
  graph x y z := z = max x y
  exu := exu_eq₂ _
  ev _ X Y := Ival.max X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact Ival.mem_max hx hy

@[lynth_fn] def minR : Fn2 .real .real .real where
  name := "min"
  graph x y z := z = min x y
  exu := exu_eq₂ _
  ev _ X Y := Ival.min X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact Ival.mem_min hx hy

@[lynth_fn] def sqrtR : Fn1 .real .real where
  name := "sqrt"
  graph x y := y = Real.sqrt x
  exu := exu_eq _
  ev c X := Ival.sqrt c.prec X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact Ival.mem_sqrt hx

/-! ### Natural numbers -/

@[lynth_fn] def natCastR : Fn1 .nat .real where
  name := "ℕ→ℝ"
  graph n x := x = (n : ℝ)
  exu := exu_eq _
  ev _ N := NIval.toIval N
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact NIval.mem_toIval hx

@[lynth_fn] def addN : Fn2 .nat .nat .nat where
  name := "+ℕ"
  graph x y z := z = x + y
  exu := exu_eq₂ _
  ev _ X Y := NIval.add X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact NIval.mem_add hx hy

@[lynth_fn] def mulN : Fn2 .nat .nat .nat where
  name := "*ℕ"
  graph x y z := z = x * y
  exu := exu_eq₂ _
  ev _ X Y := NIval.mul X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact NIval.mem_mul hx hy

@[lynth_fn] def subN : Fn2 .nat .nat .nat where
  name := "-ℕ"
  graph x y z := z = x - y
  exu := exu_eq₂ _
  ev _ X Y := NIval.sub X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact NIval.mem_sub hx hy

@[lynth_fn] def factorialN : Fn1 .nat .nat where
  name := "factorial"
  graph n m := m = Nat.factorial n
  exu := exu_eq _
  ev _ N := NIval.mapMono Nat.factorial N
  sound := fun _ _ _ _ _ hy hx => by
    obtain rfl := hy; exact NIval.mem_mapMono Nat.monotone_factorial hx

@[lynth_fn] def fibN : Fn1 .nat .nat where
  name := "fib"
  graph n m := m = Nat.fib n
  exu := exu_eq _
  ev _ N := NIval.mapMono Nat.fib N
  sound := fun _ _ _ _ _ hy hx => by
    obtain rfl := hy; exact NIval.mem_mapMono Nat.fib_mono hx

@[lynth_fn] def powN : Fn2 .nat .nat .nat where
  name := "^ℕℕ"
  graph b n m := m = b ^ n
  exu := exu_eq₂ _
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

/-! ### Complex numbers -/

@[lynth_fn] def addC : Fn2 .cplx .cplx .cplx where
  name := "+ℂ"
  graph x y z := z = x + y
  exu := exu_eq₂ _
  ev c X Y := CBox.add c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact CBox.mem_add hx hy

@[lynth_fn] def subC : Fn2 .cplx .cplx .cplx where
  name := "-ℂ"
  graph x y z := z = x - y
  exu := exu_eq₂ _
  ev c X Y := CBox.sub c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact CBox.mem_sub hx hy

@[lynth_fn] def mulC : Fn2 .cplx .cplx .cplx where
  name := "*ℂ"
  graph x y z := z = x * y
  exu := exu_eq₂ _
  ev c X Y := CBox.mul c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact CBox.mem_mul hx hy

@[lynth_fn] def divC : Fn2 .cplx .cplx .cplx where
  name := "/ℂ"
  graph x y z := z = x / y
  exu := exu_eq₂ _
  ev c X Y := CBox.div c.prec X Y
  sound := fun _ _ _ _ _ _ _ hz hx hy => by obtain rfl := hz; exact CBox.mem_div hx hy

@[lynth_fn] def negC : Fn1 .cplx .cplx where
  name := "negℂ"
  graph x y := y = -x
  exu := exu_eq _
  ev _ X := CBox.neg X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact CBox.mem_neg hx

@[lynth_fn] def invC : Fn1 .cplx .cplx where
  name := "invℂ"
  graph x y := y = x⁻¹
  exu := exu_eq _
  ev c X := CBox.inv c.prec X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact CBox.mem_inv hx

@[lynth_fn] def npowC : Fn2 .cplx .nat .cplx where
  name := "^ℕℂ"
  graph x n z := z = x ^ n
  exu := exu_eq₂ _
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

@[lynth_fn] def ofRealC : Fn1 .real .cplx where
  name := "ℝ→ℂ"
  graph x z := z = (x : ℂ)
  exu := exu_eq _
  ev _ X := CBox.ofReal X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact CBox.mem_ofReal hx

@[lynth_fn] def natCastC : Fn1 .nat .cplx where
  name := "ℕ→ℂ"
  graph n z := z = (n : ℂ)
  exu := exu_eq _
  ev _ N := CBox.ofReal (NIval.toIval N)
  sound := fun _ n _ _ _ hy hx => by
    obtain rfl := hy
    have := CBox.mem_ofReal (NIval.mem_toIval hx)
    rw [Complex.ofReal_natCast] at this
    exact this

@[lynth_fn] def iC : Fn0 .cplx where
  name := "I"
  graph z := z = Complex.I
  exu := exu_eq₀ _
  ev _ := CBox.iI
  sound := fun _ _ _ hy => by obtain rfl := hy; exact CBox.mem_I

@[lynth_fn] def reC : Fn1 .cplx .real where
  name := "re"
  graph z x := x = z.re
  exu := exu_eq _
  ev _ X := X.re
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact hx.1

@[lynth_fn] def imC : Fn1 .cplx .real where
  name := "im"
  graph z x := x = z.im
  exu := exu_eq _
  ev _ X := X.im
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact hx.2

@[lynth_fn] def normC : Fn1 .cplx .real where
  name := "norm"
  graph z x := x = ‖z‖
  exu := exu_eq _
  ev c X := CBox.norm c.prec X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact CBox.mem_norm hx

@[lynth_fn] def conjC : Fn1 .cplx .cplx where
  name := "conj"
  graph z w := w = (starRingEnd ℂ) z
  exu := exu_eq _
  ev _ X := CBox.conj X
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact CBox.mem_conj hx

end Lynth.Interval.Fns
