module

public import Init.Prelude
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Lynth.Interval.Core.Expr
public import Lynth.Interval.Core.Ctx
public import Lynth.Interval.Core.Fn
public import Lynth.Interval.Core.Ty
public import Lynth.Interval.Num.Dy
public import Lynth.Interval.Num.Ival
import all Lynth.Interval.Fns.Arith
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Constant: the golden ratio `φ`

`Real.goldenRatio = (1 + √5) / 2` (Mathlib, `NumberTheory.Real.GoldenRatio`).
It is an `abbrev` in a Mathlib module, so the reifier never unfolds it
(`isLibraryDecl`) — the `goldenRatioR` entry below is load-bearing, not a
demo.  Enclosure is the plain `(1 + √5) / 2` composition.
-/

namespace Lynth.Interval.Fns

open Lynth.Interval Dy

/-- enclosure of `(1 + √5) / 2`. -/
@[expose] public def goldenRatioIval (c : Ctx) : Ival :=
  Ival.div c.prec
    (Ival.add c.prec Ival.one (Ival.sqrt c.prec (Ival.pt (Dy.ofNat 5))))
    (Ival.pt (Dy.ofNat 2))

theorem mem_goldenRatioIval {c : Ctx} : Real.goldenRatio ∈ goldenRatioIval c := by
  show ((1 + Real.sqrt 5) / 2 : ℝ) ∈ goldenRatioIval c
  unfold goldenRatioIval
  have h5 : (5 : ℝ) ∈ Ival.pt (Dy.ofNat 5) := by
    have h := Ival.mem_pt (Dy.ofNat 5)
    simpa [Dy.toReal_def, Dy.toRat_ofNat] using h
  have h2 : (2 : ℝ) ∈ Ival.pt (Dy.ofNat 2) := by
    have h := Ival.mem_pt (Dy.ofNat 2)
    simpa [Dy.toReal_def, Dy.toRat_ofNat] using h
  exact Ival.mem_div
    (Ival.mem_add Ival.mem_one (Ival.mem_sqrt h5)) h2

@[expose, lynth_cfn] public def goldenRatioR : Fn0 .real where
  name := "goldenRatio"
  graph y := y = Real.goldenRatio
  exu := by exact exu_eq₀ _
  ev := goldenRatioIval
  sound := fun _ _ _ hy => by obtain rfl := hy; exact mem_goldenRatioIval
  cost := 120

end Lynth.Interval.Fns
