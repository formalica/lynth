import Mathlib
import Lynth

open Lynth.Interval
#eval (Fns.expIval (Ctx.make 64) (Ival.ofRat 64 2))
#eval (Fns.expIval (Ctx.make 64) (Ival.ofRat 64 (-30)))
#eval (Fns.expIval (Ctx.make 200) (Ival.ofRat 200 100))

def exp_two : { x : Rat // abs (Real.exp 2 - x) < 1 / 1000000 } := by lynth
#eval exp_two.1
theorem e1 : Real.exp 1 < 2719 / 1000 ∧ 2718 / 1000 < Real.exp 1 := by lynth
theorem e2 : |Real.exp (Real.exp 1) - 15.154262241479259| < 1 / 10 ^ 12 := by lynth
theorem e3 : Real.exp (-1000) < 1 / 10 ^ 400 := by lynth
#print axioms e2
