module
import Mathlib
public import Lynth

open Lynth.Interval

-- Point enclosure (`#eval` only; ground truth: γ = 0.57721566490153286060...).
#eval (Fns.eulerBMIval (Ctx.make 128))

set_option maxHeartbeats 6000 in
-- 20 correct digits through `lynth` (Brent–McMillan B3 evaluator).
public def euler_twenty_digits : { x : ℚ // abs (Real.eulerMascheroniConstant - x) < 1 / 10 ^ 20 } := by
  lynth
/-- info: 'euler_twenty_digits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms euler_twenty_digits
