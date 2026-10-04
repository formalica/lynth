import Mathlib
import Lynth

open Lynth.Interval

-- Point enclosures (`#eval` only; ground truth: Arb `arb.gamma`).
-- Gamma(1/4) = 3.6256099082219083119...
#eval (Fns.gammaIval (Ctx.make 64) (Ival.ofRat 64 (1 / 4)))
-- Gamma(1/3) = 2.6789385347077476336...
#eval (Fns.gammaIval (Ctx.make 64) (Ival.ofRat 64 (1 / 3)))
-- Gamma(2) = 1, Gamma(1/2) = sqrt(pi)
#eval (Fns.gammaIval (Ctx.make 64) (Ival.ofRat 64 2))
#eval (Fns.gammaIval (Ctx.make 64) (Ival.ofRat 64 (1 / 2)))
-- Reflection: Gamma(-1/2) = -2*sqrt(pi)
#eval (Fns.gammaIval (Ctx.make 64) (Ival.ofRat 64 (-1 / 2)))

set_option maxHeartbeats 26834 in
-- Closed bounds through `lynth`.
theorem gamma_quarter_le : Real.Gamma (1 / 4) ≤ 37 / 10 := by lynth
#print axioms gamma_quarter_le
set_option maxHeartbeats 26927 in
theorem gamma_third_ge : 13 / 5 ≤ Real.Gamma (1 / 3) := by lynth
#print axioms gamma_third_ge

set_option maxHeartbeats 27460 in
def gamma_quarter_approx : { x : Rat // abs (Real.Gamma (1 / 4) - x) < (10 : ℝ) ^ (-5 : ℤ) } := by
  lynth
#print axioms gamma_quarter_approx

-- Axiom footprint: the standard three plus the temporary Stirling axiom
-- (`Lynth/Interval/Fns/Gamma.lean`).
#eval (Fns.gammaIval (Ctx.make 64) (Ival.ofRat 64 (-2)))
