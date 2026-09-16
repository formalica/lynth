-- Branch-and-bound checks: integrality refutations, models, depth limits.
import Lynth.Arith.BranchBound

open Lynth.Arith.BranchBound

-- 2x = 3 is ℤ-UNSAT (ℚ-SAT at x = 3/2): needs integrality
#eval bb [([2], -3), ([-2], 3)] [0] 6 1024
-- expect .unsat

-- x ≤ 1 ∧ x ≥ 0 is SAT with an integral model
#eval match bb [([1], -1), ([-1], 0)] [0] 6 1024 with
  | .sat _ => true
  | _ => false
-- expect true

-- depth 0 with a fractional relaxation: inconclusive, never UNSAT
#eval bb [([2], -3), ([-2], 3)] [0] 0 1024
-- expect .unknown

-- x + y = 1 with x,y ≥ 0 over ℤ: SAT (e.g. x=1, y=0)
#eval match bb [([1, 1], -1), ([-1, -1], 1), ([-1, 0], 0), ([0, -1], 0)] [0, 1] 6 1024 with
  | .sat _ => true
  | _ => false
-- expect true
