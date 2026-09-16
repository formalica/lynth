-- CDCL checks: unit cases, learned clauses, differential vs DPLL.
import Lynth.Sat.Solver
import Lynth.Sat.Cdcl

open Lynth.Sat

/-- Project a CDCL result to `Bool` (`none` = out of fuel). -/
def proj : Option SatResult × Nat → Option Bool
  | (some (.sat _), _) => some true
  | (some .unsat, _) => some false
  | (none, _) => none

/-- Project a DPLL result to `Bool`. -/
def projD : SatResult → Bool
  | .sat _ => true
  | .unsat => false

-- unit cases agree with DPLL
#eval (proj (Cdcl.cdclSolve [[1]] 1000), projD (solve [[1]] 1000))
-- expect (some true, true)
#eval (proj (Cdcl.cdclSolve [[1], [-1]] 1000), projD (solve [[1], [-1]] 1000))
-- expect (some false, false)
#eval (proj (Cdcl.cdclSolve [[1, 2], [-1, 2]] 1000),
  projD (solve [[1, 2], [-1, 2]] 1000))
-- expect (some true, true)
#eval (proj (Cdcl.cdclSolve [[1], [-1, 2], [-2]] 1000),
  projD (solve [[1], [-1, 2], [-2]] 1000))
-- expect (some false, false)

-- immediate (level-0) conflicts learn nothing: UNSAT is direct
#eval match Cdcl.cdclSolve [[1], [-1]] 1000 with
  | (some .unsat, n) => n == 0
  | _ => false
-- expect true

-- deeper UNSAT learns at least one clause (pigeonhole needs search)
#eval match Cdcl.cdclSolve [[1, 2], [-1, 2], [1, -2], [-1, -2]] 1000 with
  | (some .unsat, n) => decide (0 < n)
  | _ => false
-- expect true

-- SAT models verify against the original CNF
#eval match Cdcl.cdclSolve [[1, 2], [-1, 2], [-1, -2]] 1000 with
  | (some (.sat a), _) => checkSat [[1, 2], [-1, 2], [-1, -2]] a
  | _ => false
-- expect true

-- pigeonhole PHP(2,1): 3 pigeons... small unsat needing search:
-- (x1 ∨ x2) ∧ (¬x1 ∨ ¬x2) ∧ (x1) ∧ (¬x1 ∨ x2) ∧ (¬x2 ∨ x1)... use classic:
-- (a ∨ b) ∧ (¬a ∨ b) ∧ (a ∨ ¬b) ∧ (¬a ∨ ¬b) is UNSAT
#eval (proj (Cdcl.cdclSolve [[1, 2], [-1, 2], [1, -2], [-1, -2]] 1000),
  projD (solve [[1, 2], [-1, 2], [1, -2], [-1, -2]] 1000))
-- expect (some false, false)
