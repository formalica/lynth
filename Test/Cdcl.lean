-- CDCL checks: unit cases, learned clauses, differential vs DPLL.
import Lynth.Sat.Solver
import Lynth.Sat.Cdcl

open Lynth.Sat

/-- Project a CDCL result to `Bool` (`none` = out of fuel). -/
def proj (o : Cdcl.CdclOut) : Option Bool :=
  match o.result with
  | some (.sat _) => some true
  | some .unsat => some false
  | none => none

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
#eval let o := Cdcl.cdclSolve [[1], [-1]] 1000
match o.result, o.learnt == 0 with
  | some .unsat, true => true
  | _, _ => false
-- expect true

-- deeper UNSAT learns at least one clause (pigeonhole needs search)
#eval let o := Cdcl.cdclSolve [[1, 2], [-1, 2], [1, -2], [-1, -2]] 1000
match o.result, decide (0 < o.learnt) with
  | some .unsat, true => true
  | _, _ => false
-- expect true

-- SAT models verify against the original CNF
#eval match (Cdcl.cdclSolve [[1, 2], [-1, 2], [-1, -2]] 1000).result with
  | some (.sat a) => checkSat [[1, 2], [-1, 2], [-1, -2]] a
  | _ => false
-- expect true

-- pigeonhole PHP(2,1): 3 pigeons... small unsat needing search:
-- (x1 ∨ x2) ∧ (¬x1 ∨ ¬x2) ∧ (x1) ∧ (¬x1 ∨ x2) ∧ (¬x2 ∨ x1)... use classic:
-- (a ∨ b) ∧ (¬a ∨ b) ∧ (a ∨ ¬b) ∧ (¬a ∨ ¬b) is UNSAT
#eval (proj (Cdcl.cdclSolve [[1, 2], [-1, 2], [1, -2], [-1, -2]] 1000),
  projD (solve [[1, 2], [-1, 2], [1, -2], [-1, -2]] 1000))
-- expect (some false, false)

-- restarts fire with an aggressive base yet the verdict stays UNSAT
-- (3-var cube needs several conflicts, forcing restart periods)
#eval let o := Cdcl.cdclSolve ([[1, 2, 3], [1, 2, -3], [1, -2, 3], [1, -2, -3],
     [-1, 2, 3], [-1, 2, -3], [-1, -2, 3], [-1, -2, -3]] : CNF) 1000 1
match o.result, decide (0 < o.restarts) with
  | some .unsat, true => true
  | _, _ => false
-- expect true
