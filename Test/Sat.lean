-- Pure SAT-solver checks (no axioms involved).
import Lynth.Sat.Solver

open Lynth.Sat

-- trivially SAT: single positive literal
#eval solve [[1]] 100            -- expect .sat
-- trivially UNSAT: p and ¬p
#eval solve [[1], [-1]] 100      -- expect .unsat
-- small SAT: (p ∨ q) ∧ (¬p ∨ q)  → q must be true
#eval solve [[1, 2], [-1, 2]] 100
-- pigeonhole-ish UNSAT: (p) ∧ (¬p ∨ q) ∧ (¬q)
#eval solve [[1], [-1, 2], [-2]] 100  -- expect .unsat

-- certificate checker agrees on a SAT instance
#eval match solve [[1, 2], [-1, 2]] 100 with
  | .sat a => checkSat [[1, 2], [-1, 2]] a
  | .unsat => false
-- expect true
