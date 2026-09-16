-- Pure Fourier–Motzkin checks (no axioms): refutation + certificates.
import Lynth.Arith.Fourier

open Lynth.Arith.Fourier

-- x ≤ 1 ∧ x ≥ 2 is UNSAT; cert lineage covers both originals.
#eval solve [mkLe [1] (-1) 2 0, mkLe [-1] 2 2 1]
-- expect `some [...]`

-- x ≤ 1 ∧ x ≥ 0 is SAT (relaxation): no refutation.
#eval solve [mkLe [1] (-1) 2 0, mkLe [-1] 0 2 1]
-- expect `none`

-- x + y ≤ 1 ∧ x ≥ 0 ∧ y ≥ 0 ∧ x + y ≥ 2 is UNSAT.
#eval solve
  [mkLe [1, 1] (-1) 4 0, mkLe [-1, 0] 0 4 1, mkLe [0, -1] 0 4 2,
   mkLe [-1, -1] 2 4 3]
-- expect `some [...]`

-- certificate length matches the original system size.
#eval match solve [mkLe [1] (-1) 2 0, mkLe [-1] 2 2 1] with
  | some cert => cert.length == 2
  | none => false
-- expect true
