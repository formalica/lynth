-- Verified gate library checks: evaluation smoke tests plus axiom
-- pins. Every correctness lemma must be axiom-free (core only) —
-- the gates never touch the solver or its axioms.
import Lynth.Sat.Gates

open Lynth.Sat
open Lynth.Sat.Gates

-- one-hot row over vars 1,2,3 with var 2 true
#eval checkSat (oneHotRowCNF [1, 2, 3]) [some false, some true, some false]

-- AND gate `4 ↔ 1 ∧ 2` with all true
#eval checkSat (andGateCNF 4 [1, 2]) [some true, some true, none, some true]

-- OR gate `4 ↔ 1 ∨ 2` with all false
#eval checkSat (orGateCNF 4 [1, 2]) [some false, some false, none, some false]

-- NOT gate `2 ↔ ¬1` with `1` true
#eval checkSat (notGateCNF 2 1) [some true, some false]

-- disjunction-of-conjunctions `5 ↔ (1∧2) ∨ (3∧4)` first disjunct true
#eval checkSat (orOfAndsCNF 5 [(6, 1, 2), (7, 3, 4)])
  [some true, some true, some false, some false, some true, some true, some false]

/-- info: 'Lynth.Sat.Gates.atLeastOne_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms atLeastOne_correct

/-- info: 'Lynth.Sat.Gates.atMostOne_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms atMostOne_correct

/-- info: 'Lynth.Sat.Gates.oneHotRow_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oneHotRow_correct

/-- info: 'Lynth.Sat.Gates.andGate_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms andGate_correct

/-- info: 'Lynth.Sat.Gates.orGate_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms orGate_correct

/-- info: 'Lynth.Sat.Gates.notGate_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms notGate_correct

/-- info: 'Lynth.Sat.Gates.orOfAnds_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms orOfAnds_correct
