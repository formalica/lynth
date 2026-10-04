-- Total doubling-loop solver: evaluation tests plus soundness /
-- completeness corollaries with pinned axiom dependencies.
-- Every proof here must bottom out in the two temporary solver axioms
-- (plus core axioms) — never `sorryAx`, never native evaluation.
import Lynth.Sat.Verified

open Lynth.Sat

-- Unit clash decides UNSAT at level 0 (native evaluation).
/-- info: Lynth.Sat.SatResult.unsat -/
#guard_msgs in
#eval solveTotal [[1], [-1]] 100 10 ∅

-- Pigeonhole (3 pigeons, 2 holes) decides UNSAT.
/-- info: Lynth.Sat.SatResult.unsat -/
#guard_msgs in
#eval solveTotal
  [[1, 2], [3, 4], [5, 6], [-1, -3], [-1, -5], [-3, -5],
   [-2, -4], [-2, -6], [-4, -6]] 1000 10 ∅

-- Trivial SAT decides with model (native evaluation).
/-- info: Lynth.Sat.SatResult.sat [some true, some true] -/
#guard_msgs in
#eval solveTotal [[1], [2]] 100 10 ∅

set_option maxHeartbeats 49 in
/-- Soundness corollary applies to any reported model. -/
theorem sound_use (m : Assignment)
    (h : solveTotal [[1], [2]] 100 10 ∅ = .sat m) :
    checkSat [[1], [2]] m = true :=
  solveTotal_sound _ _ _ _ m h
/-- info: 'sound_use' depends on axioms: [propext, Classical.choice, Quot.sound, cdcl_correct, cdcl_fuel_suffices] -/
#guard_msgs in
#print axioms sound_use

set_option maxHeartbeats 57 in
/-- Completeness corollary applies to any UNSAT report. -/
theorem complete_use (a : Assignment)
    (h : solveTotal [[1], [-1]] 100 10 ∅ = .unsat) :
    checkSat [[1], [-1]] a = false :=
  solveTotal_complete _ _ _ _ a h
/-- info: 'complete_use' depends on axioms: [propext, Classical.choice, Quot.sound, cdcl_correct, cdcl_fuel_suffices] -/
#guard_msgs in
#print axioms complete_use


