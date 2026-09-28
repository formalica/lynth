-- Generic finite-value + difference bridges: smoke tests plus axiom
-- pins. All correctness lemmas must be core-only (no solver axioms,
-- no puzzle content) — they are instantiated for every finite puzzle.
import Lynth.Sat.Differ

open Lynth.Sat
open Lynth.Sat.Gates
open Lynth.Sat.FinVal
open Lynth.Sat.Differ

-- two cells, two values: canonical all-zero model satisfies one-hots
#eval checkSat (cellsCNF 2 2) (modelOf 2 2 (fun _ => ⟨0, by omega⟩))

-- difference clause at value 0 over cells 0,1 under separating model
#eval checkSat [diffClause 2 0 1 0]
  (modelOf 2 2 (fun v => if v.val = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩))

/-- info: 'Lynth.Sat.FinVal.decodeVal_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decodeVal_true

/-- info: 'Lynth.Sat.FinVal.decodeVal_of_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decodeVal_of_row

/-- info: 'Lynth.Sat.FinVal.modelOf_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms modelOf_eval

/-- info: 'Lynth.Sat.Differ.diffClause_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diffClause_sound

/-- info: 'Lynth.Sat.Differ.diff_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diff_sound

/-- info: 'Lynth.Sat.Differ.diffClause_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diffClause_complete

/-- info: 'Lynth.Sat.Gates.checkSat_pair_of_true_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkSat_pair_of_true_left

/-- info: 'Lynth.Sat.Gates.checkSat_pair_of_true_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkSat_pair_of_true_right

/-- info: 'Lynth.Sat.FinVal.rowLit_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rowLit_unique

/-- info: 'Lynth.Sat.Differ.diff_sound_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diff_sound_decode

/-- info: 'Lynth.Sat.Differ.diffCNF_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diffCNF_complete

/-- info: 'Lynth.Sat.Differ.eq_sound_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_sound_decode

/-- info: 'Lynth.Sat.Differ.eqClause_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eqClause_complete

/-- info: 'Lynth.Sat.Differ.eqCNF_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eqCNF_complete

/-- info: 'Lynth.Sat.Gates.checkSat_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkSat_flatMap

/-- info: 'Lynth.Sat.Gates.checkSat_of_all_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkSat_of_all_single
