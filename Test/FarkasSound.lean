-- Farkas soundness theorems: proved, native axioms only.
-- `farkas_sound`: finite-form combination soundness.
-- `checkCert_sound`: validated runtime certificates refute denoted systems.
import Lynth

/-- info: 'Lynth.Arith.FarkasSound.farkas_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lynth.Arith.FarkasSound.farkas_sound
/-- info: 'Lynth.Arith.FarkasSound.checkCert_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lynth.Arith.FarkasSound.checkCert_sound
