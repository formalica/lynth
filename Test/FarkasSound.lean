-- Farkas soundness theorems: proved, native axioms only.
-- `farkas_sound`: finite-form combination soundness.
-- `checkCert_sound`: validated runtime certificates refute denoted systems.
import Lynth

-- The header/copyright linter wants a `Copyright (c) YYYY` banner and a
-- module docstring; this test file has neither.  Its warnings are emitted at
-- the position of the `#print axioms` below, so they would be swept into the
-- `#guard_msgs` assertion and break it.
set_option linter.style.header false

/-- info: 'Lynth.Arith.FarkasSound.farkas_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lynth.Arith.FarkasSound.farkas_sound
/-- info: 'Lynth.Arith.FarkasSound.checkCert_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lynth.Arith.FarkasSound.checkCert_sound
