-- Spec-compiler fragment matchers: shape routing checks over
-- synthetic predicates (no puzzle content anywhere in this file).
-- Positive: `∀`-guarded inequality over `Fin` (the fragment).
-- Negative: equality conclusions, conjunctions, mismatched bounds,
-- non-`Fin` indices — all must be rejected so future fragments extend
-- without disturbing this one.
import Lynth.Sat.Compile

open Lean Elab Tactic Meta
open Lynth.Sat.Compile

set_option maxHeartbeats 21 in
/-- Synthetic guarded inequality over `Fin 3 → Fin 2`. -/
def SynthGuardNe (g : Fin 3 → Fin 3 → Bool) (c : Fin 3 → Fin 2) : Prop :=
  ∀ i j, g i j = true → c i ≠ c j

set_option maxHeartbeats 17 in
/-- Sudoku-like: equality conclusion (a LATER fragment, not this one). -/
def SynthEqConcl (b : Fin 4 → Fin 4 → Fin 4) : Prop :=
  ∀ r c₁ c₂, b r c₁ = b r c₂ → c₁ = c₂

set_option maxHeartbeats 20 in
/-- Guarded equality: outer shape matches, body conclusion is `=`
rather than `≠` — rejected at the body level. -/
def SynthEqConcl2 (g : Fin 4 → Fin 4 → Bool) (c : Fin 4 → Fin 4) : Prop :=
  ∀ i j, g i j = true → c i = c j

set_option maxHeartbeats 15 in
/-- Tour-like: bare conjunction (no `∀`-guard shape at all). -/
def SynthConj (t : Fin 5 → Fin 5) : Prop :=
  Function.Injective t ∧ ∀ _ : Fin 5, True

set_option maxHeartbeats 25 in
/-- Mismatched index bounds (elaborates, but the fragment requires
one shared bound). -/
def SynthMismatch (g : Fin 3 → Fin 4 → Bool) (c : Fin 3 → Fin 2) : Prop :=
  ∀ (i : Fin 3) (j : Fin 4), g i j = true → c i ≠ c i

set_option maxHeartbeats 685 in
private def checkForall (n : Name) (want : Option Nat) : TacticM Unit := do
  let P := mkConst n []
  match ← matchForall2Fin P with
  | some (k, _, _, _, _, _) =>
    match want with
    | some w =>
      unless k == w do throwError "{n}: bound {k}, want {w}"
    | none => throwError "{n}: unexpectedly matched"
  | none =>
    match want with
    | some _ => throwError "{n}: unexpectedly rejected"
    | none => pure ()

set_option maxHeartbeats 895 in
private def checkBodyKind (n : Name) (want : Option Bool) : TacticM Unit := do
  let P := mkConst n []
  match ← matchForall2Fin P with
  | none =>
    match want with
    | some _ => throwError "{n}: outer rejected"
    | none => pure ()
  | some (_, _, _, _, _, body) =>
    match ← matchGuardNeBody body with
    | some (_, _, _, isNe) =>
      match want with
      | some w =>
        unless isNe == w do throwError "{n}: kind mismatch"
      | none => throwError "{n}: body unexpectedly matched"
    | none =>
      match want with
      | some _ => throwError "{n}: body unexpectedly rejected"
      | none => pure ()

set_option maxHeartbeats 244 in
example : True := by
  run_tac do
    checkForall ``SynthGuardNe (some 3)
    checkForall ``SynthEqConcl none
    checkForall ``SynthEqConcl2 (some 4)
    checkForall ``SynthConj none
    checkForall ``SynthMismatch none
    checkBodyKind ``SynthGuardNe (some true)
    checkBodyKind ``SynthEqConcl2 (some false)
  trivial

set_option maxHeartbeats 12 in
/-- Synthetic 9x9 board parts (shape-only, no puzzle). -/
def SynthPart := Fin 9 → Fin 9 → Option (Fin 9)
set_option maxHeartbeats 11 in
def SynthBoard := Fin 9 → Fin 9 → Fin 9
set_option maxHeartbeats 77 in
def SynthBox (r c : Fin 9) : Fin 9 := (r / 3) * 3 + (c / 3)

set_option maxHeartbeats 15 in
/-- Row injectivity shape. -/
def SynthRows (_p : SynthPart) (b : SynthBoard) : Prop :=
  ∀ r c₁ c₂, b r c₁ = b r c₂ → c₁ = c₂

set_option maxHeartbeats 15 in
/-- Column injectivity shape. -/
def SynthCols (_p : SynthPart) (b : SynthBoard) : Prop :=
  ∀ c r₁ r₂, b r₁ c = b r₂ c → r₁ = r₂

set_option maxHeartbeats 23 in
/-- Box shape with user guard + value guard + paired conclusion. -/
def SynthBoxes (_p : SynthPart) (b : SynthBoard) : Prop :=
  ∀ r₁ c₁ r₂ c₂, SynthBox r₁ c₁ = SynthBox r₂ c₂ →
    b r₁ c₁ = b r₂ c₂ → r₁ = r₂ ∧ c₁ = c₂

set_option maxHeartbeats 18 in
/-- Givens shape. -/
def SynthGivens (p : SynthPart) (b : SynthBoard) : Prop :=
  ∀ r c v, p r c = some v → b r c = v

set_option maxHeartbeats 921 in
private def checkNested (n : Name) (wantKinds : List String) : TacticM Unit := do
  let P := mkConst n []
  match ← matchFrag P with
  | none =>
    unless wantKinds.isEmpty do throwError "{n}: unexpectedly rejected"
  | some frags =>
    if frags.length != wantKinds.length then
      throwError "{n}: {frags.length} frags, want {wantKinds.length}"
    else
      for (fr, w) in frags.zip wantKinds do
        let got := match fr.kind with
          | .row => "row"
          | .col => "col"
          | .box => "box"
          | .given => "given"
          | .ne => "ne"
          | .eq => "eq"
          | .inj => "inj"
          | .req => "req"
        unless got == w do throwError "{n}: kind {got}, want {w}"

set_option maxHeartbeats 213 in
example : True := by
  run_tac do
    checkNested ``SynthRows ["row"]
    checkNested ``SynthCols ["col"]
    checkNested ``SynthBoxes ["box"]
    checkNested ``SynthGivens ["given"]
  trivial

/-- info: 'Lynth.Sat.Compile.lin2D_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lin2D_inj

/-- info: 'Lynth.Sat.Compile.unlin_lin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unlin_lin

/-- info: 'Lynth.Sat.Compile.neFam_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms neFam_complete

/-- info: 'Lynth.Sat.Compile.eqFam_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eqFam_sound

/-- info: 'Lynth.Sat.Compile.eqFam_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eqFam_complete

/-- info: 'Lynth.Sat.Compile.injFam_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms injFam_sound

/-- info: 'Lynth.Sat.Compile.injFam_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms injFam_complete

/-- info: 'Lynth.Sat.Compile.reqFam_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reqFam_sound

/-- info: 'Lynth.Sat.Compile.reqFam_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reqFam_complete

/-- info: 'Lynth.Sat.Compile.runSolver_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lynth.Sat.cdcl_correct,
 Lynth.Sat.cdcl_fuel_suffices] -/
#guard_msgs in
#print axioms runSolver_sound

/-- info: 'Lynth.Sat.Compile.runSolver_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lynth.Sat.cdcl_correct,
 Lynth.Sat.cdcl_fuel_suffices] -/
#guard_msgs in
#print axioms runSolver_complete

/-- info: 'Lynth.Sat.Compile.runSolver_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lynth.Sat.cdcl_correct,
 Lynth.Sat.cdcl_fuel_suffices] -/
#guard_msgs in
#print axioms runSolver_none

/-- info: 'Lynth.Sat.Compile.neFam_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms neFam_sound

/-- info: 'Lynth.Sat.Compile.injList_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms injList_sound

/-- info: 'Lynth.Sat.Compile.injList_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms injList_complete

/-- info: 'Lynth.Sat.Compile.rowGuard81' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rowGuard81

/-- info: 'Lynth.Sat.Compile.colGuard81' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms colGuard81

/-- info: 'Lynth.Sat.Compile.rowAdequate_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rowAdequate_sound

/-- info: 'Lynth.Sat.Compile.rowAdequate_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rowAdequate_complete

/-- info: 'Lynth.Sat.Compile.colAdequate_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms colAdequate_sound

/-- info: 'Lynth.Sat.Compile.colAdequate_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms colAdequate_complete

/-- info: 'Lynth.Sat.Compile.boxGuardLin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms boxGuardLin

/-- info: 'Lynth.Sat.Compile.boxAdequate_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms boxAdequate_sound

/-- info: 'Lynth.Sat.Compile.boxAdequate_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms boxAdequate_complete

/-- info: 'Lynth.Sat.Compile.givenGuardLin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms givenGuardLin

/-- info: 'Lynth.Sat.Compile.givenAdequate_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms givenAdequate_sound

/-- info: 'Lynth.Sat.Compile.givenAdequate_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms givenAdequate_complete

/-- info: 'Lynth.Sat.Compile.givenFamCNF' does not depend on any axioms -/
#guard_msgs in
#print axioms givenFamCNF

/-- info: 'Lynth.Sat.Compile.givenFam_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms givenFam_sound

/-- info: 'Lynth.Sat.Compile.givenFam_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms givenFam_complete

/-- info: 'Lynth.Sat.Compile.rowNested_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rowNested_sound

/-- info: 'Lynth.Sat.Compile.rowNested_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rowNested_complete

/-- info: 'Lynth.Sat.Compile.colNested_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms colNested_sound

/-- info: 'Lynth.Sat.Compile.colNested_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms colNested_complete

/-- info: 'Lynth.Sat.Compile.boxNested_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms boxNested_sound

/-- info: 'Lynth.Sat.Compile.boxNested_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms boxNested_complete

/-- info: 'Lynth.Sat.Compile.givenNested_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms givenNested_sound

/-- info: 'Lynth.Sat.Compile.givenNested_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms givenNested_complete
