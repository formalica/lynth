-- Spec-compiler fragment matchers: shape routing checks over
-- synthetic predicates (no puzzle content anywhere in this file).
-- Positive: `∀`-guarded inequality over `Fin` (the fragment).
-- Negative: equality conclusions, conjunctions, mismatched bounds,
-- non-`Fin` indices — all must be rejected so future fragments extend
-- without disturbing this one.
import Lynth.Sat.Compile

open Lean Elab Tactic Meta
open Lynth.Sat.Compile

/-- Synthetic guarded inequality over `Fin 3 → Fin 2`. -/
def SynthGuardNe (g : Fin 3 → Fin 3 → Bool) (c : Fin 3 → Fin 2) : Prop :=
  ∀ i j, g i j = true → c i ≠ c j

/-- Sudoku-like: equality conclusion (a LATER fragment, not this one). -/
def SynthEqConcl (b : Fin 4 → Fin 4 → Fin 4) : Prop :=
  ∀ r c₁ c₂, b r c₁ = b r c₂ → c₁ = c₂

/-- Guarded equality: outer shape matches, body conclusion is `=`
rather than `≠` — rejected at the body level. -/
def SynthEqConcl2 (g : Fin 4 → Fin 4 → Bool) (c : Fin 4 → Fin 4) : Prop :=
  ∀ i j, g i j = true → c i = c j

/-- Tour-like: bare conjunction (no `∀`-guard shape at all). -/
def SynthConj (t : Fin 5 → Fin 5) : Prop :=
  Function.Injective t ∧ ∀ _ : Fin 5, True

/-- Mismatched index bounds (elaborates, but the fragment requires
one shared bound). -/
def SynthMismatch (g : Fin 3 → Fin 4 → Bool) (c : Fin 3 → Fin 2) : Prop :=
  ∀ (i : Fin 3) (j : Fin 4), g i j = true → c i ≠ c i

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
