-- Witness synthesis for computational (`Subtype`/refinement) goals.
--
-- For `def f : { n : Nat // P n } := by lynth`, lynth must produce a
-- *computable* witness: search small `Nat`s by evaluation, then close the
-- side condition with kernel-checked tactics. The search bound keeps the
-- procedure total; larger witnesses fall through to the next procedure
-- with an explanation.
import Lean
import Lynth.Procedure

namespace Lynth.Witness

open Lean Elab Tactic Meta

/-- Search bound for automatic witness enumeration. -/
def searchBound : Nat := 64

/-- Try `⟨w, proof⟩` for `w` in `[0, bound)`, closing the side condition
with `decide`/`omega`/`simp_all`. Returns `.success` on the first hit. -/
def run (bound : Nat := searchBound) : TacticM ProcedureOutcome := do
  let goal ← getMainTarget
  -- Only subtype-like goals (`Subtype _` / `Sigma`-with-proof) qualify.
  let isSubtype ←
    try
      let ty ← whnf goal
      pure (ty.isAppOf `Subtype)
    catch _ => pure false
  if !isSubtype then
    return .failure []
  for w in List.range bound do
    let snapshot ← saveState
    try
      let wLit : TSyntax `term := Lean.Syntax.mkNatLit w
      let ref ← `(tactic| refine ⟨$wLit, ?_⟩)
      evalTactic ref
      let s1 ← `(tactic| decide)
      let s2 ← `(tactic| omega)
      let s3 ← `(tactic| simp_all)
      let s4 ← `(tactic| rfl)
      let sideProbes : List (TSyntax `tactic) := [s1, s2, s3, s4]
      for stx in sideProbes do
        let snap2 ← saveState
        try
          evalTactic stx
          let goals ← getUnsolvedGoals
          if goals.isEmpty then return .success
          restoreState snap2
        catch _ =>
          restoreState snap2
      restoreState snapshot
    catch _ =>
      restoreState snapshot
  return .failure []

end Lynth.Witness
