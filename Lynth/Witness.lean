-- Witness synthesis for computational goals: `Subtype` refinements
-- (`{ n // P n }`) and existentials (`∃ x, P x`).
--
-- For `def f : { n : Nat // P n } := by lynth`, lynth must produce a
-- *computable* witness: enumerate candidates per domain type, assign
-- `Subtype.mk w ?proof`, and close the side condition with kernel-checked
-- tactics. The search bound keeps the procedure total; larger witnesses
-- fall through to the next procedure with an explanation.
import Lean
import Lynth.Procedure

namespace Lynth.Witness

open Lean Elab Tactic Meta

/-- Search bound for automatic witness enumeration. -/
def searchBound : Nat := 64

/-- Candidate witnesses for a domain type: `Nat` enumerates `0..bound`;
`Int` interleaves `0, 1, -1, 2, -2, …`; `Bool` tries both values. -/
def candidates (dom : Expr) (bound : Nat) : MetaM (List Expr) := do
  let dom ← whnfR dom
  if dom.isConstOf ``Nat then
    pure ((List.range bound).map fun w => mkNatLit w)
  else if dom.isConstOf ``Int then
    let pos := (List.range bound).map fun w => mkApp (mkConst ``Int.ofNat) (mkNatLit w)
    let neg := (List.range bound).map fun w => mkApp (mkConst ``Int.negSucc) (mkNatLit w)
    -- interleave 0, 1, -1, 2, -2, …
    pure ((pos.zip neg).flatMap fun (p, n) => [p, n] |>.take bound)
  else if dom.isConstOf ``Bool then
    pure [mkConst ``Bool.true, mkConst ``Bool.false]
  else pure []

/-- Value constructor for `Subtype` goals (explicit implicits). -/
def mkSubtypeVal (dom pred w sidePrf : Expr) : MetaM Expr := do
  let u ← getLevel dom
  pure (mkAppN (mkConst ``Subtype.mk [u]) #[dom, pred, w, sidePrf])

/-- Value constructor for `Exists` goals (explicit implicits). -/
def mkExistsVal (dom pred w sidePrf : Expr) : MetaM Expr := do
  let u ← getLevel dom
  pure (mkAppN (mkConst ``Exists.intro [u]) #[dom, pred, w, sidePrf])

/-- Goal shape for witness synthesis: `Subtype` or `Exists` with
domain, predicate, and value constructor. -/
structure WitShape where
  dom : Expr
  pred : Expr
  mkVal : Expr → Expr → MetaM Expr

/-- Classify the goal; `none` ⟹ not a synthesis goal. -/
def classify (goal : Expr) : MetaM (Option WitShape) := do
  let ty ← whnf goal
  match ty.getAppFn with
  | .const ``Subtype _ =>
    let args := ty.getAppArgs
    if args.size != 2 then return none
    let dom := args[0]!
    let pred := args[1]!
    pure (some { dom := dom, pred := pred, mkVal := mkSubtypeVal dom pred })
  | .const ``Exists _ =>
    let args := ty.getAppArgs
    if args.size != 2 then return none
    let dom := args[0]!
    let pred := args[1]!
    pure (some { dom := dom, pred := pred, mkVal := mkExistsVal dom pred })
  | _ => pure none

/-- Try every candidate: build the value, close the side condition with
`decide`/`omega`/`simp_all`/`rfl`. -/
def run (bound : Nat := searchBound) : TacticM ProcedureOutcome := do
  let goal ← getMainTarget
  let some shape ← classify goal | return .failure []
  let cands ← candidates shape.dom bound
  if cands.isEmpty then return .failure []
  let s1 ← `(tactic| decide)
  let s2 ← `(tactic| omega)
  let s3 ← `(tactic| simp_all)
  let s4 ← `(tactic| rfl)
  let sideProbes : List (TSyntax `tactic) := [s1, s2, s3, s4]
  let others ← getUnsolvedGoals
  for w in cands do
    let snapshot ← saveState
    try
      let mvar ← getMainGoal
      let sideTy := mkApp shape.pred w
      let sidePrf ← mkFreshExprSyntheticOpaqueMVar sideTy
      -- explicit implicits from the goal's own `dom`/`pred`: no inference.
      let val ← shape.mkVal w sidePrf
      mvar.assign val
      replaceMainGoal (sidePrf.mvarId! :: others.filter (· != mvar))
      let mut closed := false
      for stx in sideProbes do
        if closed then break
        let snap2 ← saveState
        try
          evalTactic stx
          if (← getUnsolvedGoals).isEmpty then closed := true
          else restoreState snap2
        catch _ =>
          restoreState snap2
      if closed then return .success
      restoreState snapshot
    catch _ =>
      restoreState snapshot
  return .failure []

end Lynth.Witness
