import Lean
import Lynth.Procedure
import Lean.Meta.Tactic.Grind.Main
import Lean.Meta.Tactic.Grind.Action
import Lean.Meta.Tactic.Grind.EMatchAction
import Lean.Meta.Tactic.Grind.Intro

/-!
E-graph inference procedure: saturate the goal context with the core
grind e-graph (congruence closure + ground rewriting + theory
propagation) and share newly derived equalities as kernel-checked
facts for later procedures.

Unlike the `lynth_grind` tactic (which delegates whole-goal solving to
core), this drives core's e-graph as a *library*, following the
`VCGen` precedent: `GrindM.runAtGoal` + `Grind.processHypotheses`.
No splitting or case analysis runs here, so this is a bounded
inference step, not a second solver. All execution goes through core
imports, so the C++ e-graph kernels resolve natively.
-/
namespace Lynth.Egraph.Procedure

open Lean Elab Tactic Meta

/-- Cap on facts exported per invocation (pipeline stays predictable). -/
def maxFacts : Nat := 64

/-- Fuel for the split-free saturation loop (theory propagation +
e-matching rounds, no case splits). -/
def saturateFuel : Nat := 8

/-- Bounded saturation without splitting: loop theory propagation and
e-matching instantiation (reusing core's own action constructors),
returning the latest goal state for harvesting. -/
def saturate (goal : Lean.Meta.Grind.Goal) :
    Lean.Meta.Grind.GrindM Lean.Meta.Grind.Goal := do
  let solvers ← Lean.Meta.Grind.Solvers.mkAction
  let step : Lean.Meta.Grind.Action :=
    solvers <|> Lean.Meta.Grind.Action.instantiate
  match ← Lean.Meta.Grind.Action.run goal (Lean.Meta.Grind.Action.loop saturateFuel step) with
  | .closed _ => pure goal
  | .stuck [] => pure goal
  | .stuck (g :: _) => pure g

/-- Export congruence-class equalities: for every multi-member
equivalence class, prove root-member equalities with core's
`mkEqProof` (toolchain-native) and return `(proof, prop)` pairs.
This surfaces what `processHypotheses` merges silently (e.g. simp
normalization `x + 0 ~ x`, congruence `f a ~ f b`), beyond EUF's
hypothesis-edge closure. -/
def harvestEqcs (goal : Lean.Meta.Grind.Goal) (budget : Nat) :
    Lean.Meta.Grind.GrindM (Array (Expr × Expr)) := do
  let (out, _) ← Lean.Meta.Grind.GoalM.run goal do
    let mut out := #[]
    for ec in goal.getEqcs (sort := true) do
      match ec with
      | [] => pure ()
      | [_] => pure ()
      | root :: members =>
        for m in members do
          if out.size ≥ budget then break
          try
            let prf ← Lean.Meta.Grind.mkEqProof root m
            let ty ← mkEq root m
            out := out.push (prf, ty)
          catch _ => pure ()
    pure out
  pure out

/-- Harvest `(proof, prop)` pairs from core e-graph saturation of the
current goal: internalize hypotheses, propagate, read off newly
derived facts (each carries its kernel proof term), and export
congruence-class equalities. -/
def harvest : TacticM (Array (Expr × Expr)) := do
  let mvar ← getMainGoal
  -- NOTE: `clean := false, revert := false` keeps `initCore` from
  -- mangling the goal (`revertAll` assigns a forwarder mvar, which would
  -- fake an empty goal list); this is pure inference harvesting, so the
  -- goal must come back untouched. Cf. VCGen's `{ clean := false }`.
  let params ← Lean.Meta.Grind.mkDefaultParams { clean := false, revert := false }
  let (newFacts, eqcs) ← Lean.Meta.Grind.GrindM.runAtGoal mvar params fun goal => do
    let goal ← Lean.Meta.Grind.processHypotheses goal
    let goal ← saturate goal
    let eqcs ← harvestEqcs goal maxFacts
    pure (goal.newFacts, eqcs)
  let mut out := #[]
  for nf in newFacts do
    match nf with
    | .eq lhs rhs prf isHEq =>
      -- NOTE: core `NewFact.toExpr` renders `HEq` facts as `Eq`, which
      -- would not typecheck; rebuild the `HEq` proposition instead.
      let ty ← if isHEq then mkAppM ``HEq #[lhs, rhs]
               else Lean.Meta.Grind.NewFact.toExpr nf
      out := out.push (prf, ty)
    | .fact p prf _ => out := out.push (prf, p)
    if out.size >= maxFacts then break
  for (prf, ty) in eqcs do
    if out.size >= maxFacts then break
    out := out.push (prf, ty)
  pure out

/-- Term size (node count) for orienting exported equalities. -/
def termSize : Expr → Nat
  | .app f a => 1 + termSize f + termSize a
  | .lam _ t b _ => 1 + termSize t + termSize b
  | .forallE _ t b _ => 1 + termSize t + termSize b
  | .letE _ t v b _ => 1 + termSize t + termSize v + termSize b
  | .mdata _ b => termSize b
  | .proj _ _ b => 1 + termSize b
  | _ => 1

/-- Orient `(prf, ty)` as a shrinking rewrite (`big = small`) for safe
`simp` consumption downstream. Equal-size atomic pairs (`x = y`) are
kept (they terminate as rules); equal-size compound pairs are skipped
(they would loop, e.g. commutativity shapes). Non-equational props
pass through. -/
def orient (prf ty : Expr) : MetaM (Option (Expr × Expr)) := do
  let (lhs, rhs, isHEq) ← match ty with
    | .app (.app (.app (.const ``Eq _) _) lhs) rhs => pure (lhs, rhs, false)
    | .app (.app (.app (.app (.const ``HEq _) _) lhs) _) rhs => pure (lhs, rhs, true)
    | _ => return some (prf, ty)
  let (sl, sr) := (termSize lhs, termSize rhs)
  if sl > sr then pure (some (prf, ty))
  else if sr > sl then
    let prf' ← if isHEq then mkAppM ``HEq.symm #[prf] else mkAppM ``Eq.symm #[prf]
    let ty' ← if isHEq then mkAppM ``HEq #[rhs, lhs] else mkEq rhs lhs
    pure (some (prf', ty'))
  else if sl == 1 then pure (some (prf, ty))
  else pure none

/-- True if `ty` already appears as a hypothesis type. -/
def alreadyKnown (ty : Expr) : TacticM Bool := do
  for decl in ← getLCtx do
    if decl.type == ty then return true
  pure false

/-- Attempt `exact False.elim h` for a harvested `False` hypothesis;
true if the goal closed. -/
def tryCloseFalse (tag : Name) : TacticM Bool := do
  let closeStx ← `(tactic| exact False.elim $(mkIdent tag))
  try
    evalTactic closeStx
    pure (← getUnsolvedGoals).isEmpty
  catch _ => pure false

/-- Assert one oriented fact (kernel-checked by `note`); true if
asserted. A `False` fact closes the goal via `False.elim`. -/
def tryShareOne (tag : Name) (prf ty : Expr) : TacticM Bool := do
  try
    let mvar ← getMainGoal
    let (_, mvar') ← mvar.note tag prf (some ty)
    replaceMainGoal [mvar']
    if ty.isConstOf ``False then
      pure (← tryCloseFalse tag)
    else pure true
  catch _ => pure false

/-- Assert harvested facts as hypotheses (kernel-checked by `note`).
Returns the number asserted. A harvested `False` closes the goal. -/
def shareFacts (facts : Array (Expr × Expr)) : TacticM Nat := do
  let mut count := 0
  for (prf, ty) in facts do
    if (← getUnsolvedGoals).isEmpty then return count
    unless ty.isConstOf ``True do
      let known ← alreadyKnown ty
      unless known do
        let oriented ← try orient prf ty catch _ => pure none
        match oriented with
        | none => pure ()
        | some (prf, ty) =>
          let known2 ← alreadyKnown ty
          unless known2 do
            let tag := Name.mkStr1 s!"lynth_egraph_{count}"
            if ← tryShareOne tag prf ty then
              count := count + 1
  pure count

/-- Saturate with the e-graph and share derived equalities.
Closes `False`-refuted goals; otherwise yields facts to the pipeline. -/
def run : TacticM ProcedureOutcome := do
  let snapshot ← saveState
  let mvar0 ← getMainGoal
  let facts ← try harvest
    catch _ =>
      restoreState snapshot
      return .failure []
  -- Saturation may have genuinely proved the goal (forwarder mvars from
  -- `transformTarget` also read as assigned, so follow the chain: only a
  -- non-mvar value is a real proof; otherwise roll back for pure inference).
  let proved ← try
    let v ← instantiateMVars (.mvar mvar0)
    pure !v.isMVar
  catch _ => pure false
  if proved then
    logInfo "[lynth:egraph] closed the goal"
    return .success
  -- Pure inference: roll back any goal mangling by the e-graph driver,
  -- then share facts.
  restoreState snapshot
  let count ← shareFacts facts
  if (← getUnsolvedGoals).isEmpty then
    logInfo "[lynth:egraph] closed the goal by refutation"
    return .success
  if count > 0 then
    logInfo m!"[lynth:egraph] shared {count} derived facts"
  return .failure []

end Lynth.Egraph.Procedure
