import Lean
import Lynth.Sat.Verified

/-!
Solver certificates: turn `cdclSolveB` outcomes into proof terms.

- `unsatCertGoal`: on solver-UNSAT, closes `∀ a, checkSat cnfE a = false`
  via `cdcl_complete`.
- `satCert`: on solver-SAT with model `m`, the model plus a proof of
  `checkSat (reflect cnf) m = true` via `cdcl_sound`.

In both cases the equation `(cdclSolveB …).result = …` is discharged
by `native_decide` (native evaluation: fast even for large CNFs, where
kernel `decide` would hang). Proofs built here therefore depend on the
temporary solver axiom `cdcl_correct` plus one generated native
evaluation axiom per `native_decide` invocation — and nothing else
(never `sorryAx`).

CNFs enter as syntax (`cnfOfExpr` reads explicit cons/nil spines of
integer literals); proofs are stated over that same syntax, so they
fit goals mentioning the CNF directly.
-/
namespace Lynth.Sat.Cert

open Lean Elab Tactic Meta

/-- Closed `Nat` literal (raw or elaborated `OfNat`). -/
private def natLitOf : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ => some n
  | _ => none

/-- Closed `Int` literal core (raw, elaborated `OfNat`, `Int` constructors). -/
private def intLitCore : Expr → Option Int
  | .lit (.natVal n) => some (n : Int)
  | .app (.app (.app (.const ``OfNat.ofNat _) _) n) _ =>
    match natLitOf n with | some k => some (k : Int) | none => none
  | .app (.const ``Int.ofNat _) n =>
    match natLitOf n with | some k => some (k : Int) | none => none
  | .app (.const ``Int.negSucc _) n =>
    match natLitOf n with | some k => some (-((k : Int) + 1)) | none => none
  | _ => none

/-- Closed `Int` literal (seeing through reducible unfolding and one
negation layer). -/
private def intLitOf (e : Expr) : MetaM (Option Int) := do
  match intLitCore e with
  | some k => pure (some k)
  | none =>
    let er ← whnfR e
    match intLitCore er with
    | some k => pure (some k)
    | none =>
      match er.getAppFn with
      | .const ``Neg.neg _ =>
        match er.getAppArgs.back? with
        | some a =>
          match intLitCore a with
          | some k => pure (some (-k))
          | none => pure none
        | none => pure none
      | _ => pure none

/-- Closed literal spine from syntax (test-scale; `none` on anything
else). Shared by clause and CNF readers. -/
private def spineOf (e : Expr) (readLit : Expr → MetaM (Option Int)) :
    MetaM (Option (List Int)) := do
  let mut lits : List Int := []
  let mut e := e
  for _ in List.range 4096 do
    let er ← whnfR e
    match er.getAppFn with
    | .const ``List.nil _ => return some lits.reverse
    | .const ``List.cons _ =>
      let args := er.getAppArgs
      if args.size < 2 then return none
      else
        match ← readLit args[args.size - 2]! with
        | some l => lits := l :: lits; e := args[args.size - 1]!
        | none => return none
    | _ => return none
  pure none

/-- Closed CNF from syntax: explicit spine of integer-literal rows. -/
private def cnfOfExpr (e : Expr) : MetaM (Option CNF) := do
  let mut rows : List Clause := []
  let mut e := e
  for _ in List.range 4096 do
    let er ← whnfR e
    match er.getAppFn with
    | .const ``List.nil _ => return some rows.reverse
    | .const ``List.cons _ =>
      let args := er.getAppArgs
      if args.size < 2 then return none
      else
        match ← spineOf args[args.size - 2]! intLitOf with
        | some cl => rows := cl :: rows; e := args[args.size - 1]!
        | none => return none
    | _ => return none
  pure none

/-- `native_decide` on `m`, never throwing. Restores the ambient goal
list afterwards (the assigned mvar persists — only the list resets). -/
private def nativeDecideMVar (m : MVarId) : TacticM Bool := do
  let saved ← getUnsolvedGoals
  setGoals [m]
  let ok ← try
    evalTactic (← `(tactic| native_decide))
    pure (← getUnsolvedGoals).isEmpty
  catch _ => pure false
  setGoals saved
  pure ok

/-- Equation `(cdclSolveB …).result = rhs` as a proposition. -/
private def resultEq (cnfE fuelE rbE brE rhs : Expr) : MetaM Expr := do
  let outE := mkAppN (← mkConstWithFreshMVarLevels ``cdclSolveB)
    #[cnfE, fuelE, rbE, brE]
  let resE := Expr.proj ``Cdcl.CdclOut 0 outE
  mkAppM ``Eq #[resE, rhs]

/-- Close goal `g` of shape `∀ a, checkSat cnfE a = false` by solver +
completeness: intro (the `FVarId` is used directly, so freshened names
do not matter), then term-level assign of the `cdcl_complete`
application. Never throws; `false` ⟺ out of scope (non-literal CNF,
no solver UNSAT, or a close failure). -/
def unsatCertGoal (cnfE : Expr) (g : MVarId) (fuel restartBase : Nat := 10000)
    (branch : List Nat := []) : TacticM Bool := do
  let cnf? ← cnfOfExpr cnfE
  let cnf ← match cnf? with
    | some c => pure c
    | none => return false
  match (cdclSolveB cnf fuel restartBase branch).result with
  | some .unsat =>
    let fuelR := toExpr fuel
    let rbR := toExpr restartBase
    let brR := toExpr branch
    let rhs ← mkAppM ``Option.some #[← mkAppM ``SatResult.unsat #[]]
    let eq ← resultEq cnfE fuelR rbR brR rhs
    let m ← mkFreshExprSyntheticOpaqueMVar eq
    if !(← nativeDecideMVar m.mvarId!) then return false
    else
      let (aid, g2) ← g.intro `a
      try
        g2.assign (mkAppN (← mkConstWithFreshMVarLevels ``cdcl_complete)
          #[cnfE, fuelR, rbR, brR, m, .fvar aid])
        pure true
      catch _ => pure false
  | _ => pure false

/-- On solver-SAT with model `m`: the model plus a proof of
`checkSat cnfE (reflect m) = true` (`native_decide` evidence +
`cdcl_sound`). `none` if the CNF is not a closed literal spine or the
solver does not report SAT. -/
def satCert (cnfE : Expr) (fuel restartBase : Nat := 10000)
    (branch : List Nat := []) : TacticM (Option (Assignment × Expr)) := do
  let cnf ← match ← cnfOfExpr cnfE with | some c => pure c | none => return none
  match (cdclSolveB cnf fuel restartBase branch).result with
  | some (.sat m) =>
    let fuelR := toExpr fuel
    let rbR := toExpr restartBase
    let brR := toExpr branch
    let mR := toExpr m
    let satR ← mkAppM ``Option.some #[← mkAppM ``SatResult.sat #[mR]]
    let eq ← resultEq cnfE fuelR rbR brR satR
    let mv ← mkFreshExprSyntheticOpaqueMVar eq
    if !(← nativeDecideMVar mv.mvarId!) then return none
    else
      let prf := mkAppN (← mkConstWithFreshMVarLevels ``cdcl_sound)
        #[cnfE, fuelR, rbR, brR, mR, mv]
      pure (some (m, prf))
  | _ => pure none

end Lynth.Sat.Cert
