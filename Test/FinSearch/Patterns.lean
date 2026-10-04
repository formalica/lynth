-- Pattern registry checks: shape routing by discrimination tree,
-- per-family validation, and extension without touching existing code
-- (the sum-equation family below is defined wholly in this file).
import Lynth
import Lynth.FinSearch.Patterns

open Lean Elab Tactic Meta
open Lynth.FinSearch.Patterns

set_option maxHeartbeats 355 in
/-- Find a goal-local free variable by name. -/
private def getFVar (n : Name) : TacticM FVarId := do
  let g ← getMainGoal
  g.withContext do
    match (← getLCtx).findFromUserName? n with
    | some d => pure d.fvarId
    | none => throwError "test fvar {n} not found"

set_option maxHeartbeats 382 in
/-- Expect `matchLenEq` to yield `want` on `conj`. -/
private def checkLenEq (tgt : FVarId) (conj : Expr) (want : Option Nat) :
    TacticM Unit := do
  let reg ← seedLenEq
  let got ← matchLenEq reg tgt conj
  unless got == want do
    throwError "matchLenEq mismatch: got {got}, want {want}"

set_option maxHeartbeats 371 in
/-- Expect `matchNodup` to yield `want` on `conj`. -/
private def checkNodup (tgt : FVarId) (conj : Expr) (want : Option Nat) :
    TacticM Unit := do
  let reg ← seedNodup
  let got ← matchNodup reg tgt conj
  unless got == want do
    throwError "matchNodup mismatch: got {got}, want {want}"

set_option maxHeartbeats 898 in
example (l : List Nat) (m : Nat) (x : List Nat) : True := by
  run_tac do
    let g ← getMainGoal
    g.withContext do
      let tgt ← getFVar `l
      let fv := Expr.fvar tgt
      -- both orientations, closed literal
      let c1 ← mkAppM ``Eq #[← mkAppM ``List.length #[fv], mkNatLit 5]
      checkLenEq tgt c1 (some 5)
      let c2 ← mkAppM ``Eq #[mkNatLit 5, ← mkAppM ``List.length #[fv]]
      checkLenEq tgt c2 (some 5)
      -- non-closed other side: no match
      let mv ← getFVar `m
      let c3 ← mkAppM ``Eq #[← mkAppM ``List.length #[fv], .fvar mv]
      checkLenEq tgt c3 none
      -- wrong target: no match
      let xv ← getFVar `x
      let c4 ← mkAppM ``Eq #[← mkAppM ``List.length #[.fvar xv], mkNatLit 5]
      checkLenEq tgt c4 none
      -- unrelated shape: no handler retrieved
      let c5 := mkConst ``True []
      checkLenEq tgt c5 none
  trivial

set_option maxHeartbeats 515 in
example (l : List (Fin 6)) (k : List Nat) (x : List (Fin 6)) : True := by
  run_tac do
    let g ← getMainGoal
    g.withContext do
      let tgt ← getFVar `l
      let fv := Expr.fvar tgt
      let c1 ← mkAppM ``List.Nodup #[fv]
      checkNodup tgt c1 (some 6)
      -- infinite element type: routed but rejected
      let kv ← getFVar `k
      let c2 ← mkAppM ``List.Nodup #[.fvar kv]
      checkNodup tgt c2 none
      -- wrong target: rejected
      let xv ← getFVar `x
      let c3 ← mkAppM ``List.Nodup #[.fvar xv]
      checkNodup tgt c3 none
  trivial

set_option maxHeartbeats 138 in
/-- Extension without modification: sum equations, defined wholly
here (new pattern family + validator, zero changes to `Patterns`). -/
private def seedSumEq : TacticM (Registry Unit) := do
  let p ← wildApp ``Eq 3
  let mut r : Registry Unit := Registry.empty
  r ← r.register p "sum-eq" ()
  pure r

set_option maxHeartbeats 931 in
private def matchSumEq (reg : Registry Unit) (tgt : FVarId) (c : Expr) :
    MetaM (Option Nat) := do
  for _ in ← reg.lookup c do
    let cr ← whnfR c
    match cr.getAppFn with
    | .const ``Eq _ =>
      let args := cr.getAppArgs
      if args.size < 2 then pure ()
      else
        let a := args[args.size - 2]!
        let b := args[args.size - 1]!
        match a.getAppFn with
        | .const ``List.sum _ =>
          match a.getAppArgs.back? with
          | some (.fvar id) =>
            if id != tgt then pure ()
            else
              match Lynth.FinSearch.Recognize.asNumeral (← whnfR b) with
              | some n => return some n
              | none => pure ()
          | _ => pure ()
        | _ => pure ()
    | _ => pure ()
  pure none

set_option maxHeartbeats 851 in
example (l : List Nat) : True := by
  run_tac do
    let g ← getMainGoal
    g.withContext do
      let tgt ← getFVar `l
      let fv := Expr.fvar tgt
      let reg ← seedSumEq
      let c ← mkAppM ``Eq #[← mkAppM ``List.sum #[fv], mkNatLit 10]
      match ← matchSumEq reg tgt c with
      | some 10 => pure ()
      | other => throwError "sum-eq extension mismatch: got {other}"
      -- and the length registry is unaffected by the new family
      let c2 ← mkAppM ``Eq #[← mkAppM ``List.length #[fv], mkNatLit 3]
      checkLenEq tgt c2 (some 3)
  trivial
