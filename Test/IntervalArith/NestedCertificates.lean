import Lynth
import Mathlib

/-! Runtime rejection tests for the recursive integration checker. Each test
has an independent measured heartbeat cap, like the integration regressions. -/
namespace IntervalArith.NestedCertificates
open Lynth.Interval (Ctx Dy Ival)
open Intgrl (NExpr)
open Lynth.Interval.Integral (NodeTable)
open Lynth.Interval.Integral.Nested
  (Memo Plan Entry search check key boundR evalWith formula entryEncl replay envCheck)

private def gaussian : NExpr := .integral .interval (.rat 0) (.rat 1)
  (.integral .interval (.rat 0) (.var 0) (.unary .exp (.unary .neg (.pow (.var 1) 2))))
private def tol : Intgrl.Term := .rat (1/1000000)
private def witness : ℚ := 430764/1000000

set_option maxHeartbeats 1300 in -- measured: 1238; +5%
run_cmd do
  let c := Ctx.make 64
  let some cert := search c gaussian (1/1000000) | throwError "fixture search failed"
  unless check c gaussian cert witness tol do throwError "valid certificate rejected"
  if check c gaussian cert 0 tol then throwError "incorrect rational accepted"

set_option maxHeartbeats 1172 in -- measured: 1116; +5%
run_cmd do
  let c := Ctx.make 64
  let some cert := search c gaussian (1/1000000) | throwError "fixture search failed"
  if check c gaussian {cert with entries := cert.entries.reverse} witness tol then
    throwError "forward child dependencies accepted"
  if check c gaussian {cert with entries := #[]} witness tol then
    throwError "missing subintegrals accepted"

set_option maxHeartbeats 1016 in -- measured: 967; +5%
run_cmd do
  let c := Ctx.make 64
  let some cert := search c gaussian (1/1000000) | throwError "fixture search failed"
  let tables := cert.tables.map fun _ => ({roots := [],certWeights := []} : NodeTable)
  if check c gaussian {cert with tables := tables} witness tol then
    throwError "uncertified nodes accepted"
  if check c (.integral .interval (.rat 0) (.rat 1) (.var 40)) cert witness tol then
    throwError "unscoped variable accepted"

set_option maxHeartbeats 413 in -- measured: 393; +5%
run_cmd do
  let c := Ctx.make 64
  let inner : NExpr := .integral .interval (.rat 0) (.rat 1) (.unary .inv (.var 1))
  let e : NExpr := .integral .interval (.rat 0) (.rat 1) inner
  if (search c e (1/1000000)).isSome then
    throwError "divergent inner integral used as default zero"
  let e : NExpr := .integral .interval (.rat 0) (.rat 1) (.binary .mul (.rat 0) inner)
  if (search c e (1/1000000)).isSome then
    throwError "discarded divergent inner integral accepted"

set_option maxHeartbeats 234 in -- measured: 222; +5%
run_cmd do
  let c := Ctx.make 64
  let good : NExpr := .integral .right (.rat 0) (.rat 0) (.rat 0)
  let divergentBound : NExpr := .integral .interval (.rat 0) (.rat 1) (.unary .inv (.var 0))
  let bad : NExpr := .integral .right divergentBound (.rat 0) (.rat 0)
  let memo := ({} : Memo).insert (key good #[]) Ival.zero
  if (evalWith c memo bad #[]).isSome then
    throwError "a cached zero erased divergence in a bound"

-- A nested endpoint has a different variable level inside the body.
set_option maxHeartbeats 699 in -- measured: 665; +5%
run_cmd do
  let a : NExpr := .integral .interval (.rat 0) (.rat (1/100)) (.var 0)
  let badBody : NExpr := .pow (.binary .sub (.var 0) a) 1
  if (formula 0 .interval a (.rat 1) badBody).isSome then
    throwError "a captured endpoint binder matched the power formula"
  let goodBody : NExpr := .pow (.binary .sub (.var 0) (a.shift 0 1)) 1
  unless (formula 0 .interval a (.rat 1) goodBody).isSome do
    throwError "a correctly shifted endpoint failed to match the power formula"
  let e : NExpr := .integral .interval a (.rat 1) badBody
  unless e.scoped 0 do throwError "the binder fixture must be scoped"
  let some I := boundR (e.size+32) (Ctx.coarse 64) e #[] |
    throwError "the binder fixture failed to enclose"
  let exactValue : ℚ := 39599999901/80000000000
  unless (I.lo.map (fun d => decide (d.toRat ≤ exactValue))).getD true &&
      (I.hi.map (fun d => decide (exactValue ≤ d.toRat))).getD true do
    throwError "a nested endpoint produced an incorrect enclosure"

set_option maxHeartbeats 497 in -- measured: 473; +5%
run_cmd do
  let c := Ctx.coarse 64
  let p : Plan := {a := Dy.zero,b := Dy.one,pieces := [⟨Dy.zero,Dy.one,.direct⟩]}
  let entry : Entry := {
    expr := .integral .interval (.rat 0) (.rat 1) (.rat 0)
    env := #[⟨some Dy.one,some Dy.zero⟩]
    method := .panels p}
  unless (entryEncl c {} #[] #[] entry).isSome do
    throwError "the empty-environment fixture must have a valid local enclosure"
  if (replay c {entries := #[entry]}).isSome then
    throwError "a vacuous environment was inserted into the canonical memo"
  unless envCheck #[Ival.top,Ival.pt Dy.zero] do
    throwError "inhabited unbounded and point intervals were rejected"

-- Open half-lines do not cover the split point. Here the inner integral
-- of 1/(x^2+y^2) diverges at x=0 despite the outer factor x^2.
set_option maxHeartbeats 477 in -- measured: 454; +5%
run_cmd do
  let c := Ctx.coarse 64
  let x : NExpr := .var 0
  let inner : NExpr := .integral .interval (.rat 0) (.rat 1)
    (.unary .inv (.binary .add (.pow x 2) (.pow (.var 1) 2)))
  let f : NExpr := .binary .mul
    (.binary .mul (.pow x 2) (.unary .exp (.unary .neg (.pow x 2)))) inner
  let r : NExpr := .integral .right (.rat 0) (.rat 0) f
  let l : NExpr := .integral .left (.rat 0) (.rat 0) f
  let memo := (({} : Memo).insert (key r #[]) Ival.top).insert (key l #[]) Ival.top
  unless (evalWith c memo r #[]).isSome && (evalWith c memo l #[]).isSome do
    throwError "the split-point fixture must have both half-line memo entries"
  let entry : Entry := {
    expr := .integral .whole (.rat 0) (.rat 0) f
    env := #[]
    method := .split}
  if (entryEncl c memo #[] #[] entry).isSome then
    throwError "a divergent inner integral at the split point was accepted"

end IntervalArith.NestedCertificates
