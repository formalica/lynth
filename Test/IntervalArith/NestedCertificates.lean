import Mathlib
import Lynth.Interval.Integral.NestedSearch

/-! Runtime rejection tests for the recursive integration checker. Each test
has an independent measured heartbeat cap, like the integration regressions. -/
namespace IntervalArith.NestedCertificates
open Lean Elab Command
open Lynth.Interval Lynth.Interval.Integral Lynth.Interval.Integral.Nested Intgrl

private def gaussian : NExpr := .integral .interval (.rat 0) (.rat 1)
  (.integral .interval (.rat 0) (.var 0) (.unary .exp (.unary .neg (.pow (.var 1) 2))))
private def tol : Intgrl.Term := .rat (1/1000000)
private def witness : ℚ := 430764/1000000

set_option maxHeartbeats 1299 in -- measured: 1237; +5%
run_cmd do
  let c := Ctx.make 64
  let some cert := search c gaussian (1/1000000) | throwError "fixture search failed"
  unless check c gaussian cert witness tol do throwError "valid certificate rejected"
  if check c gaussian cert 0 tol then throwError "incorrect rational accepted"

set_option maxHeartbeats 1179 in -- measured: 1122; +5%
run_cmd do
  let c := Ctx.make 64
  let some cert := search c gaussian (1/1000000) | throwError "fixture search failed"
  if check c gaussian {cert with entries := cert.entries.reverse} witness tol then
    throwError "forward child dependencies accepted"
  if check c gaussian {cert with entries := #[]} witness tol then
    throwError "missing subintegrals accepted"

set_option maxHeartbeats 1028 in -- measured: 979; +5%
run_cmd do
  let c := Ctx.make 64
  let some cert := search c gaussian (1/1000000) | throwError "fixture search failed"
  let tables := cert.tables.map fun _ => ({roots := [],certWeights := []} : NodeTable)
  if check c gaussian {cert with tables := tables} witness tol then
    throwError "uncertified nodes accepted"
  if check c (.integral .interval (.rat 0) (.rat 1) (.var 40)) cert witness tol then
    throwError "unscoped variable accepted"

set_option maxHeartbeats 418 in -- measured: 398; +5%
run_cmd do
  let c := Ctx.make 64
  let inner : NExpr := .integral .interval (.rat 0) (.rat 1) (.unary .inv (.var 1))
  let e : NExpr := .integral .interval (.rat 0) (.rat 1) inner
  if (search c e (1/1000000)).isSome then
    throwError "divergent inner integral used as default zero"
  let e : NExpr := .integral .interval (.rat 0) (.rat 1) (.binary .mul (.rat 0) inner)
  if (search c e (1/1000000)).isSome then
    throwError "discarded divergent inner integral accepted"

set_option maxHeartbeats 241 in -- measured: 229; +5%
run_cmd do
  let c := Ctx.make 64
  let good : NExpr := .integral .right (.rat 0) (.rat 0) (.rat 0)
  let divergentBound : NExpr := .integral .interval (.rat 0) (.rat 1) (.unary .inv (.var 0))
  let bad : NExpr := .integral .right divergentBound (.rat 0) (.rat 0)
  let memo := ({} : Memo).insert (key good #[]) Ival.zero
  if (evalWith c memo bad #[]).isSome then
    throwError "a cached zero erased divergence in a bound"

end IntervalArith.NestedCertificates
