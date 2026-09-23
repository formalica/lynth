/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.Arith.Linear.LinearM
import Lynth.Grind.Arith.Linear.Util
import Lean.Meta.Tactic.Grind.Arith.Linear.Inv
open Lean.Meta
namespace Lean.Lynth.Grind.Arith.Linear
/--
Returns `true` if the variables in the given polynomial are sorted
in decreasing order.
-/
def checkLeCnstrs (css : PArray (PArray IneqCnstr)) (isLower : Bool) : LinearM Unit := do
  let mut x := 0
  for cs in css do
    for c in cs do
      checkCnstrOfPoly c.p x
      let .add a _ _ := c.p | unreachable!
      assert! isLower == (a < 0)
    x := x + 1
  return ()

def checkLowers : LinearM Unit := do
  let s ← getStruct
  assert! s.lowers.size == s.vars.size
  checkLeCnstrs s.lowers (isLower := true)

def checkUppers : LinearM Unit := do
  let s ← getStruct
  assert! s.uppers.size == s.vars.size
  checkLeCnstrs s.uppers (isLower := false)

def checkDiseqCnstrs : LinearM Unit := do
  let s ← getStruct
  assert! s.vars.size == s.diseqs.size
  let mut x := 0
  for cs in s.diseqs do
    for c in cs do
      checkCnstrOfPoly c.p x
    x := x + 1
  return ()

def checkVars : LinearM Unit := do
  let s ← getStruct
  let mut num := 0
  for ({ expr }, var) in s.varMap do
    if h : var < s.vars.size then
      let expr' := s.vars[var]
      assert! isSameExpr expr expr'
    else
      unreachable!
    num := num + 1
  assert! s.vars.size == num

def checkStructInvs : LinearM Unit := do
  checkVars
  checkLowers
  checkUppers
  checkDiseqCnstrs

public def checkInvariants : GoalM Unit := do
  if (← isDebugEnabled) then
  for structId in *...(← get').structs.size do
    LinearM.run structId do
      assert! (← getStructId) == structId
      checkStructInvs

end Lean.Lynth.Grind.Arith.Linear
