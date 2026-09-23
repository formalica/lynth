/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.Arith.Cutsat.Types
import Lynth.Grind.Arith.Cutsat.Util
open Lean.Meta
public section

namespace Lean.Lynth.Grind.Arith.Cutsat

def checkLeCnstrs (css : PArray (PArray LeCnstr)) (isLower : Bool) : GoalM Unit := do
  let mut x := 0
  for cs in css do
    for c in cs do
      checkCnstrOfPoly c.p x
      let .add a _ _ := c.p | unreachable!
      assert! isLower == (a < 0)
    x := x + 1
  return ()

def checkLowers : GoalM Unit := do
  let s ← get'
  assert! s.lowers.size == s.vars.size
  checkLeCnstrs s.lowers (isLower := true)

def checkUppers : GoalM Unit := do
  let s ← get'
  assert! s.uppers.size == s.vars.size
  checkLeCnstrs s.uppers (isLower := false)

def checkDvds : GoalM Unit := do
  let s ← get'
  assert! s.vars.size == s.dvds.size
  let mut x := 0
  for c? in s.dvds do
    if let some c := c? then
      checkCnstrOfPoly c.p x
      assert! c.d > 1
    x := x + 1

def checkVars : GoalM Unit := do
  let s ← get'
  let mut num := 0
  for ({ expr }, var) in s.varMap do
    if h : var < s.vars.size then
      let expr' := s.vars[var]
      assert! isSameExpr expr expr'
    else
      unreachable!
    num := num + 1
  assert! s.vars.size == num

def checkElimEqs : GoalM Unit := do
  let s ← get'
  assert! s.elimEqs.size == s.vars.size
  let mut x := 0
  for c? in s.elimEqs do
    if let some c := c? then
      assert! c.p.isSorted
      assert! c.p.checkCoeffs
      assert! s.elimStack.contains x
      assert! c.p.coeff x != 0
    x := x + 1

def checkElimStack : GoalM Unit := do
  for x in (← get').elimStack do
    assert! (← eliminated x)

def checkDiseqCnstrs : GoalM Unit := do
  let s ← get'
  assert! s.vars.size == s.diseqs.size
  let mut x := 0
  for cs in s.diseqs do
    for c in cs do
      checkCnstrOfPoly c.p x
    x := x + 1
  return ()

def checkInvariants : GoalM Unit := do
  checkVars
  checkDvds
  checkLowers
  checkUppers
  checkElimEqs
  checkElimStack
  checkDiseqCnstrs

end Lean.Lynth.Grind.Arith.Cutsat
