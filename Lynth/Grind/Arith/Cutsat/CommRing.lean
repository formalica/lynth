/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.Arith.Cutsat.Types
public import Lynth.Grind.Arith.CommRing.RingId
import Lynth.Grind.Simp
import Lynth.Grind.Arith.Cutsat.Util
import Lynth.Grind.Arith.Cutsat.Var
import Lynth.Grind.Arith.CommRing.Reify
import Lynth.Grind.Arith.CommRing.DenoteExpr
import Lynth.Grind.Arith.CommRing.SafePoly
open Lean.Meta
public section
namespace Lean.Lynth.Grind.Arith.Cutsat
/-!
CommRing interface for cutsat. We use it to normalize nonlinear polynomials.
-/

def getIntRingId? : GoalM (Option Nat) := do
  CommRing.getCommRingId? (← getIntExpr)

end Lean.Lynth.Grind.Arith.Cutsat
