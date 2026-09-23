/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.AC.Types
public import Lynth.Grind.AC.Util
public import Lynth.Grind.AC.Var
public import Lynth.Grind.AC.Internalize
public import Lynth.Grind.AC.Eq
public import Lean.Meta.Tactic.Grind.AC.Seq
public import Lynth.Grind.AC.Proof
public import Lynth.Grind.AC.DenoteExpr
public import Lynth.Grind.AC.ToExpr
public import Lean.Meta.Tactic.Grind.AC.VarRename
public import Lynth.Grind.AC.PP
public import Lynth.Grind.AC.Inv
public import Lynth.Grind.AC.Action
open Lean.Meta
public section
namespace Lean.Lynth.Grind.AC
initialize registerTraceClass `lynth_grind.ac
initialize registerTraceClass `lynth_grind.ac.assert
initialize registerTraceClass `lynth_grind.ac.internalize
initialize registerTraceClass `lynth_grind.ac.basis

initialize registerTraceClass `lynth_grind.debug.ac.op
initialize registerTraceClass `lynth_grind.debug.ac.simp
initialize registerTraceClass `lynth_grind.debug.ac.check
initialize registerTraceClass `lynth_grind.debug.ac.queue
initialize registerTraceClass `lynth_grind.debug.ac.superpose
initialize registerTraceClass `lynth_grind.debug.ac.eq

initialize
  acExt.setMethods
    (internalize := AC.internalize)
    (newEq       := AC.processNewEq)
    (newDiseq    := AC.processNewDiseq)
    (action      := Action.ac)
    (check       := AC.check')
    (checkInv    := AC.checkInvariants)

end Lean.Lynth.Grind.AC
