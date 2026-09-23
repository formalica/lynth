/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.Arith.Linear.Types
public import Lynth.Grind.Arith.Linear.Util
public import Lynth.Grind.Arith.Linear.Var
public import Lynth.Grind.Arith.Linear.StructId
public import Lynth.Grind.Arith.Linear.IneqCnstr
public import Lynth.Grind.Arith.Linear.Reify
public import Lynth.Grind.Arith.Linear.DenoteExpr
public import Lynth.Grind.Arith.Linear.ToExpr
public import Lynth.Grind.Arith.Linear.Proof
public import Lynth.Grind.Arith.Linear.SearchM
public import Lynth.Grind.Arith.Linear.Search
public import Lynth.Grind.Arith.Linear.PropagateEq
public import Lynth.Grind.Arith.Linear.Internalize
public import Lynth.Grind.Arith.Linear.Model
public import Lynth.Grind.Arith.Linear.PP
public import Lynth.Grind.Arith.Linear.Inv
public import Lynth.Grind.Arith.Linear.MBTC
public import Lean.Meta.Tactic.Grind.Arith.Linear.VarRename
public import Lynth.Grind.Arith.Linear.OfNatModule
public import Lynth.Grind.Arith.Linear.Action
open Lean.Meta
public section
namespace Lean.Lynth.Grind.Arith.Linear
initialize registerTraceClass `lynth_grind.linarith
initialize registerTraceClass `lynth_grind.linarith.internalize
initialize registerTraceClass `lynth_grind.linarith.assert
initialize registerTraceClass `lynth_grind.linarith.model
initialize registerTraceClass `lynth_grind.linarith.assert.unsat (inherited := true)
initialize registerTraceClass `lynth_grind.linarith.assert.trivial (inherited := true)
initialize registerTraceClass `lynth_grind.linarith.assert.store (inherited := true)
initialize registerTraceClass `lynth_grind.linarith.assert.ignored (inherited := true)

initialize registerTraceClass `lynth_grind.debug.linarith.search
initialize registerTraceClass `lynth_grind.debug.linarith.search.conflict (inherited := true)
initialize registerTraceClass `lynth_grind.debug.linarith.search.assign (inherited := true)
initialize registerTraceClass `lynth_grind.debug.linarith.search.split (inherited := true)
initialize registerTraceClass `lynth_grind.debug.linarith.search.backtrack (inherited := true)
initialize registerTraceClass `lynth_grind.debug.linarith.subst

initialize
  linearExt.setMethods
    (internalize := Linear.internalize)
    (newEq       := Linear.processNewEq)
    (newDiseq    := Linear.processNewDiseq)
    (action      := Action.linarith)
    (check       := Linear.check)
    (checkInv    := Linear.checkInvariants)
    (mbtc        := Linear.mbtc)

end Lean.Lynth.Grind.Arith.Linear
