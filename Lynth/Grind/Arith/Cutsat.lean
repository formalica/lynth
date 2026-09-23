/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.Arith.Cutsat.DvdCnstr
public import Lynth.Grind.Arith.Cutsat.LeCnstr
public import Lynth.Grind.Arith.Cutsat.Search
public import Lynth.Grind.Arith.Cutsat.Inv
public import Lynth.Grind.Arith.Cutsat.Proof
public import Lynth.Grind.Arith.Cutsat.Types
public import Lynth.Grind.Arith.Cutsat.Util
public import Lynth.Grind.Arith.Cutsat.Var
public import Lynth.Grind.Arith.Cutsat.EqCnstr
public import Lynth.Grind.Arith.Cutsat.SearchM
public import Lynth.Grind.Arith.Cutsat.Model
public import Lynth.Grind.Arith.Cutsat.MBTC
public import Lynth.Grind.Arith.Cutsat.Nat
public import Lynth.Grind.Arith.Cutsat.CommRing
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.VarRename
public import Lynth.Grind.Arith.Cutsat.Action
open Lean.Meta
public section
namespace Lean.Lynth.Grind.Arith.Cutsat
initialize registerTraceClass `lynth_grind.lia
initialize registerTraceClass `lynth_grind.lia.nonlinear
initialize registerTraceClass `lynth_grind.lia.model
initialize registerTraceClass `lynth_grind.lia.assert
initialize registerTraceClass `lynth_grind.lia.assert.trivial
initialize registerTraceClass `lynth_grind.lia.assert.unsat
initialize registerTraceClass `lynth_grind.lia.assert.store
initialize registerTraceClass `lynth_grind.lia.assert.nonlinear

initialize registerTraceClass `lynth_grind.debug.lia.subst
initialize registerTraceClass `lynth_grind.debug.lia.search
initialize registerTraceClass `lynth_grind.debug.lia.search.split (inherited := true)
initialize registerTraceClass `lynth_grind.debug.lia.search.assign (inherited := true)
initialize registerTraceClass `lynth_grind.debug.lia.search.conflict (inherited := true)
initialize registerTraceClass `lynth_grind.debug.lia.search.backtrack (inherited := true)
initialize registerTraceClass `lynth_grind.debug.lia.internalize
initialize registerTraceClass `lynth_grind.debug.lia.toInt
initialize registerTraceClass `lynth_grind.debug.lia.search.cnstrs
initialize registerTraceClass `lynth_grind.debug.lia.search.reorder
initialize registerTraceClass `lynth_grind.debug.lia.elimEq

initialize
  cutsatExt.setMethods
    (internalize := Cutsat.internalize)
    (newEq       := Cutsat.processNewEq)
    (newDiseq    := Cutsat.processNewDiseq)
    (action      := Action.lia)
    (check       := Cutsat.check)
    (checkInv    := Cutsat.checkInvariants)
    (mbtc        := Cutsat.mbtc)

end Lean.Lynth.Grind.Arith.Cutsat
