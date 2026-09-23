/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.Arith.CommRing.Types
public import Lynth.Grind.Arith.CommRing.RingId
public import Lynth.Grind.Arith.CommRing.Internalize
public import Lynth.Grind.Arith.CommRing.RingM
public import Lynth.Grind.Arith.CommRing.SemiringM
public import Lynth.Grind.Arith.CommRing.NonCommRingM
public import Lynth.Grind.Arith.CommRing.NonCommSemiringM
public import Lynth.Grind.Arith.CommRing.Functions
public import Lynth.Grind.Arith.CommRing.Reify
public import Lynth.Grind.Arith.CommRing.EqCnstr
public import Lynth.Grind.Arith.CommRing.Proof
public import Lynth.Grind.Arith.CommRing.DenoteExpr
public import Lynth.Grind.Arith.CommRing.Inv
public import Lynth.Grind.Arith.CommRing.PP
public import Lynth.Grind.Arith.CommRing.MonadRing
public import Lynth.Grind.Arith.CommRing.MonadSemiring
public import Lynth.Grind.Arith.CommRing.Action
public import Lynth.Grind.Arith.CommRing.Power
open Lean.Meta
public section
namespace Lean.Lynth.Grind.Arith.CommRing
initialize registerTraceClass `lynth_grind.ring
initialize registerTraceClass `lynth_grind.ring.internalize
initialize registerTraceClass `lynth_grind.ring.assert
initialize registerTraceClass `lynth_grind.ring.assert.unsat (inherited := true)
initialize registerTraceClass `lynth_grind.ring.assert.trivial (inherited := true)
initialize registerTraceClass `lynth_grind.ring.assert.queue (inherited := true)
initialize registerTraceClass `lynth_grind.ring.assert.basis (inherited := true)
initialize registerTraceClass `lynth_grind.ring.assert.store (inherited := true)
initialize registerTraceClass `lynth_grind.ring.simp
initialize registerTraceClass `lynth_grind.ring.superpose
initialize registerTraceClass `lynth_grind.ring.impEq

initialize registerTraceClass `lynth_grind.debug.ring.simp
initialize registerTraceClass `lynth_grind.debug.ring.proof
initialize registerTraceClass `lynth_grind.debug.ring.check
initialize registerTraceClass `lynth_grind.debug.ring.impEq
initialize registerTraceClass `lynth_grind.debug.ring.simpBasis
initialize registerTraceClass `lynth_grind.debug.ring.basis
initialize registerTraceClass `lynth_grind.debug.ring.rabinowitsch

initialize
  ringExt.setMethods
    (internalize := CommRing.internalize)
    (newEq       := CommRing.processNewEq)
    (newDiseq    := CommRing.processNewDiseq)
    (action      := Action.ring)
    (check       := CommRing.check')
    (checkInv    := CommRing.checkInvariants)

end Lean.Lynth.Grind.Arith.CommRing
