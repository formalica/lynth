/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.Order.Types
public import Lynth.Grind.Order.Internalize
public import Lynth.Grind.Order.StructId
public import Lynth.Grind.Order.OrderM
public import Lynth.Grind.Order.Assert
public import Lynth.Grind.Order.Util
open Lean.Meta
public section
namespace Lean.Lynth.Grind.Order
initialize registerTraceClass `lynth_grind.order
initialize registerTraceClass `lynth_grind.order.assert
initialize registerTraceClass `lynth_grind.order.internalize
initialize registerTraceClass `lynth_grind.order.internalize.term

initialize registerTraceClass `lynth_grind.debug.order
initialize registerTraceClass `lynth_grind.debug.order.add_edge (inherited := true)
initialize registerTraceClass `lynth_grind.debug.order.propagate (inherited := true)
initialize registerTraceClass `lynth_grind.debug.order.check_eq_true (inherited := true)
initialize registerTraceClass `lynth_grind.debug.order.check_eq_false (inherited := true)

initialize
  orderExt.setMethods
    (internalize := Order.internalize)
    (newEq       := Order.processNewEq)

end Lean.Lynth.Grind.Order
