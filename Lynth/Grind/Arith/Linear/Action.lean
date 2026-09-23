/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.Action
import Lynth.Grind.Arith.Linear.Search
open Lean.Meta
namespace Lean.Lynth.Grind.Action

/-- Linear arithmetic action. -/
public def linarith : Action :=
  terminalAction Arith.Linear.check `(grind| linarith)

end Lean.Lynth.Grind.Action
