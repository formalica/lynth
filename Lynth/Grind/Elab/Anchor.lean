/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.Types
namespace Lean.Lynth.Grind.Elab
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta Lean.Lynth.Grind

public def elabAnchorRef (anchor : TSyntax `hexnum) : CoreM AnchorRef := do
  let numDigits := anchor.getHexNumSize
  let val := anchor.getHexNumVal
  if val >= UInt64.size then
    throwError "invalid anchor, value is too big"
  let anchorPrefix := val.toUInt64
  return { numDigits, anchorPrefix }

end Lean.Lynth.Grind.Elab
