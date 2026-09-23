/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Core
open Lean.Meta
public section
namespace Lean.Lynth.Grind.Arith

/-- State for the arithmetic procedures. -/
structure State where
  deriving Inhabited

end Lean.Lynth.Grind.Arith
