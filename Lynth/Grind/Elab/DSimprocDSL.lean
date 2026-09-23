/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.Elab.Basic
public import Lean.Meta.Sym.DSimp
import Init.Sym.DSimp.DSimprocDSL
public section
namespace Lean.Lynth.Grind.Elab
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta Sym.DSimp

/-- Elaboration function for `sym_dsimproc` syntax. -/
abbrev SymDSimprocElab := Syntax → GrindTacticM DSimproc

unsafe initialize symDSimprocElabAttribute : KeyedDeclsAttribute SymDSimprocElab ←
  mkElabAttribute SymDSimprocElab `builtin_sym_dsimproc `sym_dsimproc
    `Lean.Parser.Sym.DSimp `Lean.Lynth.Grind.Elab.SymDSimprocElab "sym_dsimproc"

/-- Elaborate a `sym_dsimproc` syntax node into a `DSimproc`. -/
partial def elabSymDSimproc (stx : Syntax) : GrindTacticM DSimproc := do
  let elabFns := symDSimprocElabAttribute.getEntries (← getEnv) stx.getKind
  for elabFn in elabFns do
    try
      return (← elabFn.value stx)
    catch ex =>
      match ex with
      | .internal id _ =>
        if id == unsupportedSyntaxExceptionId then continue
        else throw ex
      | _ => throw ex
  throwErrorAt stx "unsupported sym_dsimproc syntax `{stx.getKind}`"

end Lean.Lynth.Grind.Elab
