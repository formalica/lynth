/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
-- Elaborators for `lynth_grind` / `lynth_grind?`.
--
-- NOTE (wrapper-first): these elaborate our syntax/config and then delegate to
-- the CORE grind engine (`Lean.Elab.Tactic.Grind`). Our adapted engine copy in
-- `Lynth.Grind.Elab.Main` cannot run under `lake env lean`: it calls C++-only
-- `@[extern]` kernels (`preprocess`, `internalize`, ...) whose native objects
-- never load in the interpreter, so every goal crashed with an IR assertion
-- violation / missing-native-implementation error. The core engine binds the
-- same C++ symbols from the toolchain, so it runs interpreted. This gives
-- `lynth_grind` full `grind` parity today; feeding our `@[lynth_grind]`
-- theorem DB as extra params is follow-up work (see TASKS.md).
import Lean.Elab.Tactic.Grind.Main
import Lynth.Grind.Elab.Main
import Lynth.Grind.AttrSyntax

open Lean Elab Tactic
open Lean.Parser.Tactic
open Lean.Parser.Tactic.Grind
open Lean.Lynth.Grind.Elab

@[tactic lynth_grind] def evalLynthGrind : Tactic := fun stx => do
  let `(tactic| lynth_grind $config:optConfig $[only%$only]? $[ [$params:grindParam,*] ]? $[=> $seq:grindSeq]?) := stx
    | throwUnsupportedSyntax
  let interactive := seq.isSome
  let config ← elabGrindConfig' config interactive
  -- Delegate to the core engine (see module NOTE above).
  Lean.Elab.Tactic.evalGrindCore stx config only params seq

@[tactic lynth_grindTrace] def evalLynthGrindTrace : Tactic := fun stx => do
  let `(tactic| lynth_grind? $config:optConfig $[only%$only]? $[ [$params:grindParam,*] ]?) := stx
    | throwUnsupportedSyntax
  -- Core's trace elaborator matches on `grind?` syntax, so rebuild an
  -- equivalent core node and delegate (see module NOTE).
  let coreStx : TSyntax `tactic ←
    if let some ps := params then
      `(tactic| grind? $config:optConfig $[only%$only]? [$(ps.getElems),*])
    else
      `(tactic| grind? $config:optConfig $[only%$only]?)
  let coreTacs ← Lean.Elab.Tactic.evalGrindTraceCore coreStx
  -- Rewrite top-level `grind` suggestions to `lynth_grind` by rebuilding
  -- through our own quotation (well-formed nodes pretty-print reliably;
  -- a bare kind-swap breaks the parenthesizer). Suggestions with `grind`
  -- nested under combinators are kept as-is (core text still works).
  let mut tacs := #[]
  for tac in coreTacs do
    let tac' ← match tac.raw with
      | `(tactic| grind $c:optConfig $[only%$o]? $[ [$ps:grindParam,*] ]? $[=> $sq:grindSeq]?) =>
        if let some ps := ps then
          if let some sq := sq then `(tactic| lynth_grind $c $[only%$o]? [$(ps.getElems),*] => $sq)
          else `(tactic| lynth_grind $c $[only%$o]? [$(ps.getElems),*])
        else
          if let some sq := sq then `(tactic| lynth_grind $c $[only%$o]? => $sq)
          else `(tactic| lynth_grind $c $[only%$o]?)
      | _ => pure tac
    tacs := tacs.push tac'
  if tacs.size == 1 then
    Lean.Meta.Tactic.TryThis.addSuggestion stx { suggestion := .tsyntax tacs[0]! }
  else
    Lean.Meta.Tactic.TryThis.addSuggestions stx <| tacs.map fun tac => { suggestion := .tsyntax tac }
