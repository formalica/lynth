/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Attr
public import Init.Grind.Interactive
public section
-- Attribute syntax for `@[lynth_grind ...]` / `@[lynth_lia ...]`, mirroring
-- core `Init.Grind.Attr` (`grind`, `grind!`, ...): same `grindMod` argument
-- grammar, our attribute names. Lives in its own prelude module so the
-- engine files (which are `prelude` and use `(tactic|...)` quotations) can
-- see the syntax; user files get it through the `Lynth` root import.
namespace Lean.Parser.Tactic

syntax (name := lynth_grind)
  "lynth_grind" optConfig (&" only")?
  (" [" withoutPosition(grindParam,*) "]")?
  (" => " Grind.grindSeq)? : tactic

syntax (name := lynth_grindTrace)
  "lynth_grind?" optConfig (&" only")?
  (" [" withoutPosition(grindParam,*) "]")?
  : tactic

end Lean.Parser.Tactic

namespace Lean.Parser.Attr

syntax (name := lynth_grind) "lynth_grind" (ppSpace grindMod)? : attr
syntax (name := lynth_grind!) "lynth_grind!" (ppSpace grindMod)? : attr
syntax (name := lynth_grind?) "lynth_grind?" (ppSpace grindMod)? : attr
syntax (name := lynth_grind!?) "lynth_grind!?" (ppSpace grindMod)? : attr
syntax (name := lynth_lia) "lynth_lia" (ppSpace grindMod)? : attr
syntax (name := lynth_lia!) "lynth_lia!" (ppSpace grindMod)? : attr
syntax (name := lynth_lia?) "lynth_lia?" (ppSpace grindMod)? : attr
syntax (name := lynth_lia!?) "lynth_lia!?" (ppSpace grindMod)? : attr

end Lean.Parser.Attr
