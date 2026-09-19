-- Quant procedure: E-matching ground instantiation over EUF classes.
import Lynth
import Lynth.Quant.Procedure

open Lean Elab Tactic Meta

/-- Unit: `instantiate` fires and the instance closes the goal. -/
example (P : Nat → Prop) (_h : ∀ n, P n) (x : Nat) : P x := by
  run_tac do
    let n ← Lynth.Quant.Procedure.instantiate 6
    if n == 0 then throwError "quant instantiated nothing"
  assumption

/-- Unit: congruence-modulo matching asserts `R c (f a)`.
The only `R`-ground is the goal `R c (f b)`; reaching `R c (f a)`
goes through the `a ~ b` edge (canon path; verified by trace during
development with `[quantdbg] canon hit`). -/
example (R : Nat → Nat → Prop) (f : Nat → Nat) (a b c : Nat)
    (h1 : ∀ n, R n (f a)) (h2 : a = b) : R c (f b) := by
  run_tac do
    let n ← Lynth.Quant.Procedure.instantiate 6
    if n == 0 then throwError "quant instantiated nothing"
    withMainContext do
      let lctx ← getLCtx
      let some dR := lctx.findFromUserName? `R | throwError "no R"
      let some df := lctx.findFromUserName? `f | throwError "no f"
      let some da := lctx.findFromUserName? `a | throwError "no a"
      let some dc := lctx.findFromUserName? `c | throwError "no c"
      let want := mkApp (mkApp (.fvar dR.fvarId) (.fvar dc.fvarId))
        (mkApp (.fvar df.fvarId) (.fvar da.fvarId))
      let mut found := false
      for decl in ← getLCtx do
        if decl.type == want then found := true
      if !found then throwError "no R c (f a) instance"
  lynth

/-- End-to-end: instance `P x` enables `assumption` downstream. -/
theorem quant_single (P : Nat → Prop) (h : ∀ n, P n) (x : Nat) :
    P x := by lynth

/-- Multi-premise: `P x y → Q x y` instance closes the goal. -/
theorem quant_multi (P Q : Nat → Nat → Prop) (h : ∀ a b, P a b → Q a b)
    (x y : Nat) (h2 : P x y) : Q x y := by lynth

/-- Congruence-modulo: no purely syntactic instance exists; the `g = f c`
edge lets `R n (f n)` match `R c g`. -/
theorem quant_congr (R : Nat → Nat → Prop) (f : Nat → Nat) (g c : Nat)
    (h1 : ∀ n, R n (f n)) (h2 : g = f c) : R c g := by lynth

/-- No-match fallthrough: nothing to instantiate, pipeline unaffected. -/
theorem quant_nomatch (P Q : Nat → Prop) (_h : ∀ n, P n) (x : Nat)
    (hq : Q x) : Q x := by lynth

/-- info: 'quant_single' does not depend on any axioms -/
#guard_msgs in
#print axioms quant_single
/-- info: 'quant_multi' depends on axioms: [propext] -/
#guard_msgs in
#print axioms quant_multi
/-- info: 'quant_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms quant_congr
/-- info: 'quant_nomatch' does not depend on any axioms -/
#guard_msgs in
#print axioms quant_nomatch
