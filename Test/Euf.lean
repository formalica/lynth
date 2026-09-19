-- EUF procedure checks: transitivity / symmetry chains over `Eq` hyps.
import Lynth
import Lynth.Euf.Procedure

open Lean Elab Tactic in
/-- Sharing unit check: `shareDerived` must publish reachable equalities. -/
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : True := by
  run_tac do
    let n ← Lynth.Euf.Procedure.shareDerived 8
    if n == 0 then throwError "euf shared nothing"
  trivial

/-- End-to-end: euf fails on `a + 0 = 5` but shares `a = 5` for later. -/
theorem euf_share (a b : Nat) (h1 : a = b) (h2 : b = 5) : a + 0 = 5 := by lynth

theorem euf_trans (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by lynth

theorem euf_symm (a b : Nat) (h : a = b) : b = a := by lynth

theorem euf_chain (a b c d : Nat) (h1 : a = b) (h2 : c = b) (h3 : c = d) :
    a = d := by lynth

theorem euf_refl_goal (a : Nat) : a = a := by lynth

-- congruence: equal args give equal applications
theorem euf_congr (a b : Nat) (f : Nat → Nat) (h : a = b) :
    f a = f b := by lynth

theorem euf_congr2 (a b c : Nat) (f : Nat → Nat → Nat) (h : a = b) :
    f a c = f b c := by lynth

theorem euf_congr_chain (a b : Nat) (f g : Nat → Nat) (h1 : a = b)
    (h2 : f b = g a) : f a = g b := by lynth

-- disequality via congruence: equal functions applied to equal args
-- cannot be disequal
theorem euf_ne (f : Nat → Nat) (a b : Nat) (h1 : a = b) (h2 : f a ≠ f b) :
    False := by lynth

-- direct `Ne` goal: intro + congruence contradicts the `≠` hyp
theorem euf_ne_direct (f : Nat → Nat) (a b : Nat) (h : f a ≠ f b) :
    a ≠ b := by lynth

theorem euf_ne_goal (a b c : Nat) (h1 : a = b) (h2 : b = c) :
    a ≠ c → False := by lynth

/-- info: 'euf_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms euf_trans
/-- info: 'euf_symm' does not depend on any axioms -/
#guard_msgs in
#print axioms euf_symm
/-- info: 'euf_chain' does not depend on any axioms -/
#guard_msgs in
#print axioms euf_chain
/-- info: 'euf_refl_goal' does not depend on any axioms -/
#guard_msgs in
#print axioms euf_refl_goal
/-- info: 'euf_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms euf_congr
/-- info: 'euf_congr2' does not depend on any axioms -/
#guard_msgs in
#print axioms euf_congr2
/-- info: 'euf_congr_chain' does not depend on any axioms -/
#guard_msgs in
#print axioms euf_congr_chain
/-- info: 'euf_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms euf_ne
/-- info: 'euf_ne_direct' does not depend on any axioms -/
#guard_msgs in
#print axioms euf_ne_direct
/-- info: 'euf_ne_goal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms euf_ne_goal
/-- info: 'euf_share' does not depend on any axioms -/
#guard_msgs in
#print axioms euf_share
