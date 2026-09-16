-- EUF procedure checks: transitivity / symmetry chains over `Eq` hyps.
import Lynth

theorem euf_trans (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by lynth

theorem euf_symm (a b : Nat) (h : a = b) : b = a := by lynth

theorem euf_chain (a b c d : Nat) (h1 : a = b) (h2 : c = b) (h3 : c = d) :
    a = d := by lynth

theorem euf_refl_goal (a : Nat) : a = a := by lynth

#print axioms euf_trans
#print axioms euf_symm
#print axioms euf_chain
#print axioms euf_refl_goal
