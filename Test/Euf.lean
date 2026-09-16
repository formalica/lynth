-- EUF procedure checks: transitivity / symmetry chains over `Eq` hyps.
import Lynth

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

#print axioms euf_trans
#print axioms euf_symm
#print axioms euf_chain
#print axioms euf_refl_goal
#print axioms euf_congr
#print axioms euf_congr2
#print axioms euf_congr_chain
