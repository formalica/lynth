import Lynth.Interval.Integral.NestedExpr
import Lynth.Interval.Integral.Math.NestedSyntaxProof

/-! Semantic facts about the scoped expression operations used by memo keys. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl

def maskEnv (e : Expr) (env : Array Ival) : Array Ival :=
  env.mapIdx fun i I => if e.uses i then I else Ival.zero

theorem key_env (e : Expr) (env : Array Ival) :
    (key e env).env = maskEnv (key e env).expr env := rfl

theorem sameIval_sound {a b : Ival} (h : sameIval a b = true) : a = b :=
  rawIvalEq_sound h

theorem key_beq_sound {a b : Key} (h : (a == b) = true) : a = b := by
  rcases a with ⟨ae,ax⟩
  rcases b with ⟨be,bx⟩
  have hh : ae = be ∧ ax.size = bx.size ∧
      (ax.zip bx).all (fun xy => sameIval xy.1 xy.2) = true := by
    change ((ae == be) && (ax.size == bx.size) &&
      (ax.zip bx).all (fun xy => sameIval xy.1 xy.2)) = true at h
    simpa only [Bool.and_eq_true,beq_iff_eq,and_assoc] using h
  obtain ⟨rfl,hlen,hzip⟩ := hh
  have he : ax = bx := by
    apply Array.ext hlen
    intro i hi hj
    have hiz : i < (ax.zip bx).size := by simp [hi,hj]
    have hm : (ax[i],bx[i]) ∈ ax.zip bx := by
      simpa only [Array.getElem_zip] using Array.getElem_mem (xs := ax.zip bx) hiz
    exact sameIval_sound (Array.all_eq_true_iff_forall_mem.mp hzip _ hm)
  cases he
  rfl

end Lynth.Interval.Integral.Nested
