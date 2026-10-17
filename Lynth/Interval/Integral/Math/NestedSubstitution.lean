import Lynth.Interval.Integral.Math.NestedDefs

/-! Capture-avoiding operations on absolute binder levels. The definitions
and two semantic obligations depend only on NestedDefs and Mathlib, and are
mirrored in /tmp/intgrl for independent proofs. -/
namespace Intgrl

def NExpr.shift (e : NExpr) (cutoff amount : Nat) : NExpr :=
  match e with
  | .var i => .var (if cutoff ≤ i then i+amount else i)
  | .unary op a => .unary op (a.shift cutoff amount)
  | .binary op a b => .binary op (a.shift cutoff amount) (b.shift cutoff amount)
  | .pow a n => .pow (a.shift cutoff amount) n
  | .rpow a q => .rpow (a.shift cutoff amount) q
  | .integral k a b f => .integral k
      (a.shift cutoff amount) (b.shift cutoff amount) (f.shift cutoff amount)
  | e => e

/-- Replacement terms start in the scope ending at i. Their own binders
must move past each additional binder encountered in the source body. -/
def NExpr.replace (e : NExpr) (i : Nat) (v : NExpr) : NExpr :=
  match e with
  | .var j => if i == j then v else .var j
  | .unary op a => .unary op (a.replace i v)
  | .binary op a b => .binary op (a.replace i v) (b.replace i v)
  | .pow a n => .pow (a.replace i v) n
  | .rpow a q => .rpow (a.replace i v) q
  | .integral k a b f => .integral k (a.replace i v) (b.replace i v)
      (f.replace i (v.shift (i+1) 1))
  | e => e

theorem NExpr.shift_real {e : NExpr} {xs ys : List ℝ}
    (hs : e.scoped xs.length = true) :
    (e.shift xs.length ys.length).real (xs++ys) = e.real xs := by
  sorry

theorem NExpr.replace_real {e v : NExpr} {xs : List ℝ}
    (he : e.scoped (xs.length+1) = true) (hv : v.scoped (xs.length+1) = true)
    (t : ℝ) :
    (e.replace xs.length v).real (xs++[t]) =
      e.real (xs++[v.real (xs++[t])]) := by
  sorry

end Intgrl
