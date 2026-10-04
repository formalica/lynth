import Mathlib
import Lynth

namespace DiscMath

def IsUniqueNearestRoot (f : ℝ → ℝ) (q : Rat) (r : ℝ) : Prop :=
  f r = 0 ∧
  ∀ z : ℝ, f z = 0 →
    abs (r - (q : ℝ)) ≤ abs (z - (q : ℝ)) ∧
    (abs (r - (q : ℝ)) = abs (z - (q : ℝ)) → z = r)

def x :
    { r : ℝ //
      IsUniqueNearestRoot
        (fun t : ℝ => t ^ 2 - 2)
        ((7 : Rat) / 5)
        r } := by
  lynth
#print axioms x

def y :
    { r : ℝ //
      IsUniqueNearestRoot
        (fun t : ℝ => t ^ 2 - 3)
        ((17 : Rat) / 10)
        r } := by
  lynth
#print axioms y

def IsMinimalPoly (z : ℝ) (p : Polynomial ℚ) : Prop :=
  p.Monic ∧
  p.aeval z = 0 ∧
  ∀ q : Polynomial ℚ,
    q.Monic → q.aeval z = 0 → p.degree ≤ q.degree

def minPolyXY :
    { s : Polynomial ℚ × Rat //
      IsMinimalPoly (x.1 + y.1) s.1 ∧
      IsUniqueNearestRoot
        (fun t : ℝ => s.1.aeval t)
        s.2
        (x.1 + y.1) } := by
  lynth
#print axioms minPolyXY

theorem invXY :
    (x.1 + y.1)⁻¹ = y.1 - x.1 := by
  lynth
#print axioms invXY

#eval minPolyXY.1.2

end DiscMath
