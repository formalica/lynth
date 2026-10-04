-- Cross-fragment corpus: every procedure must route correctly.
import Lynth

theorem k2 (x y : Int) (h1 : x = y) (h2 : x + 1 ≤ 0) : y + 1 ≤ 0 := by lynth
/-- info: 'k2' does not depend on any axioms -/
#guard_msgs in
#print axioms k2
