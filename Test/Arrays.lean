-- Array theory: read-over-write rules + select congruence routing.
import Lynth

/-- R1: `select (store a 0 v) 0 = v` via `Array.getElem_set_self`. -/
theorem arr_row_same (a : Array Nat) (ha : 0 < a.size) (v : Nat)
    (h2 : 0 < (a.set 0 v ha).size) :
    (a.set 0 v ha)[0]'h2 = v := by lynth

/-- R2 with literal indices: `0 ≠ 1` by `decide`. -/
theorem arr_row_diff_lit (a : Array Nat) (ha : 0 < a.size) (v : Nat)
    (h1 : 1 < (a.set 0 v ha).size) (h3 : 1 < a.size) :
    (a.set 0 v ha)[1]'h1 = a[1]'h3 := by lynth

/-- R2 with a `≠`-hypothesis premise. -/
theorem arr_row_diff_hyp (a : Array Nat) (i j v : Nat)
    (hi : i < a.size) (hj : j < a.size) (hij : i ≠ j)
    (hsi : j < (a.set i v hi).size) :
    (a.set i v hi)[j]'hsi = a[j]'hj := by lynth

/-- Select congruence with dependent proofs falls through to `sat`
(`simp` substitutes); documents the current routing. -/
theorem arr_congr_fallthrough (a b : Array Nat)
    (ha : 0 < a.size) (hb : 0 < b.size) (h : a = b) :
    a[0]'ha = b[0]'hb := by lynth

#print axioms arr_row_same
#print axioms arr_row_diff_lit
#print axioms arr_row_diff_hyp
#print axioms arr_congr_fallthrough
