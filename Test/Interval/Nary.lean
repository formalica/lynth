import Mathlib
import Lynth

open Lynth.Interval

/-! # User-defined n-ary custom functions (N1–N10).

End-to-end coverage for `CFn` over `Nat`/`Int`/`Rat`/`Real`: registry
(`@[lynth_cfn]`), reification (`Expr.call` nodes, rat lit-or-chain rule),
evaluation (discrete top-guard), and discrete/closed witnesses.
Ground truth checked against kernel computation.
-/

/-- N1–N3 setup: 2-ary Nat addition, 2-ary Int multiply, 3-ary Nat combo. -/
def myadd (a b : ℕ) : ℕ := a + b
def mymul (a b : ℤ) : ℤ := a * b
def myf3 (a b c : ℕ) : ℕ := a + 2 * b + 3 * c

set_option maxHeartbeats 20000 in
-- N1: 2-ary Nat, bare discrete witness. 7
def nary_nat_add : { n : Nat // n = myadd 3 4 } := by
  lynth
/-- info: 'nary_nat_add' does not depend on any axioms -/
#guard_msgs in
#print axioms nary_nat_add
#eval nary_nat_add.1

set_option maxHeartbeats 20000 in
-- N2: 2-ary Int with negatives, bare discrete witness. -12
def nary_int_mul : { s : Int // s = mymul (-3) 4 } := by
  lynth
/-- info: 'nary_int_mul' does not depend on any axioms -/
#guard_msgs in
#print axioms nary_int_mul
#eval nary_int_mul.1

set_option maxHeartbeats 20000 in
-- N3: 3-ary Nat, bare discrete witness. 14
def nary_nat_3ary : { n : Nat // n = myf3 1 2 3 } := by
  lynth
/-- info: 'nary_nat_3ary' does not depend on any axioms -/
#guard_msgs in
#print axioms nary_nat_3ary
#eval nary_nat_3ary.1

/-- N4 setup: manual 2-ary Real entry (`x² + y²`, composed interval ops). -/
def mysqadd (x y : ℝ) : ℝ := x * x + y * y

set_option maxHeartbeats 60000 in
-- N4: manual 2-ary Real via the closed procedure. 13
def nary_real_manual : { x : Rat //
    abs (mysqadd 2 3 - x) < 1 / 1000 } := by
  lynth
/-- info: 'nary_real_manual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nary_real_manual
#eval nary_real_manual.1

/-- N5/N7 setup: rational parameter and rational result. -/
def myratmul (q : ℚ) (x : ℝ) : ℝ := q * x

def myhalf (n : ℕ) : ℚ := n / 2

def myqmul (q : ℚ) (x : ℝ) : ℝ := q * x + 1

set_option maxHeartbeats 60000 in
-- N5: rational parameter (closed literal). 3
def nary_rat_param : { x : Rat //
    abs (myratmul (3 / 2) 2 - x) < 1 / 1000 } := by
  lynth
/-- info: 'nary_rat_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nary_rat_param
#eval nary_rat_param.1

set_option maxHeartbeats 60000 in
-- N6: rational result under a cast. 1/2
def nary_rat_result : { x : Rat //
    abs (((myhalf 3 : ℚ) : ℝ) - x) < 1 / 1000 } := by
  lynth
/-- info: 'nary_rat_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nary_rat_result
#eval nary_rat_result.1

set_option maxHeartbeats 60000 in
-- N7: nested rat result inside a rat parameter. 4
def nary_rat_nest : { x : Rat //
    abs (myqmul (myhalf 3) 2 - x) < 1 / 1000 } := by
  lynth
/-- info: 'nary_rat_nest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nary_rat_nest
#eval nary_rat_nest.1

set_option maxHeartbeats 60000 in
-- N8: manual nested in manual with a rational parameter. 5
def nary_nest_manual : { x : Rat //
    abs (mysqadd (myratmul (1 / 2) 4) 1 - x) < 1 / 1000 } := by
  lynth
/-- info: 'nary_nest_manual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nary_nest_manual
#eval nary_nest_manual.1

/-- N9 setup: noncomputable marker with an arbitrary internal type. -/
inductive MyTag where
  | A : MyTag
  | B : MyTag
  deriving DecidableEq, Repr

noncomputable def mywsum (a b : ℕ) : ℕ :=
  let tags : List MyTag := [MyTag.A, MyTag.B]
  a + b + tags.length

set_option maxHeartbeats 20000 in
-- N9: noncomputable with internal custom type, bare witness. 9
noncomputable def nary_noncomputable : { n : Nat // n = mywsum 3 4 } := by
  lynth
/-- info: 'nary_noncomputable' does not depend on any axioms -/
#guard_msgs in
#print axioms nary_noncomputable
-- `#eval[!]` cannot compile the noncomputable marker; the witness value is
-- checked definitionally instead (bare candidate is the literal `9`).
example : nary_noncomputable.1 = 9 := rfl

/-- N10 setup: 4-ary over all four `CTy`s. -/
def myall (a : ℕ) (z : ℤ) (q : ℚ) (x : ℝ) : ℝ := (a : ℝ) + (z : ℝ) + (q : ℝ) + x

set_option maxHeartbeats 60000 in
-- N10: 4-ary mixed, all `CTy`s. 2.5
def nary_mixed_4ary : { x : Rat //
    abs (myall 1 (-2) (1 / 2) 3 - x) < 1 / 1000 } := by
  lynth
/-- info: 'nary_mixed_4ary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nary_mixed_4ary
#eval nary_mixed_4ary.1

/-- info: 'myadd' does not depend on any axioms -/
#guard_msgs in
#print axioms myadd
/-- info: 'mymul' does not depend on any axioms -/
#guard_msgs in
#print axioms mymul
/-- info: 'myf3' does not depend on any axioms -/
#guard_msgs in
#print axioms myf3
/-- info: 'mysqadd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mysqadd
/-- info: 'myratmul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms myratmul
/-- info: 'myhalf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms myhalf
/-- info: 'myqmul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms myqmul
/-- info: 'mywsum' does not depend on any axioms -/
#guard_msgs in
#print axioms mywsum
/-- info: 'myall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms myall