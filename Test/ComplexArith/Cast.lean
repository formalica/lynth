module
import Mathlib
public import Lynth

open Lynth.Interval

/-! # Integer / natural casts into `ℂ`.

Tiny regression tests locking the `intCastC` / `natCastC` entries
(direct `Int.cast` / `Nat.cast` patterns, not via `ofReal` unfolding).
-/

set_option maxHeartbeats 1397 in
-- CCast1: `((-3 : ℤ) : ℂ)`. (-3, 0)
public def cx_int_cast : { p : Rat × Rat //
    ‖((-3 : ℤ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_int_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_int_cast
#eval! cx_int_cast.1

set_option maxHeartbeats 1319 in
-- CCast2: `((7 : ℕ) : ℂ)`. (7, 0)
public def cx_nat_cast : { p : Rat × Rat //
    ‖((7 : ℕ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_nat_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_nat_cast
#eval! cx_nat_cast.1
