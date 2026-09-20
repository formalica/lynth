-- Synquid BV tests (test/current/BV-inc.sq, BV-dec.sq, BV-add.sq),
-- translated: synthesize `inc`, `dec`, `plus'`, `plus`.
-- TODO: failing until function synthesis over inductive domains lands.
import Lynth

/-- LSB-first bit string (Synquid's `BitVec`, renamed: core owns `BitVec`). -/
inductive Bits where
  | bit : Bool → Bits
  | cons : Bool → Bits → Bits

/-- Synquid's inline helper `bit`. -/
def bit (b : Bool) : Nat := if b then 1 else 0

/-- Synquid's `len` measure. -/
def len : Bits → Nat
  | .bit _ => 1
  | .cons _ xs => 1 + len xs

/-- Synquid's `value` measure (LSB first). -/
def value : Bits → Nat
  | .bit b => bit b
  | .cons b xs => bit b + 2 * value xs

/-- Increment. -/
def inc : { f : Bits → Bits // ∀ x, value (f x) = value x + 1 } := by
  lynth

/-- Decrement (precondition `value x > 0`). -/
def dec : { f : { x : Bits // value x > 0 } → Bits //
    ∀ x, value (f x) = value x.1 - 1 } := by
  lynth

/-- Addition with carry-in, equal-length inputs. -/
def plus' : { f : (x : Bits) → { y : Bits // len y = len x } → Bool → Bits //
    ∀ x y c, value (f x y c) = value x + value y.1 + bit c } := by
  lynth

/-- Addition, equal-length inputs. -/
def plus : { f : (x : Bits) → { y : Bits // len y = len x } → Bits //
    ∀ x y, value (f x y) = value x + value y.1 } := by
  lynth

/-- info: 'inc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms inc
/-- info: 'dec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms dec
/-- info: 'plus'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms plus'
/-- info: 'plus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms plus
