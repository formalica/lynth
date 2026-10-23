module
import Mathlib
public import Lynth

open Lynth.Interval

/-!
Nested floor/ceil/round: enclosures feed further real computation
(`docs/interval/05-point-goals.md §3`).  Ground truth checked against libm.
-/

set_option maxHeartbeats 6741 in
-- N1: floor of a composition, under sqrt. √8 ≈ 2.8284271247461903
public def floor_sqrt_nest : { x : Rat //
    abs (Real.sqrt (↑⌊Real.exp 2 + Real.sin 1⌋₊) - x) < 1 / 1000000 } := by
  lynth
/-- info: 'floor_sqrt_nest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floor_sqrt_nest
#eval floor_sqrt_nest.1

set_option maxHeartbeats 6444 in
-- N2: floor inside sin. sin 5 ≈ -0.9589242746631385
public def floor_sin_nest : { x : Rat //
    abs (Real.sin (↑⌊Real.exp 1 + Real.pi⌋₊) - x) < 1 / 1000000 } := by
  lynth
/-- info: 'floor_sin_nest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floor_sin_nest
#eval floor_sin_nest.1

set_option maxHeartbeats 34217 in
-- N3: Gamma-fed floor feeding division. 6/10 = 0.6
public def floor_gamma_div : { x : Rat //
    abs (((⌊Real.Gamma (1 / 4) + Real.Gamma (1 / 3)⌋₊ : ℕ) : ℝ) / 10 - x) < 1 / 1000000 } := by
  lynth
/-- info: 'floor_gamma_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floor_gamma_div
#eval floor_gamma_div.1

set_option maxHeartbeats 1917 in
-- N4: computed floor feeding `npow`. 2^3 = 8
public def floor_npow : { x : Rat //
    abs ((2 : ℝ) ^ ⌊Real.sqrt 2 + Real.sqrt 3⌋₊ - x) < 1 / 1000000 } := by
  lynth
/-- info: 'floor_npow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floor_npow
#eval floor_npow.1

set_option maxHeartbeats 4901 in
-- N5: computed ceil under sqrt. √9 = 3
public def ceil_sqrt_nest : { x : Rat //
    abs (Real.sqrt (↑⌈Real.exp 1 * Real.pi⌉₊) - x) < 1 / 1000000 } := by
  lynth
/-- info: 'ceil_sqrt_nest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ceil_sqrt_nest
#eval ceil_sqrt_nest.1

set_option maxHeartbeats 4341 in
-- N6: double nesting through a cast. ⌊5 + sin 1⌋₊ = 5
public def floor_double_nest : { n : Nat //
    n = ⌊((⌊(11 : ℝ) / 2⌋₊ : ℕ) : ℝ) + Real.sin 1⌋₊ } := by
  lynth
/-- info: 'floor_double_nest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floor_double_nest
#eval floor_double_nest.1

set_option maxHeartbeats 4870 in
-- N7: Nat.floor junk path (`⌊negative⌋₊ = 0`) composing correctly. √2
public def floor_neg_nest : { x : Rat //
    abs (Real.sqrt ((((⌊Real.sin 3 - 2⌋₊ : ℕ)) : ℝ) + 2) - x) < 1 / 1000000 } := by
  lynth
/-- info: 'floor_neg_nest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floor_neg_nest
#eval floor_neg_nest.1

set_option maxHeartbeats 262 in
-- N8: exact-integer hit. 2
public def floor_exact_hit : { n : Nat // n = ⌊(2 : ℝ)⌋₊ } := by
  lynth
/-- info: 'floor_exact_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floor_exact_hit
#eval floor_exact_hit.1

set_option maxHeartbeats 6183 in
-- I1: Int.floor nested in sin. sin 5
public def intfloor_sin_nest : { x : Rat //
    abs (Real.sin (↑⌊Real.exp 1 + Real.pi⌋) - x) < 1 / 1000000 } := by
  lynth
/-- info: 'intfloor_sin_nest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intfloor_sin_nest
#eval intfloor_sin_nest.1

set_option maxHeartbeats 4631 in
-- I2: Int.ceil under sqrt. 3
public def intceil_sqrt_nest : { x : Rat //
    abs (Real.sqrt (↑⌈Real.exp 1 * Real.pi⌉) - x) < 1 / 1000000 } := by
  lynth
/-- info: 'intceil_sqrt_nest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intceil_sqrt_nest
#eval intceil_sqrt_nest.1

set_option maxHeartbeats 5731 in
-- I3: round nested in sin. sin 6 ≈ -0.27941549819892586
public def round_sin_nest : { x : Rat //
    abs (Real.sin (↑(round (Real.exp 1 + Real.pi))) - x) < 1 / 1000000 } := by
  lynth
/-- info: 'round_sin_nest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms round_sin_nest
#eval round_sin_nest.1

set_option maxHeartbeats 5798 in
-- I4: Int witness with nested Int floor. 3
public def intfloor_wit_nest : { n : Int //
    n = ⌊(((⌊Real.exp 1 + 1⌋ : ℤ)) : ℝ) + Real.sin 1⌋ } := by
  lynth
/-- info: 'intfloor_wit_nest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intfloor_wit_nest
#eval intfloor_wit_nest.1

set_option maxHeartbeats 3801 in
-- I5: round tie behavior. sin 3
public def round_tie_nest : { x : Rat //
    abs (Real.sin (↑(round (5 / 2 : ℝ))) - x) < 1 / 1000000 } := by
  lynth
/-- info: 'round_tie_nest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms round_tie_nest
#eval round_tie_nest.1

set_option maxHeartbeats 2879 in
-- I6/I7/I8: negative Int floor/ceil/round composing. all 1
public def intfloor_neg : { x : Rat //
    abs ((((⌊-Real.exp 1⌋ : ℤ)) : ℝ) + 4 - x) < 1 / 1000000 } := by
  lynth
/-- info: 'intfloor_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intfloor_neg
#eval intfloor_neg.1

set_option maxHeartbeats 2879 in
public def intceil_neg : { x : Rat //
    abs ((((⌈-Real.exp 1⌉ : ℤ)) : ℝ) + 3 - x) < 1 / 1000000 } := by
  lynth
/-- info: 'intceil_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intceil_neg
#eval intceil_neg.1

set_option maxHeartbeats 2880 in
public def round_neg : { x : Rat //
    abs (((round (-Real.exp 1) : ℤ) : ℝ) + 4 - x) < 1 / 1000000 } := by
  lynth
/-- info: 'round_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms round_neg
#eval round_neg.1

set_option maxHeartbeats 5456 in
-- round witness (top level). 4
public def round_wit : { s : Int // round (Real.exp 1 + Real.sin 1) = s } := by
  lynth
/-- info: 'round_wit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms round_wit
#eval round_wit.1

set_option maxHeartbeats 7722 in
-- MD01 shape (existing suite target). 15
public def floor_exp_sin_cos : { n : Nat //
    n = ⌊(Real.exp 2 + Real.sin 1) / Real.cos 1⌋₊ } := by
  lynth
/-- info: 'floor_exp_sin_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floor_exp_sin_cos
#eval floor_exp_sin_cos.1

