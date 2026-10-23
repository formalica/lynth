module
import Mathlib
public import Lynth

open Lynth.Interval

/-! # Golden ratio consumers: `Real.goldenRatio`.

`Real.goldenRatio` (Mathlib) lives in the internal registry
(`Lynth.Interval.Fns.GoldenRatio`, nullary `goldenRatioR` entry) because the
reifier never unfolds Mathlib definitions.  This file just exercises it
through powers, cosine, and a floor-nested power.  Ground truths are kernel
computations.
-/

-- φ² = 2.618033988749895...
set_option maxHeartbeats 4000 in
public def golden_two : { x : ℚ // abs (Real.goldenRatio ^ 2 - x) < 1 / 10 ^ 6 } := by
  lynth
/-- info: 'golden_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms golden_two
#eval golden_two.1

-- φ^(√2+1) ≈ 3.195...
set_option maxHeartbeats 4000 in
public def golden_sqrt_two : { x : ℚ // abs (Real.goldenRatio ^ (Real.sqrt 2 + 1) - x) < 1 / 10 ^ 6 } := by
  lynth
/-- info: 'golden_sqrt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms golden_sqrt_two
#eval golden_sqrt_two.1

-- cos(φ) ≈ -0.049...
set_option maxHeartbeats 4000 in
public def golden_cos : { x : ℚ // abs (Real.cos Real.goldenRatio - x) < 1 / 10 ^ 6 } := by
  lynth
/-- info: 'golden_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms golden_cos
#eval golden_cos.1

-- φ^⌊φ⌋ = φ^1: power nested with a Nat floor across types.
set_option maxHeartbeats 6000 in
public def golden_floor : { x : ℚ // abs (Real.goldenRatio ^ (Nat.floor Real.goldenRatio) - x) < 1 / 10 ^ 6 } := by
  lynth
/-- info: 'golden_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms golden_floor
#eval golden_floor.1