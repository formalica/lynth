import Mathlib
import Lynth

open Lynth.Interval

/-! # User-defined custom functions: `Real → Real`.

Registration path for a user-defined function: golden-ratio power
`phi x = φ ^ x` with `φ = (1 + √5) / 2`.  The evaluator composes existing
sound interval ops, so the only new proofs are the composition steps.
Once registered with `@[lynth_fn]`, the reifier tries the entry before
unfolding the definition (`Reify.reify` step 4 vs step 5).
-/

/-- golden-ratio power (user-defined custom function). -/
noncomputable def phi (x : Real) : Real := ((1 + Real.sqrt 5) / 2) ^ x

/-- enclosure of the golden ratio `(1 + √5) / 2`. -/
def phiBase (c : Ctx) : Ival :=
  Ival.div c.prec
    (Ival.add c.prec Ival.one (Ival.sqrt c.prec (Ival.pt (Dy.ofNat 5))))
    (Ival.pt (Dy.ofNat 2))

theorem mem_phiBase {c : Ctx} : ((1 + Real.sqrt 5) / 2 : ℝ) ∈ phiBase c := by
  unfold phiBase
  have h5 : (5 : ℝ) ∈ Ival.pt (Dy.ofNat 5) := by
    have h := Ival.mem_pt (Dy.ofNat 5)
    simpa [Dy.toReal_def, Dy.toRat_ofNat] using h
  have h2 : (2 : ℝ) ∈ Ival.pt (Dy.ofNat 2) := by
    have h := Ival.mem_pt (Dy.ofNat 2)
    simpa [Dy.toReal_def, Dy.toRat_ofNat] using h
  exact Ival.mem_div
    (Ival.mem_add Ival.mem_one (Ival.mem_sqrt h5)) h2

@[lynth_fn] def phiR : Fn1 .real .real where
  name := "phi"
  graph x y := y = phi x
  exu := exu_eq _
  ev c X := Fns.rpowIval c (phiBase c) X
  sound := fun c x _ X hc hy hx => by
    obtain rfl := hy
    exact Fns.mem_rpowIval hc mem_phiBase hx
  cost := 120

-- φ² = 2.618033988749895...
set_option maxHeartbeats 4000 in
def phi_two : { x : ℚ // abs (phi 2 - x) < 1 / 10 ^ 6 } := by
  lynth
#print axioms phi_two
#eval phi_two.1

-- φ^(√2+1) ≈ 3.195...; custom fn of a compound real argument.
set_option maxHeartbeats 4000 in
def phi_sqrt_two : { x : ℚ // abs (phi (Real.sqrt 2 + 1) - x) < 1 / 10 ^ 6 } := by
  lynth
#print axioms phi_sqrt_two
#eval phi_sqrt_two.1

-- cos(φ) ≈ -0.049...; builtin outside, custom fn inside.
set_option maxHeartbeats 4000 in
def phi_cos : { x : ℚ // abs (Real.cos (phi 1) - x) < 1 / 10 ^ 6 } := by
  lynth
#print axioms phi_cos
#eval phi_cos.1

-- phi(⌊phi 1⌋) = phi 1: custom fn nested with a Nat floor across types.
set_option maxHeartbeats 6000 in
def phi_floor : { x : ℚ // abs (phi (Nat.floor (phi 1)) - x) < 1 / 10 ^ 6 } := by
  lynth
#print axioms phi_floor
#eval phi_floor.1
