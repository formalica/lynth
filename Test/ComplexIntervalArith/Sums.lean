import Mathlib
import Lynth
import Lynth.Interval.Goals.Series

open Lean Elab Tactic in
elab "lynth_cseries" : tactic => do
  let g ← getMainGoal
  let some pf ← Lynth.Interval.Goals.proveSeries? (← Lean.instantiateMVars (← g.getType))
    | throwError "series: no proof"
  g.assign pf
  replaceMainGoal []

/-!
Complex finite + infinite sums.

Ports of `Test/IntervalArith/Sums.lean` (5 finite) and
`Test/IntervalArith/InfiniteSums.lean` (6 infinite) to `Complex.*`
alternatives, plus 2 divergence proofs and 4 genuinely-complex
(nonzero-imaginary-part) extras.

Witnesses are `Rat × Rat` pairs; distance is `Complex.abs` (`‖·‖`).
Bodies use nat-cast literals (`(((1 : ℕ)) : ℂ)`); OfNat literals as
direct args to `+ℂ`/`*ℂ` do not reify.
-/

namespace ComplexIntervalArith

set_option maxHeartbeats 30 in
noncomputable def cx_fin_exp_cos_fn (k : ℕ) : ℂ := Complex.exp (-((k : ℕ) : ℂ)) * Complex.cos (((k : ℕ) : ℂ))

set_option maxHeartbeats 23930 in
/-- **CX-S01** — port of `sum_exp_cos`. -/
def cx_fin_exp_cos : { p : Rat × Rat //
    ‖(∑ k ∈ Finset.range 5, cx_fin_exp_cos_fn k) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_fin_exp_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_fin_exp_cos
#eval! cx_fin_exp_cos.1

set_option maxHeartbeats 65 in
noncomputable def cx_fin_geometric_fn (k : ℕ) : ℂ := ((((1 : ℕ)) : ℂ) / (((2 : ℕ)) : ℂ)) ^ (k + 1)

set_option maxHeartbeats 14200 in
/-- **CX-S02** — port of `sum_geometric_half_powers`. -/
def cx_fin_geometric : { p : Rat × Rat //
    ‖(∑ k ∈ Finset.range 100, cx_fin_geometric_fn k) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < (10 : ℝ) ^ (-30 : ℤ) } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_fin_geometric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_fin_geometric
#eval! cx_fin_geometric.1

set_option maxHeartbeats 61 in
noncomputable def cx_fin_sin_pi_fn (k : ℕ) : ℂ := Complex.sin (((Real.pi : ℂ) * (((k : ℕ) : ℂ) + (((1 : ℕ)) : ℂ))) / (((7 : ℕ)) : ℂ))

set_option maxHeartbeats 19502 in
/-- **CX-S03** — port of `sum_sin_pi_over_seven`. -/
def cx_fin_sin_pi : { p : Rat × Rat //
    ‖(∑ k ∈ Finset.range 5, cx_fin_sin_pi_fn k) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_fin_sin_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_fin_sin_pi
#eval! cx_fin_sin_pi.1

set_option maxHeartbeats 75 in
noncomputable def cx_fin_inv_sq_fn (k : ℕ) : ℂ := (((1 : ℕ)) : ℂ) / ((((k : ℕ) : ℂ) + (((1 : ℕ)) : ℂ)) ^ 2)

set_option maxHeartbeats 216897 in
/-- **CX-S04** — port of `series_inv_sq_tail` (theorem form). -/
theorem cx_series_inv_sq : ‖(∑ k ∈ Finset.range 1000, cx_fin_inv_sq_fn k) - ((Real.pi : ℂ) ^ 2 / 6)‖ < 1 / 500 := by
  lynth
/-- info: 'ComplexIntervalArith.cx_series_inv_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_series_inv_sq

set_option maxHeartbeats 81 in
noncomputable def cx_fin_alt_fn (k : ℕ) : ℂ := ((-1 : ℂ) ^ k) / ((((2 : ℕ)) : ℂ) * (((k : ℕ)) : ℂ) + (((1 : ℕ)) : ℂ))

set_option maxHeartbeats 39366 in
/-- **CX-S05** — port of `alternating_series_pi_over_four` (theorem form). -/
theorem cx_series_alt_pi : ‖(∑ k ∈ Finset.range 100, cx_fin_alt_fn k) - ((Real.pi : ℂ) / 4)‖ < 1 / 100 := by
  lynth
/-- info: 'ComplexIntervalArith.cx_series_alt_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_series_alt_pi

set_option maxHeartbeats 61 in
noncomputable def cx_tele1_body (k : ℕ) : ℂ :=
  1 / ((((1 : ℕ) : ℂ) + ((k : ℕ) : ℂ))
    * ((((1 : ℕ) : ℂ) + ((k : ℕ) : ℂ)) + ((1 : ℕ) : ℂ)))

set_option maxHeartbeats 4011 in
/-- **CX-I01** — port of `telescopingReciprocalsSubtype`. -/
def cx_tele1 : { p : Rat × Rat //
    Summable cx_tele1_body ∧
    ‖tsum cx_tele1_body - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 100000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_tele1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_tele1
#eval! cx_tele1.1

set_option maxHeartbeats 77 in
noncomputable def cx_tele2_body (k : ℕ) : ℂ :=
  1 / (((((k : ℕ) : ℂ) + ((k : ℕ) : ℂ)) + ((1 : ℕ) : ℂ))
    * ((((((k : ℕ) : ℂ) + ((k : ℕ) : ℂ)) + ((1 : ℕ) : ℂ)) + ((2 : ℕ) : ℂ))))

set_option maxHeartbeats 6373 in
/-- **CX-I02** — port of `fourSquareMinusOneSubtype`. -/
def cx_tele2 : { p : Rat × Rat //
    Summable cx_tele2_body ∧
    ‖tsum cx_tele2_body - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 100000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_tele2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_tele2
#eval! cx_tele2.1

set_option maxHeartbeats 42 in
noncomputable def cx_fact_body (k : ℕ) : ℂ :=
  (((1 : ℕ)) : ℂ) / ((((Nat.factorial (k + 1) : ℕ)) : ℂ))

set_option maxHeartbeats 4199 in
/-- **CX-I03** — port of `reciprocalFactorialsSubtype`. -/
def cx_fact : { p : Rat × Rat //
    Summable cx_fact_body ∧
    ‖tsum cx_fact_body - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 100000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_fact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_fact
#eval! cx_fact.1

set_option maxHeartbeats 73 in
noncomputable def cx_self_body (k : ℕ) : ℂ :=
  (((1 : ℕ)) : ℂ) / (((((k + 1 : ℕ)) : ℂ) ^ (k + 1)))

set_option maxHeartbeats 5353 in
/-- **CX-I04** — port of `reciprocalSelfPowersSubtype`. -/
def cx_self : { p : Rat × Rat //
    Summable cx_self_body ∧
    ‖tsum cx_self_body - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 100000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_self
#eval! cx_self.1

set_option maxHeartbeats 74 in
noncomputable def cx_mers_body (k : ℕ) : ℂ :=
  (((1 : ℕ)) : ℂ) / (((((2 : ℕ)) : ℂ) ^ (k + 1)) - (((1 : ℕ)) : ℂ))

set_option maxHeartbeats 10834 in
/-- **CX-I05** — port of `reciprocalMersenneNumbersSubtype`. -/
def cx_mers : { p : Rat × Rat //
    Summable cx_mers_body ∧
    ‖tsum cx_mers_body - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 100000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_mers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_mers
#eval! cx_mers.1

set_option maxHeartbeats 41 in
noncomputable def cx_fib_body (k : ℕ) : ℂ :=
  (((1 : ℕ)) : ℂ) / ((((Nat.fib (k + 1) : ℕ)) : ℂ))

set_option maxHeartbeats 8922 in
/-- **CX-I06** — port of `reciprocalFibonacciSubtype`. -/
def cx_fib : { p : Rat × Rat //
    Summable cx_fib_body ∧
    ‖tsum cx_fib_body - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 100000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_fib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_fib
#eval! cx_fib.1

set_option maxHeartbeats 68 in
noncomputable def cx_alt_body (k : ℕ) : ℂ :=
  ((-1 : ℂ) ^ k) / ((((k : ℕ)) : ℂ) + (((1 : ℕ)) : ℂ))

set_option maxHeartbeats 606 in
theorem cx_alt_not_summ : ¬ Summable cx_alt_body := by
  lynth_cseries
/-- info: 'ComplexIntervalArith.cx_alt_not_summ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_alt_not_summ

set_option maxHeartbeats 10 in
noncomputable def cx_const_body (_ : ℕ) : ℂ := 1

set_option maxHeartbeats 195 in
theorem cx_const_not_summ : ¬ Summable cx_const_body := by
  lynth_cseries
/-- info: 'ComplexIntervalArith.cx_const_not_summ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_const_not_summ

set_option maxHeartbeats 48 in
noncomputable def cx_ex_geomI (k : ℕ) : ℂ := (Complex.I / (((2 : ℕ)) : ℂ)) ^ k

set_option maxHeartbeats 2930 in
def cx_ex1 : { p : Rat × Rat //
    ‖(∑ k ∈ Finset.range 5, cx_ex_geomI k) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_ex1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_ex1
#eval! cx_ex1.1

set_option maxHeartbeats 21 in
noncomputable def cx_ex_expI (k : ℕ) : ℂ := Complex.exp ((((k : ℕ)) : ℂ) + Complex.I)

set_option maxHeartbeats 9838 in
def cx_ex2 : { p : Rat × Rat //
    ‖(∑ k ∈ Finset.range 3, cx_ex_expI k) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_ex2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_ex2
#eval! cx_ex2.1

set_option maxHeartbeats 21 in
noncomputable def cx_ex_sinI (k : ℕ) : ℂ := Complex.sin ((((k : ℕ)) : ℂ) * Complex.I)

set_option maxHeartbeats 11615 in
def cx_ex3 : { p : Rat × Rat //
    ‖(∑ k ∈ Finset.range 3, cx_ex_sinI k) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_ex3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_ex3
#eval! cx_ex3.1

set_option maxHeartbeats 21 in
noncomputable def cx_ex_linI (k : ℕ) : ℂ := ((((k : ℕ)) : ℂ) * Complex.I)

set_option maxHeartbeats 1797 in
def cx_ex4 : { p : Rat × Rat //
    ‖(∑ k ∈ Finset.range 4, cx_ex_linI k) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_ex4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_ex4
#eval! cx_ex4.1

end ComplexIntervalArith
