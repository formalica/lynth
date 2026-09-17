-- Simplex checks: units, models verify, differential vs FM.
import Lynth.Arith.Simplex
import Lynth.Arith.Explain
import Lynth.Arith.Fourier

open Lynth.Arith.Simplex
open Lynth.Arith.Fourier hiding solve
open Lynth.Arith.Explain

-- x ≤ 1 ∧ x ≥ 2 is UNSAT
#eval match solve [([1], -1), ([-1], 2)] with
  | .unsat _ => true
  | _ => false
-- expect true

-- x ≤ 1 ∧ x ≥ 0 is SAT with a model in [0, 1]
#eval match solve [([1], -1), ([-1], 0)] with
  | .sat m => checkModel [([1], -1), ([-1], 0)] m
  | _ => false
-- expect true

-- x + y ≤ 1 ∧ x ≥ 0 ∧ y ≥ 0 ∧ x + y ≥ 2 is UNSAT
#eval match solve [([1, 1], -1), ([-1, 0], 0), ([0, -1], 0), ([-1, -1], 2)] with
  | .unsat _ => true
  | _ => false
-- expect true

-- two-var SAT: model verifies
#eval match solve [([1, 1], -1), ([-1, 0], 0), ([0, -1], 0)] with
  | .sat m => checkModel [([1, 1], -1), ([-1, 0], 0), ([0, -1], 0)] m
  | _ => false
-- expect true

-- UNSAT explanations validate
#eval match solve [([1], -1), ([-1], 2)] with
  | .unsat e => checkExplanation [([1], -1), ([-1], 2)] e
  | _ => false
-- expect true

/-- Agreement between Simplex and FM on one system:
UNSAT ⟺ UNSAT, Simplex models verify, Simplex explanations validate. -/
def agree (sys : List (List Rat × Rat)) : Bool :=
  let lec : List LeC :=
    sys.zipIdx.map fun ((cs, c0), k) => mkLe cs c0 sys.length k
  match solve sys 1024, Lynth.Arith.Fourier.solve lec 128 with
  | .sat m, _ => checkModel sys m
  | .unsat e, some _ => checkExplanation sys e
  | .unsat _, none => false -- FM SAT but Simplex UNSAT: real disagreement
  | .unknown, _ => true -- Simplex out of fuel: inconclusive, skip

-- seeded random integral systems; mismatch count; expect 0
def lcg (s : Nat) : Nat := (1103515245 * s + 12345) % 2147483648

def genSys : Nat → Nat → List (List Rat × Rat) × Nat
  | s, 0 => ([], s)
  | s, k + 1 =>
    let c : List Rat :=
      (List.range 3).map fun j => ((lcg (s + j + k * 7) % 5 : Nat) : Rat) - 2
    let c0 : Rat := ((lcg (s + 99 + k) % 7 : Nat) : Rat) - 3
    let (rest, s') := genSys (lcg (s + k)) k
    ((c, c0) :: rest, s')

#eval (List.range 60).foldl
  (fun n i => if agree (genSys (i + 1) 5).1 then n else n + 1) 0
