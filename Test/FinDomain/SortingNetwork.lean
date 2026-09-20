-- Finite-domain pilot: universal sorting-network program.
-- Witness is a LIST of comparators (index pairs); correctness is
-- `∀ input ∈ all 2^3 binary inputs, running the network sorts`.
-- DfaLearn checks fixed examples; this is correctness on ALL inputs.
-- NOTE: bounded (≤ 3 comparators over 3 wires) — finite; brute-force applies.
-- TODO: failing until comparator-list synthesis lands in the pipeline.
import Lynth

/-- All 8 binary inputs. -/
def allInputs : List (List Bool) :=
  [[false,false,false],[false,false,true],[false,true,false],[false,true,true],
   [true,false,false],[true,false,true],[true,true,false],[true,true,true]]

/-- Apply one comparator (i,j): sort the pair at those positions. -/
def applyCmp (xs : List Bool) (c : Nat × Nat) : List Bool :=
  match xs[c.1]?, xs[c.2]? with
  | some a, some b =>
    let lo := a && b
    let hi := a || b
    ((xs.set c.1 lo).set c.2 hi)
  | _, _ => xs

/-- Run the whole network. -/
def runNet (net : List (Nat × Nat)) (xs : List Bool) : List Bool :=
  net.foldl applyCmp xs

/-- Sorted (non-decreasing) check on 3 bits. -/
def isSorted3 : List Bool → Bool
  | [a, b, c] => (!a || b) && (!b || c)
  | _ => false

/-- Network is correct: ≤ 3 comparators over wires 0..2, sorts all inputs. -/
def netValid (net : List (Nat × Nat)) : Prop :=
  net.length ≤ 3 ∧
  (∀ c ∈ net, c.1 < 3 ∧ c.2 < 3 ∧ c.1 ≠ c.2) ∧
  (∀ xs ∈ allInputs, isSorted3 (runNet net xs) = true)

/-- Computable check (mirrors `netValid`). -/
def netCheck (net : List (Nat × Nat)) : Bool :=
  decide (net.length ≤ 3) &&
  (net.all fun c => decide (c.1 < 3 ∧ c.2 < 3 ∧ c.1 ≠ c.2)) &&
  (allInputs.all fun xs => isSorted3 (runNet net xs))

/-- The goal `lynth` must fill: the comparator list. -/
def netSol : { net : List (Nat × Nat) // netValid net } := by
  lynth

/-- Etalon: classic 3-wire bubble network [(0,1),(1,2),(0,1)]. -/
def etalon : List (Nat × Nat) := [(0, 1), (1, 2), (0, 1)]

-- The value computed by `lynth`:
#eval (netSol : List (Nat × Nat))

-- The etalon sorts every input:
#eval allInputs.map (runNet etalon ·)

-- Runtime check: witness sorts all inputs within the bound.
#guard netCheck (netSol : List (Nat × Nat))

/-- info: 'netSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms netSol
