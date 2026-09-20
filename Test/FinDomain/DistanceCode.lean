-- Finite-domain pilot: binary code with minimum Hamming distance.
-- Witness is a SET of 4 codewords of length 5 with pairwise distance ≥ 3.
-- Metric-threshold reasoning, not just ≠.
-- NOTE: C(32,4) ≈ 36k codeword sets — finite; brute-force applies.
-- TODO: failing until metric-threshold synthesis lands in the pipeline.
import Lynth

/-- Hamming distance between two 5-bit words. -/
def hamming : List Bool → List Bool → Nat :=
  fun a b => (a.zip b).countP (fun p => p.1 != p.2)

/-- Valid code: 4 words of length 5, pairwise distance ≥ 3. -/
def codeValid (c : List (List Bool)) : Prop :=
  c.length = 4 ∧ (∀ w ∈ c, w.length = 5) ∧ c.Nodup ∧
  (∀ w1 ∈ c, ∀ w2 ∈ c, w1 ≠ w2 → 3 ≤ hamming w1 w2)

/-- Computable check (mirrors `codeValid`). -/
def codeCheck (c : List (List Bool)) : Bool :=
  decide (c.length = 4) &&
  (c.all fun w => decide (w.length = 5)) &&
  (c.toArray.toList.eraseDups.length == c.length) &&
  (c.all fun w1 => c.all fun w2 =>
    (decide (w1 = w2)) || decide (3 ≤ hamming w1 w2))

/-- The goal `lynth` must fill: the codeword set. -/
def codeSol : { c : List (List Bool) // codeValid c } := by
  lynth

/-- Etalon: shortened [5,4,3] Hamming code words. -/
def etalon : List (List Bool) :=
  [[false,false,false,false,false],
   [false,true,true,false,true],
   [true,false,true,true,false],
   [true,true,false,true,true]]

-- The value computed by `lynth`:
#eval (codeSol : List (List Bool))

-- The etalon pairwise distances:
#eval etalon.map fun w1 => etalon.map fun w2 => hamming w1 w2

-- Runtime check: witness is a valid distance-3 code.
#guard codeCheck (codeSol : List (List Bool))

/-- info: 'codeSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms codeSol
