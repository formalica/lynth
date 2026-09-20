-- Finite-domain pilot: DFA identification from examples.
--
-- WHAT IS THIS PROBLEM? A DFA (deterministic finite automaton) is a tiny
-- machine with finitely many states that reads words letter by letter.
-- It is defined by three things: `step` (in state `s`, seeing letter `a`,
-- go to which state?), `start` (which state to begin in), and `accept`
-- (which states are "good" at the end?). To run a word, start at `start`
-- and feed letters one by one through `step`; at the end check `accept`.
--
-- Example: machine for "word ends in 1": `start = 0`, `step s a = a`
-- (remember the last letter seen), `accept s = (s == 1)`.
-- Run [0,0,1]: 0 ->0 ->0 ->1, end in 1, accept = true.
-- Run [1,0]:   0 ->1 ->0, end in 0, accept = false.
--
-- THE TASK: given positive examples ([1], [0,1], [0,0,1]) that must be
-- accepted and negative examples ([], [0], [1,0], [0,0]) that must be
-- rejected, find ANY machine `(step, start, accept)` that does that.
-- Unlike the other pilots, the witness cannot be checked directly — it
-- must be RUN (via `foldl`) on each example word.
-- NOTE: `lynth` should infer finiteness: `step` has 2^(2*2) = 16 options,
-- `start` has 2, `accept` has 2^2 = 4 — 128 machines total, so brute-force
-- enumeration over structures containing functions applies.
-- TODO: failing until machine-synthesis lands in the pipeline.
import Lynth

/-- A 2-state DFA over the binary alphabet `Fin 2`. -/
structure DFA where
  step : Fin 2 → Fin 2 → Fin 2
  start : Fin 2
  accept : Fin 2 → Bool

/-- Run the machine on a word: fold `step` from `start`, check `accept`. -/
def run (d : DFA) (w : List (Fin 2)) : Bool :=
  d.accept (w.foldl d.step d.start)

/-- Words that must be accepted (all end in 1). -/
def positives : List (List (Fin 2)) := [[1], [0, 1], [0, 0, 1]]

/-- Words that must be rejected (empty or ending in 0). -/
def negatives : List (List (Fin 2)) := [[], [0], [1, 0], [0, 0]]

/-- A machine is correct if it accepts all positives and rejects all negatives. -/
def dfaValid (d : DFA) : Prop :=
  (∀ w ∈ positives, run d w = true) ∧ (∀ w ∈ negatives, run d w = false)

/-- Computable validity check (mirrors `dfaValid`). -/
def dfaValidCheck (d : DFA) : Bool :=
  positives.all (run d ·) && negatives.all (fun w => !(run d w))

/-- The goal `lynth` must fill: a computable DFA separating the examples. -/
def dfaSol : { d : DFA // dfaValid d } := by
  lynth

/-- Etalon: remember the last letter, accept iff it is 1. -/
def etalon : DFA := ⟨fun _ a => a, 0, (· == 1)⟩

-- The value computed by `lynth`:
#eval (dfaSol : DFA)

-- The etalon accepts the positives:
#eval positives.map (run etalon ·)

-- The etalon rejects the negatives:
#eval negatives.map (run etalon ·)

-- Runtime check: witness separates the examples.
#guard dfaValidCheck (dfaSol : DFA)

/-- info: 'dfaSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms dfaSol
