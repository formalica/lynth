-- Finite-domain pilot: two guards (liar / honest), two responses
-- (`Blah` / `Mlah`), two doors (Heaven / Hell).
-- `question` and `deduce` are NOT defined: `lynth` must find them as
-- the value of the subtype below. `question_exists` is a `def`
-- returning that subtype (pair + correctness proof).
-- NOTE: the search space is finite: 2 guards x 2 response-vocabularies
-- x 2 door-assignments = 8 scenarios; question table 2^8 = 256,
-- deduce table 2^2 = 4, total 1024 candidates — brute-force applies.
-- TODO: failing until higher-order finite-function synthesis lands
-- in the pipeline.
import Mathlib.Logic.Equiv.Defs
import Lynth

inductive Response where
  | Blah
  | Mlah
  deriving DecidableEq

inductive Door where
  | Heaven
  | Hell
  deriving DecidableEq

inductive Guard where
  | Liar
  | Honest
  deriving DecidableEq

def response (g : Guard) (truth : Bool) (response_map : Response ≃ Bool) : Response :=
  match g with
  | .Liar => response_map.invFun (!truth)
  | .Honest => response_map.invFun truth

/-- The goal `lynth` must fill: a pair `(question, deduce)` plus the
proof that asking any guard "would you say 'Blah'?" and decoding via
`deduce` always yields that guard's actual door. -/
def question_exists :
    { qd : (Guard → (Response ≃ Bool) → (Guard ≃ Door) → Bool) × (Response → Door) //
      ∀ (g : Guard) (response_map : Response ≃ Bool) (door_map : Guard ≃ Door),
        qd.2 (response g (qd.1 g response_map door_map) response_map) = door_map g } := by
  lynth

/-- info: 'question_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms question_exists
