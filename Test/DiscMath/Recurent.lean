import Lynth

namespace DiscMath

/-- Synthesize a two-parameter function satisfying
`G c (n + 1) = n² + G c n` for every `c` and `n`. -/
def recurent_ :
    { G : Rat → Nat → Rat //
      ∀ c,
        G c 0 = c ∧
        ∀ n, G c (n + 1) = (n : Rat) ^ 2 + G c n } := by
  lynth

/-- `c = 0`, `n = 10`: `0² + 1² + … + 9² = 285`. -/
#eval recurent_.1 0 10

/-- `c = 7`, `n = 10`: `7 + 0² + … + 9² = 292`. -/
#eval recurent_.1 7 10

end DiscMath
