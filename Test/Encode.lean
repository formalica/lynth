-- Tseitin encoding + tautology oracle checks (pure, no axioms).
import Lynth.Sat.Encode

open Lynth.Sat.Encode

-- p → p is a tautology (atom 0)
#eval isTautology (.imp (.atom 0) (.atom 0)) 1
-- p ∧ q → p
#eval isTautology (.imp (.conj (.atom 0) (.atom 1)) (.atom 0)) 2
-- modus ponens skeleton: ((p → q) ∧ p) → q
#eval isTautology
  (.imp (.conj (.imp (.atom 0) (.atom 1)) (.atom 0)) (.atom 1)) 2
-- p alone is NOT a tautology
#eval !(isTautology (.atom 0) 1)
-- p ∨ q alone (as goal) is NOT a tautology
#eval !(isTautology (.disj (.atom 0) (.atom 1)) 2)
-- excluded middle p ∨ ¬p IS a (classical) tautology
#eval isTautology (.disj (.atom 0) (.neg (.atom 0))) 1
