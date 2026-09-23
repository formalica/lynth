import Lynth.Grind.Tactic
/--
error: `grind` failed
case grind.1
n m a : Nat
ih : ∀ {a : Nat}, a ^ 2 = 4 ^ m * n → False
h : a ^ 2 = 4 ^ (m + 1) * n
h_1 : ↑a = 4
⊢ False
-/
#guard_msgs in
example {n m a : Nat} (ih : ∀ {a : Nat}, a ^ 2 = 4 ^ m * n → False)
    (h : a ^ 2 = 4 ^ (m + 1) * n) : False := by
  lynth_grind -verbose

example {n m a : Nat} (ih : ∀ {a : Nat}, a ^ 2 = 4 ^ m * n → False)
    (h : a ^ 2 = 4 ^ m * n) : False := by
  lynth_grind

example {m a n : Nat} (ih : ∀ {a : Nat}, a ^ 2 = 4 ^ m * 4 * n → False)
    (h : a ^ 2 = 4 ^ (m + 1) * n) : False := by
  lynth_grind
