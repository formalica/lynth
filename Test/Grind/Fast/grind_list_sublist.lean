import Lynth.Grind.Tactic
open List

variable {α} {l₁ l₂ l₃ l₄ l₅ : List α}

example : l₂ ++ l₄ ⊆ l₁ ++ l₂ ++ l₃ ++ l₄ ++ l₅ := by
  lynth_grind

example : l₂ ++ l₄ <+ l₁ ++ l₂ ++ l₃ ++ l₄ ++ l₅ := by
  lynth_grind

example : l₁ ++ l₂ <+: l₁ ++ (l₂ ++ l₃) := by
  lynth_grind

example : l₂ ++ l₃ <:+ l₁ ++ l₂ ++ l₃ := by
  lynth_grind

example : l₂ ++ l₃ <:+: l₁ ++ l₂ ++ l₃ ++ l₄ := by
  lynth_grind

example (h : l₁ <:+: l₂) : l₁.filter p <:+: (l₂ ++ l₃).filter p := by
  lynth_grind

example (h : l₁ <+: l₂) : l₁.map f <+: (l₂ ++ l₃).map f := by
  lynth_grind

example (h : l₁ <+: l₂) : l₁.reverse <:+ xs ++ l₂.reverse := by lynth_grind

example (h : l₁ <+: l₂) : l₁.reverse <:+: xs ++ l₂.reverse := by lynth_grind

example (h : l₁ <:+: l₂) : l₁.reverse <:+: xs ++ l₂.reverse ++ ys := by lynth_grind

example (h : 8 ≤ xs.count 37) : replicate 7 37 <+ xs := by lynth_grind

-- Can we do this without unfolding `IsSuffix`?
example (h : replicate (n + 1) 37 <:+ xs) : n ≤ xs.count 37 := by lynth_grind [IsSuffix]

-- Can we do this without unfolding `IsInfix`?
example (h : replicate (n + 1) 37 <:+: xs) : n ≤ 2 * xs.count 37 := by lynth_grind [IsInfix]
