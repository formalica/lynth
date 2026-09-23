import Lynth.Grind.Tactic
open Prod

theorem swap_swap : ∀ x : α × β, swap (swap x) = x
  | ⟨_, _⟩ => by lynth_grind

theorem fst_swap {p : α × β} : (swap p).1 = p.2 := by lynth_grind

theorem snd_swap {p : α × β} : (swap p).2 = p.1 := by lynth_grind
