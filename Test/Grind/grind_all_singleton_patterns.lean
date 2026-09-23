import Lynth.Grind.Tactic
example (p : Nat → Prop) (h₁ : x < n) (h₂ : ¬ p x) : ∃ i, i < n ∧ ¬ p i := by
  lynth_grind

example (p : Nat → Prop) (h : ¬ p x) : ∃ i, ¬ p i := by
  lynth_grind

example (p : Nat → Prop) (h₁ : x < n) (h₂ : ¬ p x) : ¬ (∀i < n, p i) := by
  lynth_grind

@[grind] def A (p q : Prop) := p ∧ q

example (p q : Nat → Prop) (h : ∀ x, A (p x) (q x)) : q a := by
  lynth_grind

example (p q r : Nat → Prop) (h : ∀ x, A (p x) (A (r x) (q x))) : r a := by
  lynth_grind
