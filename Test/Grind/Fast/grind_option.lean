import Lynth.Grind.Tactic
-- This file uses `#guard_msgs` to check which lemmas `grind` is using.
-- This may prove fragile, so remember it is okay to update the expected output if appropriate!
-- Hopefully these will act as regression tests against `grind` activating irrelevant lemmas.

section

variable [BEq α] {o₁ o₂ o₃ o₄ o₅ : Option α}

/--
info: Try these:
  [apply] lynth_grind only [=_ Option.or_assoc, = Option.or_assoc, = Option.or_some, = Option.some_or,
    = Option.some_beq_none]
  [apply] lynth_grind =>
    instantiate only [=_ Option.or_assoc, = Option.or_assoc, = Option.or_some]
    instantiate only [= Option.some_or, = Option.or_some]
    instantiate only [= Option.some_beq_none]
-/
#guard_msgs in
example : ((o₁.or (o₂.or (some x))).or (o₄.or o₅) == none) = false := by lynth_grind?

/--
info: Try these:
  [apply] lynth_grind only [= Option.max_none_right, = Option.min_some_some, = Nat.min_def]
  [apply] lynth_grind =>
    instantiate only [= Option.max_none_right, = Option.min_some_some]
    instantiate only [= Nat.min_def]
-/
#guard_msgs in
example : max (some 7) none = min (some 13) (some 7) := by lynth_grind?

/--
info: Try these:
  [apply] lynth_grind only [= Option.guard_apply]
  [apply] lynth_grind => instantiate only [= Option.guard_apply]
-/
#guard_msgs in
example : Option.guard (· ≤ 7) 3 = some 3 := by lynth_grind?

/--
info: Try these:
  [apply] lynth_grind only [= Option.mem_bind_iff, #8b09]
  [apply] lynth_grind only [= Option.mem_bind_iff]
  [apply] lynth_grind =>
    instantiate only [= Option.mem_bind_iff]
    instantiate only [#8b09]
-/
#guard_msgs in
example {x : β} {o : Option α} {f : α → Option β} (h : a ∈ o) (h' : x ∈ f a) : x ∈ o.bind f := by lynth_grind?

end

open Option

theorem toList_toArray {o : Option α} : o.toArray.toList = o.toList := by
  lynth_grind

theorem toArray_toList {o : Option α} : o.toList.toArray = o.toArray := by
  lynth_grind

theorem size_toArray_eq_one_iff {o : Option α} :
    o.toArray.size = 1 ↔ o.isSome := by
  lynth_grind

theorem size_toArray_choice_eq_one [Nonempty α] : (choice α).toArray.size = 1 := by
  lynth_grind

theorem length_toList_eq_one_iff {o : Option α} :
    o.toList.length = 1 ↔ o.isSome := by
  lynth_grind

theorem length_toList_choice_eq_one [Nonempty α] : (choice α).toList.length = 1 := by
  lynth_grind

example : (default : Option α) = none := by lynth_grind

example (a : α) : Option.all q (guard p a) = (!p a || q a) := by lynth_grind

example (a : α) : Option.any q (guard p a) = (p a && q a) := by lynth_grind

example : (guard p a).or (guard q a) = guard (fun x => p x || q x) a := by lynth_grind
