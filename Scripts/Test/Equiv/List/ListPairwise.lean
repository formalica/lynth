import Mathlib

/-!
# `List.Pairwise` — ten equivalent definitions

`List.Pairwise r l` (`∀ i < j, r (l[i]) (l[j])`) recast in ten shapes: a
head/tail form, an explicit-index form, a two-element decomposition, an
append-split, `drop`-closure, `erase`-closure, `reverse`, a
`Nodup ∧ eraseDups` form, and an `indexOf`-ordering form.

Three of the ten coincide with Mathlib lemmas that already state exactly this
equivalence, and are proved by instantiating them: #3 (`List.pairwise_iff_getElem`),
#5 (`List.pairwise_append`), and #8 (`List.pairwise_reverse`).  The other seven
are proved here from scratch, mostly by structural induction on the list.

Items 7, 9, 10 need `[DecidableEq α]` (for `erase`, `eraseDups`, `indexOf`);
the rest are fully polymorphic.

**Why #2 must mention order.**  The tempting shape `∀ a ∈ l, ∀ b ∈ l.tail, r a b`
is *false*: with `r := (· < ·)` and `l = [0, 1, 2]` the left-hand side holds,
while the right-hand side asks for `r 2 1`, since `1 ∈ l.tail` although `2`
occurs *after* it.  Membership alone does not record order, so #2 splits `l` at
the element in question (`l = l₁ ++ a :: t`) and compares `a` with the tail `t`.

**Why #7 needs a second clause.**  `l.erase a` deletes only the *first*
`a`, so `Pairwise r (l.erase a)` for every `a ∈ l` sees a two-element list only
through its two singletons: for `l = [x, y]` with `x ≠ y` the right-hand side
below is vacuous while `Pairwise r [x, y]` is the unproven `r x y`.  Pairing the
closure clause with the head/tail clause makes it an equivalence again.

**Why #9 and #10 need the `Nodup` conjunct on *both* sides.**  `Pairwise r l`
constrains only *distinct positions* and says nothing about two equal entries, so
with `r := fun _ _ => True` it holds for `[x, x]`.  Conversely `l.eraseDups` and
`l.indexOf` only ever see the *first* occurrence of each entry: they cannot pin
down `Pairwise r l` without knowing that there are no repeats.  `Nodup l` is
exactly that hypothesis — it forces `l.eraseDups = l` and `l.idxOf (l[i]) = i`.
-/

namespace List

variable {α : Type}

/-- Lean v4.34 renamed `List.indexOf` to `List.idxOf`.  Statement #10 keeps the
historical spelling, so the old name is re-exposed here rather than editing it. -/
abbrev indexOf [BEq α] (a : α) : List α → ℕ := idxOf a

end List

namespace Equiv.ListPairwise

variable {α : Type}

/-- Erasing a member leaves a sublist.  Mathlib ships only the two-sided
`List.Sublist.erase` (`l₁ <+ l₂ → l₁.erase a <+ l₂.erase a`), so the one-sided
statement used by #7 is proved here. -/
private theorem erase_sublist [DecidableEq α] :
    ∀ (l : List α) (a : α), a ∈ l → (l.erase a).Sublist l := by
  intro l
  induction l with
  | nil => intro a ha; cases ha
  | cons b t ih =>
    intro a ha
    by_cases hab : a = b
    · rw [hab, List.erase_cons_head]
      exact List.sublist_cons_self b t
    · rw [List.erase_cons_tail (by simpa using Ne.symm hab)]
      exact List.Sublist.cons_cons b (ih a (Or.resolve_left (List.mem_cons.mp ha) hab))

/-- `eraseDups` is the identity on a duplicate-free list. -/
private theorem eraseDups_eq_self [DecidableEq α] :
    ∀ {l : List α}, l.Nodup → l.eraseDups = l := by
  intro l hl
  induction l with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨hna, hnas⟩ := List.nodup_cons.mp hl
    have hfilter : as.filter (fun b => !b == a) = as :=
      List.filter_eq_self.mpr fun b hb => by
        have hne : ¬b = a := fun hba => hna (hba ▸ hb)
        simp [hne]
    rw [List.eraseDups_cons, hfilter, ih hnas]

/-- In a duplicate-free list, `idxOf` is the identity on `getElem` indices. -/
private theorem idxOf_getElem_of_nodup [DecidableEq α] :
    ∀ (l : List α) (i : ℕ) (hi : i < l.length), l.Nodup → l.idxOf (l.get ⟨i, hi⟩) = i := by
  intro l i hi hl
  have hq : l.idxOf? (l.get ⟨i, hi⟩) = some i := by
    refine List.idxOf?_eq_some_iff.mpr ⟨hi, rfl, fun j hj hji => ?_⟩
    have hne : l[j] ≠ l[i] := List.pairwise_iff_getElem.mp hl j i (Nat.lt_trans hj hi) hi hj
    exact absurd hji hne
  rw [List.idxOf_eq_getD_idxOf?, hq]
  simp

/-- 1. The inductive definition, as the `nil`/`cons` case split. -/
theorem pairwise_iff_cases (r : α → α → Prop) (l : List α) :
    List.Pairwise r l ↔ (l = [] ∨ ∃ a t, (∀ x ∈ t, r a x) ∧ List.Pairwise r t ∧ l = a :: t) := by
  constructor
  · intro hp
    cases l with
    | nil => exact Or.inl rfl
    | cons a t =>
      exact Or.inr ⟨a, t, (List.pairwise_cons.mp hp).1, (List.pairwise_cons.mp hp).2, rfl⟩
  · rintro (rfl | ⟨a, t, hhead, hrest, rfl⟩)
    · exact List.Pairwise.nil
    · exact List.Pairwise.cons hhead hrest

/-- 2. As "every member relates to every member of the tail that follows it":
split `l` at the element under consideration.  See the file docstring for why the
`∀ a ∈ l, ∀ b ∈ l.tail, r a b` shape is false. -/
theorem pairwise_iff_mem_tail (r : α → α → Prop) (l : List α) :
    List.Pairwise r l ↔ ∀ l₁ a t, l = l₁ ++ a :: t → ∀ b ∈ t, r a b := by
  constructor
  · intro hp l₁ a t heq
    -- the right summand of the split is `a :: t`, and `Pairwise` looks at its head
    exact (List.pairwise_cons.mp (List.pairwise_append.mp (heq ▸ hp)).2.1).1
  · intro h
    induction l with
    | nil => exact List.Pairwise.nil
    | cons c t ih =>
      refine List.Pairwise.cons (h [] c t rfl) (ih fun l₁ a t' heq => ?_)
      exact h (c :: l₁) a t' (by simp only [heq, List.cons_append])

/-- 3. As an explicit bounded-index comparison.  This is `List.pairwise_iff_getElem`;
the bound `hi : i < l.length` is redundant (it follows from `i < j < l.length`) but has
to be spelled out for the `getElem` notation to elaborate. -/
theorem pairwise_iff_getElem (r : α → α → Prop) (l : List α) :
    List.Pairwise r l ↔
      ∀ (i j : ℕ) (hi : i < l.length), i < j → (hj : j < l.length) → r l[i] l[j] :=
  ⟨fun hp i j hi hij hj => List.pairwise_iff_getElem.mp hp i j hi hj hij,
   fun h => List.pairwise_iff_getElem.mpr fun i j hi hj hij => h i j hi hij hj⟩

/-- 4. As a two-element decomposition with a three-way split between them. -/
theorem pairwise_iff_append (r : α → α → Prop) (l : List α) :
    List.Pairwise r l ↔
      ∀ a b l₁ m l₂, l = l₁ ++ a :: m ++ b :: l₂ → r a b := by
  constructor
  · intro hp a b l₁ m l₂ heq
    -- `a` sits at the head of a suffix of `l`, and `b` inside that suffix's tail
    have hsplit : l = l₁ ++ a :: (m ++ b :: l₂) := by
      rw [heq, List.append_assoc, List.cons_append]
    refine (pairwise_iff_mem_tail r l).mp hp l₁ a (m ++ b :: l₂) hsplit b ?_
    exact List.mem_append.mpr (Or.inr (List.Mem.head l₂))
  · intro h
    induction l with
    | nil => exact List.Pairwise.nil
    | cons c t ih =>
      refine List.Pairwise.cons (fun b hb => ?_) (ih fun a b l₁ m l₂ heq => ?_)
      · obtain ⟨l₁, l₂, heq⟩ := List.mem_iff_append.mp hb
        exact h c b [] l₁ l₂ (by simp [heq])
      · refine h a b (c :: l₁) m l₂ ?_
        simp only [heq, List.cons_append]

/-- 5. As an append split with all cross pairs.  This is `List.pairwise_append`,
with the split `l = l₁ ++ l₂` made a hypothesis instead of being structural. -/
theorem pairwise_iff_append_split (r : α → α → Prop) (l : List α) :
    List.Pairwise r l ↔
      ∀ l₁ l₂, l = l₁ ++ l₂ →
        List.Pairwise r l₁ ∧ List.Pairwise r l₂ ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, r a b := by
  constructor
  · intro hp l₁ l₂ heq
    exact List.pairwise_append.mp (heq ▸ hp)
  · intro h
    exact List.pairwise_append.mpr ⟨List.Pairwise.nil, (h [] l rfl).2.1, by simp⟩

/-- 6. As closure under `drop` at every in-bounds index. -/
theorem pairwise_iff_drop (r : α → α → Prop) (l : List α) :
    List.Pairwise r l ↔ ∀ (i : ℕ), i < l.length → List.Pairwise r (l.drop i) := by
  constructor
  · intro hp i _
    -- `l.drop i` is a sublist of `l`, and `Pairwise` passes to sublists
    exact List.Pairwise.sublist (List.drop_sublist i l) hp
  · intro h
    cases l with
    | nil => exact List.Pairwise.nil
    | cons a t =>
      have h0 := h 0 (by simp)
      rw [List.drop_zero] at h0
      exact h0

/-- 7. As closure under `erase` at every member, together with the head/tail
clause.  Needs `[DecidableEq α]`.  See the file docstring for why the closure
clause alone is not an equivalence. -/
theorem pairwise_iff_erase (r : α → α → Prop) (l : List α) [DecidableEq α] :
    List.Pairwise r l ↔
      ∀ a ∈ l, List.Pairwise r (l.erase a) ∧ ∀ t, l = a :: t → ∀ b ∈ t, r a b := by
  constructor
  · intro hp a ha
    -- `l.erase a` is a sublist of `l`, and `Pairwise` passes to sublists
    refine ⟨List.Pairwise.sublist (erase_sublist l a ha) hp, fun t heq => ?_⟩
    exact (List.pairwise_cons.mp (heq ▸ hp)).1
  · intro h
    cases l with
    | nil => exact List.Pairwise.nil
    | cons a t =>
      -- erasing the head is exactly the tail, so both clauses land on `t`
      have ha' := h a (List.Mem.head t)
      exact List.Pairwise.cons (ha'.2 t rfl) (List.erase_cons_head a t ▸ ha'.1)

/-- 8. As the mirrored relation on `reverse`.  This is `List.pairwise_reverse`,
with the two sides transposed. -/
theorem pairwise_iff_reverse (r : α → α → Prop) (l : List α) :
    List.Pairwise r l ↔ List.Pairwise (fun a b => r b a) l.reverse := by
  constructor
  · intro hp
    exact List.Pairwise.reverse hp
  · intro hp
    exact List.pairwise_reverse.mp hp

/-- 9. As `Nodup` together with pairwise-ness of the deduplicated list.
Needs `[DecidableEq α]`.  The `Nodup` conjunct is essential and must be assumed
on both sides — see the file docstring. -/
theorem pairwise_iff_nodup_eraseDups (r : α → α → Prop) (l : List α) [DecidableEq α] :
    (List.Nodup l ∧ List.Pairwise r l) ↔
      (List.Nodup l ∧ List.Pairwise r l.eraseDups) := by
  constructor
  · rintro ⟨hn, hp⟩
    exact ⟨hn, by rw [eraseDups_eq_self hn]; exact hp⟩
  · rintro ⟨hn, hp⟩
    exact ⟨hn, by rw [← eraseDups_eq_self hn]; exact hp⟩

/-- 10. As an ordering statement on `indexOf`.  Needs `[DecidableEq α]`.  Here
`indexOf` is the pre-v4.34 name of `List.idxOf` (see the shim at the top of this
file). -/
theorem pairwise_iff_indexOf (r : α → α → Prop) (l : List α) [DecidableEq α] :
    (List.Nodup l ∧ List.Pairwise r l) ↔
      (List.Nodup l ∧
        ∀ a b, a ∈ l → b ∈ l → l.indexOf a < l.indexOf b → r a b) := by
  constructor
  · rintro ⟨hn, hp⟩
    refine ⟨hn, fun a b ha hb hlt => ?_⟩
    -- `indexOf` is the position of the first occurrence, so lift it to `getElem`
    have hia : l.idxOf a < l.length := List.idxOf_lt_length_of_mem ha
    have hib : l.idxOf b < l.length := List.idxOf_lt_length_of_mem hb
    have key := List.pairwise_iff_getElem.mp hp (l.idxOf a) (l.idxOf b) hia hib hlt
    rwa [List.getElem_idxOf hia, List.getElem_idxOf hib] at key
  · rintro ⟨hn, h⟩
    refine ⟨hn, List.pairwise_iff_getElem.mpr fun i j hi hj hij => ?_⟩
    -- in a duplicate-free list `indexOf (l[i]) = i`, so the ordering is the natural one
    refine h (l[i]) (l[j]) (List.getElem_mem hi) (List.getElem_mem hj) ?_
    change l.idxOf (l.get ⟨i, hi⟩) < l.idxOf (l.get ⟨j, hj⟩)
    have h₁ := idxOf_getElem_of_nodup l i hi hn
    have h₂ := idxOf_getElem_of_nodup l j hj hn
    omega

end Equiv.ListPairwise
