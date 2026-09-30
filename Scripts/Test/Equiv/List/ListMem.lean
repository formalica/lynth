import Mathlib

/-!
# `List.Mem` — ten equivalent definitions

`List.Mem` (`a ∈ l`) recast in ten different shapes: index/projection,
decomposition, `erase`, `count`, `Finset` image, `filter`, `any`, and a
`head?`-of-a-suffix form.  Items 5–9 need `[DecidableEq α]`; items 1–4 and 10
are fully polymorphic.

Note the `∈` notation *is* `List.Mem`, so `a ∈ l` and `List.Mem a l` are the
same predicate; each equivalence below fixes one side and varies the other.
-/

namespace Equiv.ListMem

variable {α : Type}

/-- 1. Membership, spelled out.  `∈` *is* `List.Mem`, so this is `Iff.rfl`. -/
theorem mem_iff_mem (a : α) (l : List α) : List.Mem a l ↔ a ∈ l := Iff.rfl

/-- 2. As an `Option`-valued projection at some index. -/
theorem mem_iff_getElem (a : α) (l : List α) :
    a ∈ l ↔ ∃ (i : ℕ), l[i]? = some a := by
  constructor
  · intro h
    induction l with
    | nil => cases h
    | cons b t ih =>
      cases h with
      | head => exact ⟨0, by simp⟩
      | tail _ ht =>
        obtain ⟨i, hi⟩ := ih ht
        exact ⟨i + 1, by simpa using hi⟩
  · rintro ⟨i, hi⟩
    induction l generalizing i with
    | nil => simp at hi
    | cons b t ih =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero] at hi
        cases hi
        exact List.Mem.head t
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi
        exact List.Mem.tail b (ih j hi)

/-- 3. As a `get`-projection at a bounded index. -/
theorem mem_iff_get (a : α) (l : List α) :
    a ∈ l ↔ ∃ (i : ℕ) (h : i < l.length), l[i] = a := by
  constructor
  · intro h
    induction l with
    | nil => cases h
    | cons b t ih =>
      cases h with
      | head => exact ⟨0, by simp, by simp⟩
      | tail _ ht =>
        obtain ⟨i, hi, he⟩ := ih ht
        exact ⟨i + 1, by simpa using hi, by simpa using he⟩
  · rintro ⟨i, hi, he⟩
    induction l generalizing i with
    | nil => simp at hi
    | cons b t ih =>
      cases i with
      | zero =>
        have hba : b = a := by simpa using he
        subst hba
        exact List.Mem.head t
      | succ j =>
        have hj : j < t.length := by simpa using hi
        exact List.Mem.tail b (ih j hj (by simpa using he))

/-- 4. As a prefix/suffix split at the element. -/
theorem mem_iff_append_cons (a : α) (l : List α) :
    a ∈ l ↔ ∃ l₁ l₂, l = l₁ ++ a :: l₂ := by
  constructor
  · intro h
    induction l with
    | nil => cases h
    | cons b t ih =>
      cases h with
      | head => exact ⟨[], t, by simp⟩
      | tail _ ht =>
        obtain ⟨l₁, l₂, he⟩ := ih ht
        refine ⟨b :: l₁, l₂, ?_⟩
        simp [he]
  · rintro ⟨l₁, l₂, rfl⟩
    exact List.mem_append.mpr (Or.inr (List.Mem.head l₂))

/-- 5. Membership survives erasing a *different* element.  Needs `[DecidableEq α]`.

Note: the tempting `a ∈ l ↔ a ∉ l.erase a` is **false**.  `erase` drops only the *first*
occurrence, so for `l = [a, a]` we have `a ∈ l` and `a ∈ l.erase a` simultaneously (and for
`l = [a]` the second fails while the first holds).  `decide` refutes that iff outright, e.g.
at `a = 0, l = [0, 0]`.  With `b ≠ a` fixed, erase is a no-op on `a`. -/
theorem mem_iff_mem_erase (a b : α) (l : List α) [DecidableEq α] (hne : a ≠ b) :
    a ∈ l ↔ a ∈ l.erase b :=
  List.mem_erase_of_ne hne |>.symm

/-- 6. As a nonzero `count`.  Needs `[DecidableEq α]`. -/
theorem mem_iff_count_pos (a : α) (l : List α) [DecidableEq α] :
    a ∈ l ↔ 0 < l.count a :=
  List.count_pos_iff.symm

/-- 7. As `any` finding it.  Needs `[DecidableEq α]`. -/
theorem mem_iff_any (a : α) (l : List α) [DecidableEq α] :
    a ∈ l ↔ l.any (· == a) = true := by
  rw [List.any_eq_true]
  simp [beq_iff_eq]

/-- 8. As `filter` producing a nonempty list.  Needs `[DecidableEq α]`. -/
theorem mem_iff_filter_ne_nil (a : α) (l : List α) [DecidableEq α] :
    a ∈ l ↔ l.filter (· == a) ≠ [] := by
  constructor
  · intro h
    have hmem : a ∈ l.filter (· == a) := List.mem_filter.mpr ⟨h, by simp⟩
    intro hnil
    rw [hnil] at hmem
    cases hmem
  · intro h
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil (l.filter (· == a)) h
    obtain ⟨hxl, hxa⟩ := List.mem_filter.mp hx
    have hax : a = x := (beq_iff_eq.mp hxa).symm
    subst hax
    exact hxl

/-- 9. As membership in the `Finset` image.  Needs `[DecidableEq α]`. -/
theorem mem_iff_toFinset (a : α) (l : List α) [DecidableEq α] :
    a ∈ l ↔ a ∈ l.toFinset := by
  simp

/-- 10. As the `head?` of some suffix being `some a`. -/
theorem mem_iff_head?_drop (a : α) (l : List α) :
    a ∈ l ↔ ∃ n ≤ l.length, (l.drop n).head? = some a := by
  constructor
  · intro h
    induction l with
    | nil => cases h
    | cons b t ih =>
      cases h with
      | head => exact ⟨0, by simp, by simp⟩
      | tail _ ht =>
        obtain ⟨n, hn, hh⟩ := ih ht
        refine ⟨n + 1, ?_, ?_⟩
        · exact Nat.succ_le_succ hn
        · simpa using hh
  · rintro ⟨n, hn, hh⟩
    induction l generalizing n with
    | nil => simp at hh
    | cons b t ih =>
      cases n with
      | zero =>
        have hba : b = a := by simpa using hh
        subst hba
        exact List.Mem.head t
      | succ k =>
        have hk : k ≤ t.length := by simpa using hn
        simp only [List.drop_succ_cons] at hh
        exact List.Mem.tail b (ih k hk hh)

end Equiv.ListMem
