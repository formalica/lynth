import Init.Data.List.Basic
import Init.Data.List.Perm



namespace PermutationDefinitions

variable {α : Type u}

def Perm0 : List α → List α → Prop := List.Perm

def Perm1 [BEq α] [LawfulBEq α] (l₁ l₂ : List α) : Prop :=
  l₁.isPerm l₂

def Perm2 [BEq α] [LawfulBEq α] (l₁ l₂ : List α) : Prop :=
  ∀ a, l₁.count a = l₂.count a

def Perm3 [BEq α] [LawfulBEq α] : List α → List α → Prop
  | [], [] => True
  | [], _ :: _ => False
  | a :: l₁, l₂ => a ∈ l₂ ∧ Perm3 l₁ (l₂.erase a)

def Perm4 : List α → List α → Prop
  | [], [] => True
  | [], _ :: _ => False
  | a :: l₁, l₂ => ∃ s t, l₂ = s ++ a :: t ∧ Perm4 l₁ (s ++ t)

inductive Perm5 : List α → List α → Prop
  | nil : Perm5 [] []
  | insert (a : α) (s t : List α) {l : List α} :
      Perm5 l (s ++ t) → Perm5 (a :: l) (s ++ a :: t)

inductive Perm6 [BEq α] [LawfulBEq α] : List α → List α → Prop
  | nil : Perm6 [] []
  | erase (a : α) {l₁ l₂ : List α} :
      a ∈ l₂ → Perm6 l₁ (l₂.erase a) → Perm6 (a :: l₁) l₂

theorem perm1_iff_perm0 [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
  Perm1 l₁ l₂ ↔ Perm0 l₁ l₂ := by
  simpa [Perm1] using (List.isPerm_iff (l₁ := l₁) (l₂ := l₂))

theorem perm2_iff_perm0 [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
  Perm2 l₁ l₂ ↔ Perm0 l₁ l₂ := by
  simpa [Perm2] using (List.perm_iff_count (l₁ := l₁) (l₂ := l₂)).symm

theorem perm3_iff_perm0 [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
  Perm3 l₁ l₂ ↔ Perm0 l₁ l₂ := by
  unfold Perm0
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ <;> simp [Perm3]
  | cons a l₁ ih =>
      constructor
      · intro h
        rcases h with ⟨ha, htail⟩
        exact ((ih.mp htail).cons a).trans (List.perm_cons_erase ha).symm
      · intro h
        rcases List.cons_perm_iff_perm_erase.mp h with ⟨ha, htail⟩
        exact ⟨ha, ih.mpr htail⟩

theorem perm4_iff_perm0 {l₁ l₂ : List α} : Perm4 l₁ l₂ ↔ Perm0 l₁ l₂ := by
  unfold Perm0
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ <;> simp [Perm4]
  | cons a l₁ ih =>
      constructor
      · rintro ⟨s, t, rfl, htail⟩
        exact ((ih.mp htail).cons a).trans List.perm_middle.symm
      · intro h
        have ha : a ∈ l₂ := h.subset (by simp)
        rcases List.append_of_mem ha with ⟨s, t, rfl⟩
        refine ⟨s, t, rfl, ?_⟩
        apply ih.mpr
        simpa using (List.perm_inv_core (a := a) (l₁ := []) (l₂ := s) (r₁ := l₁) (r₂ := t) h)

theorem perm5_iff_perm4 {l₁ l₂ : List α} : Perm5 l₁ l₂ ↔ Perm4 l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil =>
          constructor
          · intro _
            trivial
          · intro _
            exact Perm5.nil
      | cons b l₂ =>
          constructor
          · intro h
            cases h
          · intro h
            cases h
  | cons a l₁ ih =>
      constructor
      · intro h
        cases h with
        | insert _ s t htail =>
            exact ⟨s, t, rfl, ih.mp htail⟩
      · intro h
        rcases h with ⟨s, t, rfl, htail⟩
        exact Perm5.insert a s t (ih.mpr htail)


theorem perm6_iff_perm3 [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    Perm6 l₁ l₂ ↔ Perm3 l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil =>
          constructor
          · intro _
            trivial
          · intro _
            exact Perm6.nil
      | cons b l₂ =>
          constructor
          · intro h
            cases h
          · intro h
            cases h
  | cons a l₁ ih =>
      constructor
      · intro h
        cases h with
        | erase _ ha htail =>
            exact ⟨ha, ih.mp htail⟩
      · intro h
        rcases h with ⟨ha, htail⟩
        exact Perm6.erase a ha (ih.mpr htail)



end PermutationDefinitions
