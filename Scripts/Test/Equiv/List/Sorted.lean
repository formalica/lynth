import Init.Data.List.Nat.Pairwise
import Init.Data.List.Range
import Init.Data.List.Zip

namespace SortedDefinitions

def AllP {α : Type} (p : α → Prop) : List α → Prop
| [] => True
| a :: t => p a ∧ AllP p t

def AllB {α : Type} (p : α → Bool) : List α → Bool
| [] => true
| a :: t => p a && AllB p t

theorem allP_iff_forall_mem {α : Type} {p : α → Prop} {l : List α} :
    AllP p l ↔ ∀ x, x ∈ l → p x := by
  induction l with
  | nil =>
      constructor
      · intro _
        intro x hx
        cases hx
      · intro _
        trivial
  | cons a t ih =>
      constructor
      · rintro ⟨ha, ht⟩ x hx
        cases hx with
        | head => simpa using ha
        | tail _ hx => exact ih.mp ht x hx
      · intro h
        refine ⟨h a (by simp), ?_⟩
        apply ih.mpr
        intro x hx
        exact h x (by simp [hx])

theorem allP_map_iff {α β : Type} {f : α → β} {p : β → Prop} {l : List α} :
    AllP p (l.map f) ↔ AllP (fun x => p (f x)) l := by
  induction l with
  | nil => simp [AllP]
  | cons a t ih => simp [AllP, ih]

def Sorted0 (l : List Nat) : Prop :=
  ∀ x y : Nat,
    0 ≤ x ∧ x < l.length →
    0 ≤ y ∧ y < l.length →
    x ≤ y →
    l[x]! ≤ l[y]!

def Sorted1 : List Nat → Prop
| [] | [_] => True
| a :: b :: t => a ≤ b ∧ Sorted1 (b :: t)

def Sorted2 : List Nat → Prop
| [] | [_] => True
| a :: b :: t => a < b ∧ Sorted2 (b :: t)

inductive Sorted3 : List Nat → Prop
| nil : Sorted3 []
| single (a : Nat) : Sorted3 [a]
| step {a b t} : a ≤ b → Sorted3 (b :: t) → Sorted3 (a :: b :: t)

inductive Sorted4 : List Nat → Prop
| nil : Sorted4 []
| single (a : Nat) : Sorted4 [a]
| step {a b t} : a < b → Sorted4 (b :: t) → Sorted4 (a :: b :: t)

def Sorted5Bool : List Nat → Bool
| [] | [_] => true
| a :: b :: t => decide (a ≤ b) && Sorted5Bool (b :: t)

def Sorted5 (l : List Nat) : Prop :=
  Sorted5Bool l = true

def Sorted6 (l : List Nat) : Prop :=
  AllP (fun p : Nat × Nat => p.1 ≤ p.2) (l.zip l.tail)

def OptionLe : Option Nat → Option Nat → Prop
| some a, some b => a ≤ b
| _, _ => True

def Sorted7 (l : List Nat) : Prop :=
  AllP (fun i : Nat => OptionLe l[i]? l[i + 1]?) (List.range (l.length - 1))

def Sorted8 : List Nat → Prop
| [] | [_] => True
| a :: t => AllP (fun b => a ≤ b) t ∧ Sorted8 t

def Sorted9 (l : List Nat) : Prop :=
  l.Pairwise (· ≤ ·)

theorem sorted8_iff_sorted9 {l : List Nat} :
    Sorted8 l ↔ Sorted9 l := by
  rw [Sorted9]
  induction l with
  | nil => simp [Sorted8]
  | cons a t ih =>
      cases t with
      | nil => simp [Sorted8]
      | cons b u =>
          simp [Sorted8, allP_iff_forall_mem, ih, List.pairwise_cons]

private theorem sorted1_rel_of_mem {a x : Nat} {l : List Nat} :
    Sorted1 (a :: l) → x ∈ l → a ≤ x := by
  induction l generalizing a with
  | nil =>
      intro _ hx
      cases hx
  | cons b t ih =>
      intro h hx
      rcases h with ⟨hab, htail⟩
      cases hx with
      | head => exact hab
      | tail _ hx => exact Nat.le_trans hab (ih htail hx)

theorem sorted1_iff_sorted9 {l : List Nat} :
    Sorted1 l ↔ Sorted9 l := by
  rw [Sorted9]
  constructor
  · intro h
    induction l with
    | nil =>
        exact List.Pairwise.nil
    | cons a t ih =>
        cases t with
        | nil =>
        simp
        | cons b u =>
            have htail : Sorted1 (b :: u) := h.2
            exact List.Pairwise.cons (fun x hx => sorted1_rel_of_mem h hx) (ih htail)
  · intro h
    induction h with
    | nil => simp [Sorted1]
    | @cons a t hrel htail ih =>
        cases t with
        | nil => simp [Sorted1]
        | cons b u => exact ⟨hrel b (by simp), ih⟩

theorem sorted1_iff_sorted8 {l : List Nat} :
    Sorted1 l ↔ Sorted8 l :=
  sorted1_iff_sorted9.trans sorted8_iff_sorted9.symm

theorem sorted0_iff_sorted9 {l : List Nat} :
    Sorted0 l ↔ Sorted9 l := by
  rw [Sorted9, List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij
    have h' := h i j ⟨Nat.zero_le i, hi⟩ ⟨Nat.zero_le j, hj⟩ (Nat.le_of_lt hij)
    simpa [List.getElem!_eq_getElem?_getD, hi, hj] using h'
  · intro h x y hx hy hxy
    cases Nat.lt_or_ge x y with
    | inl hlt =>
        have h' := h x y hx.2 hy.2 hlt
        simpa [List.getElem!_eq_getElem?_getD, hx.2, hy.2] using h'
    | inr hyx =>
        have hEq : x = y := Nat.le_antisymm hxy hyx
        subst hEq
        exact Nat.le_refl _

theorem sorted0_iff_sorted8 {l : List Nat} :
    Sorted0 l ↔ Sorted8 l :=
  sorted0_iff_sorted9.trans sorted8_iff_sorted9.symm

theorem sorted3_iff_sorted1 {l : List Nat} :
    Sorted3 l ↔ Sorted1 l := by
  constructor
  · intro h
    induction h with
    | nil => simp [Sorted1]
    | single _ => simp [Sorted1]
    | step hab _ ih => simp [Sorted1, hab, ih]
  · induction l with
    | nil =>
        intro _
        exact Sorted3.nil
    | cons a t ih =>
        cases t with
        | nil =>
            intro _
            exact Sorted3.single a
        | cons b u =>
            intro h
            exact Sorted3.step h.1 (ih h.2)

theorem sorted4_iff_sorted2 {l : List Nat} :
    Sorted4 l ↔ Sorted2 l := by
  constructor
  · intro h
    induction h with
    | nil => simp [Sorted2]
    | single _ => simp [Sorted2]
    | step hab _ ih => simp [Sorted2, hab, ih]
  · induction l with
    | nil =>
        intro _
        exact Sorted4.nil
    | cons a t ih =>
        cases t with
        | nil =>
            intro _
            exact Sorted4.single a
        | cons b u =>
            intro h
            exact Sorted4.step h.1 (ih h.2)

theorem sorted5_iff_sorted1 {l : List Nat} :
    Sorted5 l ↔ Sorted1 l := by
  induction l with
  | nil => simp [Sorted5, Sorted1, Sorted5Bool]
  | cons a t ih =>
      cases t with
      | nil => simp [Sorted5, Sorted1, Sorted5Bool]
      | cons b u =>
          constructor
          · intro h
            by_cases hab : a ≤ b
            · have htail : Sorted5 (b :: u) := by
                simp [Sorted5, Sorted5Bool, hab] at h
                exact h
              exact ⟨hab, ih.mp htail⟩
            · have : False := by
                simp [Sorted5, Sorted5Bool, hab] at h
              exact False.elim this
          · rintro ⟨hab, htail⟩
            have htail' : Sorted5 (b :: u) := ih.mpr htail
            simpa [Sorted5, Sorted5Bool, hab] using htail'

theorem sorted6_iff_sorted1 {l : List Nat} :
    Sorted6 l ↔ Sorted1 l := by
  induction l with
  | nil => simp [Sorted6, Sorted1, AllP]
  | cons a t ih =>
      cases t with
      | nil => simp [Sorted6, Sorted1, AllP]
      | cons b u =>
          constructor
          · intro h
            have h' : a ≤ b ∧ Sorted6 (b :: u) := by
              simpa [Sorted6, AllP] using h
            exact ⟨h'.1, ih.mp h'.2⟩
          · rintro ⟨hab, htail⟩
            have htail' : Sorted6 (b :: u) := ih.mpr htail
            simpa [Sorted6, Sorted1, AllP] using And.intro hab htail'

theorem sorted7_iff_sorted1 {l : List Nat} :
    Sorted7 l ↔ Sorted1 l := by
  induction l with
  | nil => simp [Sorted7, Sorted1, AllP]
  | cons a t ih =>
      cases t with
      | nil => simp [Sorted7, Sorted1, AllP]
      | cons b u =>
          constructor
          · intro h
            have h' : a ≤ b ∧ Sorted7 (b :: u) := by
              simpa [Sorted7, AllP, OptionLe, allP_map_iff, List.range_succ_eq_map] using h
            exact ⟨h'.1, ih.mp h'.2⟩
          · rintro ⟨hab, htail⟩
            have htail' : Sorted7 (b :: u) := ih.mpr htail
            simpa [Sorted7, AllP, OptionLe, allP_map_iff, List.range_succ_eq_map] using
              And.intro hab htail'

end SortedDefinitions
