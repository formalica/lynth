import Init.GetElem
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Data.List.Count
import Init.Data.List.Nat.Count
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Pairwise

def Distinct0 (l : List Nat) : Prop :=
  ∀ x y : Nat,
    x < l.length →
    y < l.length →
    l[x]! = l[y]! →
    x = y

def Distinct1 (l : List Nat) : Prop :=
  ∀ x y : Nat, l[x]? = l[y]? → l[x]? ≠ none → x = y

def Distinct2 (l : List Nat) : Prop :=
  ∀ x y : Nat, x ≠ y → l[x]? ≠ none → l[x]? ≠ l[y]?

def Distinct3 (l : List Nat) : Prop :=
  ∀ x y, x < l.length → y < l.length → l[x]? = l[y]? → x = y

def Distinct4 (l : List Nat) : Prop :=
  ∀ x y, x < l.length → y < l.length → x ≠ y → l[x]? ≠ l[y]?

def Distinct5 (l : List Nat) : Prop :=
  ∀ a, l.count a ≤ 1

def Distinct6 (l : List Nat) : Prop :=
  ∀ a, l.count a = 0 ∨ l.count a = 1

def Distinct7 (l : List Nat) : Prop :=
  ∀ a, (l.filter fun x => x = a).length ≤ 1

def Distinct8 (l : List Nat) : Prop :=
  l.Nodup

private theorem getElemOption_eq_some_getElem {α : Type} {l : List α} {i : Nat}
    (hi : i < l.length) : l[i]? = some l[i] := by
  exact List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩

private theorem getElemOption_ne_none_iff_lt {α : Type} {l : List α} {i : Nat} :
    l[i]? ≠ none ↔ i < l.length := by
  constructor
  · intro h
    by_cases hi : i < l.length
    · exact hi
    · exact False.elim <| h <| List.getElem?_eq_none (l := l) (i := i) (by simpa [Nat.not_lt] using hi)
  · intro hi
    rw [getElemOption_eq_some_getElem hi]
    intro hnone
    cases hnone

private theorem getElem_eq_of_option_eq {α : Type} {l : List α} {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) : l[i]? = l[j]? → l[i] = l[j] := by
  intro h
  have h' : some l[i] = some l[j] := by
    simpa [getElemOption_eq_some_getElem hi, getElemOption_eq_some_getElem hj] using h
  simpa using h'

private theorem option_eq_of_getElem_eq {α : Type} {l : List α} {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) : l[i] = l[j] → l[i]? = l[j]? := by
  intro h
  calc
    l[i]? = some l[i] := getElemOption_eq_some_getElem hi
    _ = some l[j] := by simp [h]
    _ = l[j]? := (getElemOption_eq_some_getElem hj).symm

private theorem distinct4_iff_distinct8 {l : List Nat} : Distinct4 l ↔ Distinct8 l := by
  rw [Distinct8, List.Nodup, List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij
    intro hijEq
    exact (h i j hi hj (Nat.ne_of_lt hij) (option_eq_of_getElem_eq hi hj hijEq)).elim
  · intro h x y hx hy hxy
    intro hxyOpt
    rcases Nat.lt_trichotomy x y with hlt | rfl | hgt
    · exact (h x y hx hy hlt (getElem_eq_of_option_eq hx hy hxyOpt)).elim
    · exact (hxy rfl).elim
    · exact (h y x hy hx hgt (getElem_eq_of_option_eq hy hx hxyOpt.symm)).elim

private theorem distinct5_iff_distinct8 {l : List Nat} : Distinct5 l ↔ Distinct8 l := by
  simpa [Distinct5, Distinct8] using (List.nodup_iff_count (l := l)).symm

private theorem filter_beq_eq_filter_eq (l : List Nat) (a : Nat) :
    l.filter (fun x => x == a) = l.filter (fun x => x = a) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases h : x = a
      · simp [h, ih]
      · simp [h, beq_iff_eq, ih]

private theorem count_eq_filter_length (l : List Nat) (a : Nat) :
    l.count a = (l.filter fun x => x = a).length := by
  calc
    l.count a = l.countP (· == a) := List.count_eq_countP
    _ = (l.filter fun x => x == a).length := List.countP_eq_length_filter
    _ = (l.filter fun x => x = a).length := by rw [filter_beq_eq_filter_eq]

theorem distinct3_iff_distinct4 {l : List Nat} : Distinct3 l ↔ Distinct4 l := by
  constructor
  · intro h x y hx hy hxy
    intro hxyEq
    exact hxy (h x y hx hy hxyEq)
  · intro h x y hx hy hxyEq
    by_cases hxy : x = y
    · exact hxy
    · exact False.elim (h x y hx hy hxy hxyEq)

private theorem distinct3_iff_distinct8 {l : List Nat} : Distinct3 l ↔ Distinct8 l := by
  exact distinct3_iff_distinct4.trans distinct4_iff_distinct8

theorem distinct0_iff_distinct3 {l : List Nat} : Distinct0 l ↔ Distinct3 l := by
  constructor
  · intro h x y hx hy hxy
    apply h x y hx hy
    simpa [List.getElem!_eq_getElem?_getD, hx, hy] using hxy
  · intro h x y hx hy hxy
    apply h x y hx hy
    simpa [List.getElem!_eq_getElem?_getD, hx, hy] using hxy

theorem distinct1_iff_distinct3 {l : List Nat} : Distinct1 l ↔ Distinct3 l := by
  constructor
  · intro h x y hx hy hxy
    exact h x y hxy (getElemOption_ne_none_iff_lt.mpr hx)
  · intro h x y hxy hxNone
    have hx : x < l.length := getElemOption_ne_none_iff_lt.mp hxNone
    have hy : y < l.length := getElemOption_ne_none_iff_lt.mp (by rwa [← hxy])
    exact h x y hx hy hxy

theorem distinct2_iff_distinct4 {l : List Nat} : Distinct2 l ↔ Distinct4 l := by
  constructor
  · intro h x y hx hy hxy
    exact h x y hxy (getElemOption_ne_none_iff_lt.mpr hx)
  · intro h x y hxy hxNone
    intro hxyEq
    have hx : x < l.length := getElemOption_ne_none_iff_lt.mp hxNone
    have hy : y < l.length := getElemOption_ne_none_iff_lt.mp (by rwa [← hxyEq])
    exact h x y hx hy hxy hxyEq

theorem distinct5_iff_distinct3 {l : List Nat} : Distinct5 l ↔ Distinct3 l := by
  exact distinct5_iff_distinct8.trans distinct3_iff_distinct8.symm

theorem distinct6_iff_distinct5 {l : List Nat} : Distinct6 l ↔ Distinct5 l := by
  constructor
  · intro h a
    rcases h a with h0 | h1
    · simp [h0]
    · simp [h1]
  · intro h a
    have ha : l.count a ≤ 1 := h a
    rcases Nat.eq_zero_or_pos (l.count a) with h0 | hpos
    · exact Or.inl h0
    · exact Or.inr (Nat.le_antisymm ha (Nat.succ_le_of_lt hpos))

theorem distinct7_iff_distinct5 {l : List Nat} : Distinct7 l ↔ Distinct5 l := by
  constructor
  · intro h a
    rw [count_eq_filter_length]
    exact h a
  · intro h a
    rw [← count_eq_filter_length]
    exact h a
