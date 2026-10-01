import Mathlib.Data.List.Palindrome
import Mathlib.Tactic

def Palindrome0 {α : Type} (l : List α) : Prop :=
  l.reverse = l

def Palindrome1 {α : Type} (l : List α) : Prop :=
  l = l.reverse

def Palindrome2 {α : Type} (l : List α) : Prop :=
  l.Palindrome

def Palindrome3 {α : Type} (l : List α) : Prop :=
  ∀ i : Nat, l[i]? = l.reverse[i]?

def Palindrome4 {α : Type} (l : List α) : Prop :=
  ∀ i : Nat, l.reverse[i]? = l[i]?

def Palindrome5 {α : Type} (l : List α) : Prop :=
  ∀ i j : Nat, i + j + 1 = l.length → l[i]? = l[j]?

def Palindrome6 {α : Type} (l : List α) : Prop :=
  ∀ i j : Nat, i + j + 1 = l.length → l[j]? = l[i]?

def Palindrome7 {α : Type} (l : List α) : Prop :=
  ∀ i : Nat, i < l.length → l[i]? = l.reverse[i]?

def Palindrome8 {α : Type} (l : List α) : Prop :=
  ∀ i : Nat, ∀ hi : i < l.length, l[i] = l.reverse[i]'(by simpa using hi)

def Palindrome9 {α : Type} (l : List α) : Prop :=
  l.reverse.Palindrome

def Palindrome10 {α : Type} (l : List α) : Prop :=
  l.reverse.reverse = l.reverse

private theorem getElemOption_eq_some_getElem {α : Type} {l : List α} {i : Nat}
    (hi : i < l.length) : l[i]? = some l[i] := by
  exact List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩

private theorem option_eq_of_getElem_eq {α : Type} {l : List α} {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) : l[i] = l[j] → l[i]? = l[j]? := by
  intro h
  calc
    l[i]? = some l[i] := getElemOption_eq_some_getElem hi
    _ = some l[j] := by simp [h]
    _ = l[j]? := (getElemOption_eq_some_getElem hj).symm

theorem palindrome0_iff_palindrome1 {α : Type} {l : List α} :
    Palindrome0 l ↔ Palindrome1 l := by
  constructor <;> intro h <;> simpa [Palindrome0, Palindrome1] using h.symm

theorem palindrome1_iff_palindrome2 {α : Type} {l : List α} :
    Palindrome1 l ↔ Palindrome2 l := by
  constructor
  · intro h
    exact List.Palindrome.of_reverse_eq h.symm
  · intro h
    exact h.reverse_eq.symm

theorem palindrome1_iff_palindrome3 {α : Type} {l : List α} :
    Palindrome1 l ↔ Palindrome3 l := by
  constructor
  · intro h i
    rw [Palindrome1] at h
    rw [<-h]
  · intro h
    exact List.ext_getElem? h

theorem palindrome3_iff_palindrome4 {α : Type} {l : List α} :
    Palindrome3 l ↔ Palindrome4 l := by
  constructor
  · intro h i
    exact (h i).symm
  · intro h i
    exact (h i).symm

theorem palindrome3_iff_palindrome5 {α : Type} {l : List α} :
    Palindrome3 l ↔ Palindrome5 l := by
  constructor
  · intro h i j hij
    calc
      l[i]? = l.reverse[i]? := h i
      _ = l[j]? := List.getElem?_reverse' (l := l) (i := i) (j := j) hij
  · intro h i
    by_cases hi : i < l.length
    · let j := l.length - 1 - i
      have hij : i + j + 1 = l.length := by
        dsimp [j]
        omega
      have h1 : l[i]? = l[j]? := h i j hij
      have h2 : l.reverse[i]? = l[j]? := List.getElem?_reverse' (l := l) (i := i) (j := j) hij
      exact h1.trans h2.symm
    · have hiLen : l.length ≤ i := Nat.not_lt.mp hi
      have hNone : l[i]? = none := List.getElem?_eq_none (l := l) (i := i) hiLen
      have hRevLen : l.reverse.length ≤ i := by
        simpa [List.length_reverse] using hiLen
      have hRevNone : l.reverse[i]? = none := List.getElem?_eq_none (l := l.reverse) (i := i) hRevLen
      simpa [hNone, hRevNone]

theorem palindrome5_iff_palindrome6 {α : Type} {l : List α} :
    Palindrome5 l ↔ Palindrome6 l := by
  constructor
  · intro h i j hij
    exact (h i j hij).symm
  · intro h i j hij
    exact (h i j hij).symm

theorem palindrome3_iff_palindrome7 {α : Type} {l : List α} :
    Palindrome3 l ↔ Palindrome7 l := by
  constructor
  · intro h i hi
    exact h i
  · intro h i
    by_cases hi : i < l.length
    · exact h i hi
    · have hiLen : l.length ≤ i := Nat.not_lt.mp hi
      have hNone : l[i]? = none := List.getElem?_eq_none (l := l) (i := i) hiLen
      have hRevLen : l.reverse.length ≤ i := by
        simpa [List.length_reverse] using hiLen
      have hRevNone : l.reverse[i]? = none := List.getElem?_eq_none (l := l.reverse) (i := i) hRevLen
      simpa [hNone, hRevNone]

theorem palindrome7_iff_palindrome8 {α : Type} {l : List α} :
    Palindrome7 l ↔ Palindrome8 l := by
  constructor
  · intro h i hi
    have hiRev : i < l.reverse.length := by
      suffices hlen : l.reverse.length = l.length by rw [hlen]; exact hi
      exact List.length_reverse
    have hOpt : l[i]? = l.reverse[i]? := h i hi
    have hSome : some l[i] = some l.reverse[i] := by
      rw [getElemOption_eq_some_getElem hi, getElemOption_eq_some_getElem hiRev] at hOpt
      exact hOpt
    exact Option.some.inj hSome
  · intro h i hi
    have hiRev : i < l.reverse.length := by
      suffices hlen : l.reverse.length = l.length by rw [hlen]; exact hi
      exact List.length_reverse
    rw [getElemOption_eq_some_getElem hiRev, getElemOption_eq_some_getElem hi]
    exact congr_arg some (h i hi)

theorem palindrome2_iff_palindrome9 {α : Type} {l : List α} :
    Palindrome2 l ↔ Palindrome9 l := by
  constructor
  · intro h
    apply List.Palindrome.of_reverse_eq
    simpa [Palindrome2] using h.reverse_eq.symm
  · intro h
    apply List.Palindrome.of_reverse_eq
    have hEq : l = l.reverse := by
      simpa [Palindrome9] using h.reverse_eq
    exact hEq.symm

theorem palindrome1_iff_palindrome10 {α : Type} {l : List α} :
    Palindrome1 l ↔ Palindrome10 l := by
  constructor
  · intro h
    simpa [Palindrome1, Palindrome10, h]
  · intro h
    simpa [Palindrome10] using h
