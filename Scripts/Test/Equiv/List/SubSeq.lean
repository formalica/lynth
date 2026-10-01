import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic
import Init.Data.List.Nat.Pairwise


/-- Inductive/substructural definition: include or skip elements. -/
def SubSeq0 {α : Type} : List α → List α → Prop :=
  List.Sublist

/-- Boolean-mask definition: there is a bool-list `bs` of the same length as `l2`
    and taking the `true` entries (in order) yields `l1`. -/
def SubSeq1 {α : Type} (l1 l2 : List α) : Prop :=
  ∃ bs : List Bool,
    bs.length = l2.length ∧
    List.filterMap (fun (p : Bool × α) => if p.1 then some p.2 else none) (List.zip bs l2) = l1


/-! Inductive definition: choose to match or skip each head element. -/
inductive SubSeq2 {α : Type} : List α → List α → Prop
| nil : ∀ l, SubSeq2 [] l
| cons {a : α} {as bs : List α} : SubSeq2 as bs → SubSeq2 (a :: as) (a :: bs)
| skip {a : α} {as : List α} {b : α} {bs : List α} : SubSeq2 (a :: as) bs → SubSeq2 (a :: as) (b :: bs)


/-! Index-list definition: there is a strictly increasing list of indices in `l2` whose elements (in order)
    correspond to `l1`. -/
def SubSeq3 {α : Type} (l1 l2 : List α) : Prop :=
  ∃ (is : List Nat),
    is.length = l1.length ∧
    is.Pairwise (· < ·) ∧
    ∀ j : Nat, j < is.length → ∃ k : Nat, is[j]? = some k ∧ l1[j]? = l2[k]?


/-! Function/index mapping definition: there is a strictly monotone (index) map `f` mapping positions
    of `l1` into positions of `l2` and preserving elements. -/
def SubSeq4 {α : Type} (l1 l2 : List α) : Prop :=
  ∃ f : Nat → Nat,
    (∀ i, i < l1.length → f i < l2.length) ∧
    (∀ i j, i < j → f i < f j) ∧
    (∀ i (hi : i < l1.length), l1[i]? = l2[f i]?)


/-! Existence of a boolean mask from an inductive subsequence proof -/

private theorem filterMap_zip_map_false {α : Type} : ∀ (l : List α),
  List.filterMap (fun (p : Bool × α) => if p.1 then some p.2 else none) (List.zip (l.map fun _ => false) l) = []
| [] => by simp
| _ :: tl => by
  dsimp [List.map, List.zip, List.filterMap]
  exact filterMap_zip_map_false tl

theorem SubSeq2.to_SubSeq1 {α : Type} {l1 l2 : List α} (h : SubSeq2 l1 l2) : SubSeq1 l1 l2 := by
  induction h
  case nil l =>
    use l.map (fun _ => false)
    constructor
    · simp
    · exact filterMap_zip_map_false l
  case cons a as bs ih =>
    rcases ih with ⟨bs', hlen', hfilter'⟩
    use true :: bs'
    constructor
    · simp [hlen']
    · simp [hfilter']
  case skip a as b bs ih =>
    rcases ih with ⟨bs', hlen', hfilter'⟩
    use false :: bs'
    constructor
    · simp [hlen']
    · simp [hfilter']

theorem SubSeq1.to_SubSeq2 {α : Type} {l1 l2 : List α} (h : SubSeq1 l1 l2) : SubSeq2 l1 l2 := by
  rcases h with ⟨bs, hlen, hfilter⟩
  induction bs generalizing l1 l2 with
  | nil =>
    cases l2 with
    | nil =>
      cases l1 with
      | nil => exact SubSeq2.nil []
      | cons _ _ => simp at hfilter
    | cons _ _ => simp at hlen
  | cons b bs' ih =>
    cases l2 with
    | nil => simp at hlen
    | cons x xs =>
      have hlen' : bs'.length = xs.length := by simpa using hlen
      cases b
      case false =>
        simp [List.zip] at hfilter
        cases l1 with
        | nil => exact SubSeq2.nil _
        | cons y ys => exact SubSeq2.skip (ih hlen' hfilter)
      case true =>
        cases l1 with
        | nil => simp [List.zip] at hfilter
        | cons y ys =>
          simp [List.zip] at hfilter
          rcases hfilter with ⟨rfl, htail⟩
          exact SubSeq2.cons (ih hlen' htail)


theorem SubSeq1_iff_SubSeq2 {α : Type} (l1 l2 : List α) : SubSeq1 l1 l2 ↔ SubSeq2 l1 l2 := by
  constructor
  · intro h; exact SubSeq1.to_SubSeq2 h
  · intro h; exact SubSeq2.to_SubSeq1 h


/-! (Optional) Equivalence with `List.Sublist` (alias `SubSeq0`) can be added later. -/

/-! Equivalence with `List.Sublist` (alias `SubSeq0`) via boolean-mask `SubSeq1` -/

theorem SubSeq0.to_SubSeq1 {α : Type} {l1 l2 : List α} (h : SubSeq0 l1 l2) : SubSeq1 l1 l2 := by
  induction h with
  | slnil =>
    use []
    constructor <;> simp
  | cons a s ih =>
    rcases ih with ⟨bs, hlen, hfilter⟩
    use false :: bs
    constructor
    · simp [hlen]
    · simp [hfilter]
  | cons_cons a s ih =>
    rcases ih with ⟨bs, hlen, hfilter⟩
    use true :: bs
    constructor
    · simp [hlen]
    · simp [hfilter]

/-! From inductive subsequence to `List.Sublist` -/

theorem SubSeq2.to_SubSeq0 {α : Type} {l1 l2 : List α} (h : SubSeq2 l1 l2) : SubSeq0 l1 l2 := by
  induction h with
  | nil l =>
    induction l with
    | nil => exact List.Sublist.slnil
    | cons a l ih => exact List.Sublist.cons a ih
  | cons h ih =>
    exact List.Sublist.cons_cons _ ih
  | skip h ih =>
    exact List.Sublist.cons _ ih

theorem SubSeq1.to_SubSeq0 {α : Type} {l1 l2 : List α} (h : SubSeq1 l1 l2) : SubSeq0 l1 l2 :=
  SubSeq2.to_SubSeq0 (SubSeq1.to_SubSeq2 h)

theorem SubSeq0_iff_SubSeq2 {α : Type} (l1 l2 : List α) : SubSeq0 l1 l2 ↔ SubSeq2 l1 l2 := by
  constructor
  · intro h; exact SubSeq1.to_SubSeq2 (SubSeq0.to_SubSeq1 h)
  · intro h; exact SubSeq2.to_SubSeq0 h


/-! Equivalence with `SubSeq3` (index-list definition) -/

theorem SubSeq3.to_SubSeq0 {α : Type} {l1 l2 : List α} (h : SubSeq3 l1 l2) : SubSeq0 l1 l2 := by
  classical
  rcases h with ⟨is, hlen, hpair, hcompat⟩
  rw [SubSeq0, List.sublist_iff_exists_fin_orderEmbedding_get_eq]
  let idx : ∀ j : Nat, j < is.length → Nat := fun j hj => Classical.choose (hcompat j hj)
  have hidx : ∀ j hj, is[j]? = some (idx j hj) ∧ l1[j]? = l2[idx j hj]? := by
    intro j hj
    exact Classical.choose_spec (hcompat j hj)
  have hidx_val : ∀ j hj, is.get ⟨j, hj⟩ = idx j hj := by
    intro j hj
    apply Option.some.inj
    calc
      some (is.get ⟨j, hj⟩) = is[j]? := by
        simpa using (List.getElem?_eq_getElem (l := is) (i := j) hj).symm
      _ = some (idx j hj) := (hidx j hj).1
  have hidx_lt : ∀ j hj, idx j hj < l2.length := by
    intro j hj
    have hj1 : j < l1.length := by rw [← hlen]; exact hj
    have hEq : l2[idx j hj]? = some (l1.get ⟨j, hj1⟩) := by
      calc
        l2[idx j hj]? = l1[j]? := by simpa [eq_comm] using (hidx j hj).2
        _ = some (l1.get ⟨j, hj1⟩) := by
          simpa using (List.getElem?_eq_getElem (l := l1) (i := j) hj1)
    exact (List.getElem?_eq_some_iff.mp hEq).choose
  let f : Fin l1.length → Fin l2.length := fun i =>
    have hi : i.1 < is.length := by rw [hlen]; exact i.2
    ⟨idx i.1 hi, hidx_lt i.1 hi⟩
  refine ⟨OrderEmbedding.ofStrictMono f ?_, ?_⟩
  · intro i j hij
    have hi : i.1 < is.length := by rw [hlen]; exact i.2
    have hj : j.1 < is.length := by rw [hlen]; exact j.2
    have hij' : (⟨i.1, hi⟩ : Fin is.length) < ⟨j.1, hj⟩ := by
      exact Fin.lt_def.mpr (Fin.lt_def.mp hij)
    have hpair' : is.get ⟨i.1, hi⟩ < is.get ⟨j.1, hj⟩ :=
      (List.pairwise_iff_get.mp hpair) ⟨i.1, hi⟩ ⟨j.1, hj⟩ hij'
    rw [hidx_val i.1 hi, hidx_val j.1 hj] at hpair'
    change idx i.1 hi < idx j.1 hj
    exact hpair'
  · intro i
    have hi : i.1 < is.length := by rw [hlen]; exact i.2
    have hEq := (hidx i.1 hi).2
    have hLeft : l1[i.1]? = some (l1.get i) := by
      simpa using (List.getElem?_eq_getElem (l := l1) (i := i.1) i.2)
    have hRight : l2[idx i.1 hi]? = some (l2.get (f i)) := by
      simpa [f, hi] using (List.getElem?_eq_getElem (l := l2) (i := idx i.1 hi) (hidx_lt i.1 hi))
    apply Option.some.inj
    calc
      some (l1.get i) = l1[i.1]? := by simpa using hLeft.symm
      _ = l2[idx i.1 hi]? := hEq
      _ = some (l2.get (f i)) := hRight

theorem SubSeq0.to_SubSeq3 {α : Type} {l1 l2 : List α} (h : SubSeq0 l1 l2) : SubSeq3 l1 l2 := by
  rw [SubSeq0, List.sublist_iff_exists_fin_orderEmbedding_get_eq] at h
  rcases h with ⟨f, hf⟩
  use List.ofFn (fun i : Fin l1.length => (f i).1)
  have hlen : (List.ofFn (fun i : Fin l1.length => (f i).1)).length = l1.length := List.length_ofFn
  constructor
  · exact hlen
  constructor
  · rw [List.pairwise_iff_get]
    intro i j hij
    have hi : i.1 < l1.length := by simpa [hlen] using i.2
    have hj : j.1 < l1.length := by simpa [hlen] using j.2
    have hij' : (⟨i.1, hi⟩ : Fin l1.length) < ⟨j.1, hj⟩ := by
      exact Fin.lt_def.mpr (Fin.lt_def.mp hij)
    have hmono := f.strictMono hij'
    simp only [List.get_ofFn]
    exact (Fin.lt_def.mp hmono)
  · intro j hj
    have hj' : j < l1.length := by simpa [hlen] using hj
    use (f ⟨j, hj'⟩).1
    have h1 : (List.ofFn (fun i : Fin l1.length => (f i).1))[j]? = some (f ⟨j, hj'⟩).1 := by
      rw [List.getElem?_eq_getElem hj]
      simp [List.getElem_ofFn]
    have h2 : l1[j]? = l2[(f ⟨j, hj'⟩).1]? := by
      rw [show l1[j]? = (l1.get ⟨j, hj'⟩) by simp]
      rw [hf]
      simp [(f ⟨j, hj'⟩).2]
    exact ⟨h1, h2⟩

theorem SubSeq0_iff_SubSeq3 {α : Type} (l1 l2 : List α) : SubSeq0 l1 l2 ↔ SubSeq3 l1 l2 := by
  constructor
  · intro h; exact SubSeq0.to_SubSeq3 h
  · intro h; exact SubSeq3.to_SubSeq0 h


/-! Equivalence with `SubSeq4` (function/index mapping definition) -/

theorem SubSeq4.to_SubSeq3 {α : Type} {l1 l2 : List α} (h : SubSeq4 l1 l2) : SubSeq3 l1 l2 := by
  rcases h with ⟨f, hbound, hmono, hcompat⟩
  refine ⟨List.ofFn (fun i : Fin l1.length => f i.1), List.length_ofFn, ?_, ?_⟩
  · rw [List.pairwise_iff_get]
    intro i j hij
    simp only [List.get_ofFn]
    exact hmono i.1 j.1 (Fin.lt_def.mp hij)
  · intro j hj
    have hj' : j < l1.length := by simpa [List.length_ofFn] using hj
    exact ⟨f j,
      by rw [List.getElem?_eq_getElem hj]; simp [List.getElem_ofFn],
      hcompat j hj'⟩

private theorem is_lt_of_SubSeq3_compat {α : Type} {l1 l2 : List α}
    {is : List Nat} (hlen : is.length = l1.length)
    (hcompat : ∀ j, j < is.length → ∃ k, is[j]? = some k ∧ l1[j]? = l2[k]?)
    (i : Nat) (hi : i < l1.length) : is[i]'(hlen ▸ hi) < l2.length := by
  have hi' : i < is.length := hlen ▸ hi
  rcases hcompat i hi' with ⟨k, hk1, hk2⟩
  have hki : is[i]'hi' = k := by
    have h1 := List.getElem?_eq_getElem (l := is) (i := i) hi'
    rw [h1] at hk1
    exact Option.some.inj hk1
  have hEq : l2[k]? = some (l1[i]'hi) := by rw [← hk2]; exact List.getElem?_eq_getElem hi
  rw [hki]; exact (List.getElem?_eq_some_iff.mp hEq).choose

theorem SubSeq3.to_SubSeq4 {α : Type} {l1 l2 : List α} (h : SubSeq3 l1 l2) : SubSeq4 l1 l2 := by
  rcases h with ⟨is, hlen, hpair, hcompat⟩
  -- For i < l1.length use is[i]; otherwise use l2.length + i (keeps strict monotonicity)
  refine ⟨fun i => if hi : i < l1.length then is[i]'(hlen ▸ hi) else l2.length + i, ?_, ?_, ?_⟩
  · -- in-bounds
    intro i hi
    simp only [dif_pos hi]
    exact is_lt_of_SubSeq3_compat hlen hcompat i hi
  · -- strict monotonicity on all ℕ
    intro i j hij
    by_cases hi : i < l1.length
    · simp only [dif_pos hi]
      by_cases hj : j < l1.length
      · simp only [dif_pos hj]
        have hi' : i < is.length := hlen ▸ hi
        have hj' : j < is.length := hlen ▸ hj
        exact (List.pairwise_iff_get.mp hpair) ⟨i, hi'⟩ ⟨j, hj'⟩ (Fin.mk_lt_mk.mpr hij)
      · simp only [dif_neg hj]
        have hlt := is_lt_of_SubSeq3_compat hlen hcompat i hi
        have hge : l1.length ≤ j := Nat.le_of_not_lt hj
        omega
    · simp only [dif_neg hi]
      have hge : l1.length ≤ i := Nat.le_of_not_lt hi
      have hj_not : ¬ j < l1.length := by omega
      simp only [dif_neg hj_not]
      omega
  · -- element correspondence
    intro i hi
    simp only [dif_pos hi]
    have hi' : i < is.length := hlen ▸ hi
    rcases hcompat i hi' with ⟨k, hk1, hk2⟩
    have hki : is[i]'hi' = k := by
      have h1 := List.getElem?_eq_getElem (l := is) (i := i) hi'
      rw [h1] at hk1
      exact Option.some.inj hk1
    rw [hki]; exact hk2

theorem SubSeq3_iff_SubSeq4 {α : Type} (l1 l2 : List α) : SubSeq3 l1 l2 ↔ SubSeq4 l1 l2 :=
  ⟨SubSeq3.to_SubSeq4, SubSeq4.to_SubSeq3⟩

theorem SubSeq0_iff_SubSeq4 {α : Type} (l1 l2 : List α) : SubSeq0 l1 l2 ↔ SubSeq4 l1 l2 :=
  (SubSeq0_iff_SubSeq3 l1 l2).trans (SubSeq3_iff_SubSeq4 l1 l2)
