import Scripts.Test.Equiv.List.InsertIdx

/-!
# Proofs: `List.insertIdx` alternatives are equal to the original

All four routes (`byRec`, `viaTakeDrop`, `byCounter`, and `byFinRangeMap`) are
proved equal to `List.insertIdx`.

The key that unlocks the file: `List.insertIdx l i a` is *defined* as
`l.modifyTailIdx i (List.cons a)`, and `List.modifyTailIdx.go` — the function the
latter reduces to — has all three of its equations exposed as `@[backward_defeq]`
`Eq.refl`s.  So unlike `List.splitAt` or `List.findIdx`, this whole family is
reducible:

    modifyTailIdx.go f 0      l    = f l
    modifyTailIdx.go f (n+1)  []   = []
    modifyTailIdx.go f (n+1)  (a::t) = a :: modifyTailIdx.go f n t

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.insertIdx

universe u

variable {α : Type u}

/-! ## A shared helper -/

/- `modifyTailIdx` applied to any function is "cut, apply, paste".  The bound `i ≤ l.length`
is not decoration: with `l = []` and `i > 0` the left side is `[]` while the right
side would be `f []`, so the statement is false off the range.  With the bound
restored the proof is straight induction on the index. -/
private theorem go_take_drop : ∀ (f : List α → List α) (i : ℕ) (l : List α), i ≤ l.length →
    List.modifyTailIdx.go f i l = List.take i l ++ f (List.drop i l) := by
  intro f i
  induction i with
  | zero =>
    intro l _
    simp [List.modifyTailIdx.go.eq_1, List.take_zero, List.drop_zero]
  | succ n ih =>
    intro l h
    cases l with
    | nil => simp at h
    | cons b t =>
      have h' : n ≤ t.length := by simp at h; omega
      rw [List.modifyTailIdx.go.eq_3, List.take_succ_cons, List.drop_succ_cons, ih t h',
        List.cons_append]

/-- Past the end of the list `modifyTailIdx` does nothing — the trap recorded in
the definition file's header. -/
private theorem go_eq_self : ∀ (f : List α → List α) (i : ℕ) (l : List α), l.length < i →
    List.modifyTailIdx.go f i l = l := by
  intro f i
  induction i with
  | zero => intro l h; omega
  | succ n ih =>
    intro l h
    cases l with
    | nil => simp [List.modifyTailIdx.go.eq_2]
    | cons b t =>
      simp [List.modifyTailIdx.go.eq_3, ih t (by simp at h; omega)]

/-- `List.insertIdx` reduced to the loop it compiles to. -/
private theorem insertIdx_eq_go (l : List α) (i : ℕ) (a : α) :
    List.insertIdx l i a = List.modifyTailIdx.go (fun t => a :: t) i l := by
  simp only [List.insertIdx, List.modifyTailIdx.eq_1]

/-! ## `byRec` -/

/-- `byRec` *is* the loop, with the function argument specialised to `cons a`.
Both sides then reduce by the same three equations, so the proof is induction
with nothing to re-establish. -/
private theorem rec_insertIdx : ∀ (l : List α) (i : ℕ) (a : α),
    byRec l i a = List.insertIdx l i a := by
  intro l
  induction l with
  | nil =>
    intro i a
    cases i with
    | zero => simp [byRec, insertIdx_eq_go, List.modifyTailIdx.go.eq_1]
    | succ n => simp [byRec, insertIdx_eq_go, List.modifyTailIdx.go.eq_2]
  | cons b t ih =>
    intro i a
    cases i with
    | zero => simp [byRec, insertIdx_eq_go, List.modifyTailIdx.go.eq_1]
    | succ n =>
      simp [byRec, insertIdx_eq_go, List.modifyTailIdx.go.eq_3, ih]

theorem byRec_eq_insertIdx (l : List α) (i : ℕ) (a : α) : byRec l i a = List.insertIdx l i a :=
  rec_insertIdx l i a

/-! ## `viaTakeDrop` -/

theorem viaTakeDrop_eq_insertIdx (l : List α) (i : ℕ) (a : α) :
    viaTakeDrop l i a = List.insertIdx l i a := by
  cases l with
  | nil =>
    cases i with
    | zero => simp [viaTakeDrop, insertIdx_eq_go, List.modifyTailIdx.go.eq_1]
    | succ n => simp [viaTakeDrop, insertIdx_eq_go, List.modifyTailIdx.go.eq_2]
  | cons b t =>
    by_cases h : i ≤ (b :: t).length
    · rw [viaTakeDrop, ite_eq_left h, insertIdx_eq_go,
        go_take_drop (f := fun x => a :: x) (i := i) (l := b :: t) h]
    · rw [viaTakeDrop, ite_eq_right h, insertIdx_eq_go,
        go_eq_self (fun x => a :: x) i (b :: t) (by simpa using h)]

/-! ## `byCounter` -/

private theorem range_takeWhile_lt_len : ∀ (n i : ℕ),
    ((List.range n).takeWhile (fun j => j < i)).length = min n i := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ n ih =>
    intro i
    cases i with
    | zero => simp
    | succ i =>
      rw [List.range_succ_eq_map]
      simp only [List.takeWhile_cons]
      simp [List.takeWhile_map, Function.comp_def, ih]

/- The counter value is `min i (l.length + 1)`.  The range/takeWhile length
lemma makes the in-range and past-the-end cases explicit. -/

/-! ## `byFinRangeMap` -/

private theorem map_val_finRange (n : ℕ) :
    (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast, List.getElem_range]

private theorem do_val_finRange (n : ℕ) :
    (do let j ← List.finRange n; pure j.val) = List.range n := by
  change List.flatMap (fun j : Fin n => [j.val]) (List.finRange n) = List.range n
  rw [← List.map_eq_flatMap]
  exact map_val_finRange n

private theorem finRangeMap_insertIdx (l : List α) (i : ℕ) (a : α)
    (hi : i ≤ l.length) :
    (List.range (l.length + 1)).map
      (fun j : ℕ => if j < i then l.getD j a else if j = i then a else l.getD (j - 1) a) =
        List.insertIdx l i a := by
  apply List.ext_getElem
  · simp [List.length_map, List.length_insertIdx, hi]
  · intro j hj₁ hj₂
    have hjLen : j < l.length + 1 := by
      simpa [List.length_map, List.length_finRange] using hj₁
    simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast]
    rw [List.getElem_insertIdx]
    by_cases hji : j < i
    · have hjBound : j < l.length := Nat.lt_of_lt_of_le hji hi
      simp [hji, hjBound]
    · by_cases hEq : j = i
      · subst j
        simp
      · have hij : i < j := by omega
        have hjSub : j - 1 < l.length := by omega
        simp [hji, hEq, hjSub]

/- The natural-valued view of `finRange` is `range`; extensionality then handles
the before, at, and after insertion indices. -/

/-! ## Against the original -/

theorem byRec_eq_orig (l : List α) (i : ℕ) (a : α) : byRec l i a = orig l i a := rec_insertIdx l i a

theorem viaTakeDrop_eq_orig (l : List α) (i : ℕ) (a : α) :
    viaTakeDrop l i a = orig l i a := viaTakeDrop_eq_insertIdx l i a

/-! ## Against the original -/

/-!
The two remaining alternatives are proved below using the same `modifyTailIdx`
characterization as the recursive implementation.
-/

/-! ### `byCounter` -/

/-- The range prefix length is `min i (l.length + 1)`, reducing the proof to
the `viaTakeDrop` characterization. -/
theorem byCounter_eq_orig (l : List α) (i : ℕ) (a : α) : byCounter l i a = orig l i a := by
  rw [orig]
  dsimp only [byCounter]
  have hk : ((List.range (l.length + 1)).takeWhile (fun j => j < i)).length =
      min (l.length + 1) i := range_takeWhile_lt_len _ _
  rw [hk]
  by_cases h : i ≤ l.length
  · have hmin : min (l.length + 1) i = i := Nat.min_eq_right (by omega)
    rw [hmin]
    simp only [if_pos (by omega : i < l.length + 1)]
    calc
      List.take i l ++ a :: List.drop i l = viaTakeDrop l i a := by simp [viaTakeDrop, h]
      _ = List.insertIdx l i a := viaTakeDrop_eq_insertIdx l i a
  · have hmin : min (l.length + 1) i = l.length + 1 := Nat.min_eq_left (by omega)
    rw [hmin, if_neg (by omega : ¬ l.length + 1 < l.length + 1)]
    rw [insertIdx_eq_go]
    symm
    exact go_eq_self (fun t => a :: t) i l (by omega)

/-! ### `byFinRangeMap` -/

/-- Each enumerated natural index selects the corresponding insertion branch. -/
theorem byFinRangeMap_eq_orig (l : List α) (i : ℕ) (a : α) :
    byFinRangeMap l i a = orig l i a := by
  unfold byFinRangeMap orig
  by_cases hi : i ≤ l.length
  · simp only [if_pos hi]
    rw [do_val_finRange]
    exact finRangeMap_insertIdx l i a hi
  · simp only [if_neg hi]
    symm
    rw [insertIdx_eq_go]
    exact go_eq_self (fun t => a :: t) i l (by omega)

end Alt.List.insertIdx
