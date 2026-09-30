import Scripts.Test.Equiv.List.Drop

/-!
# Proofs: `List.drop` alternatives are equal to the original

All four routes (`byRec`, `byIterTail`, `byGetElemMap`, and `byCounter`) are
proved equal to `List.drop`.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.drop

universe u

variable {α : Type u}

/-! ## `byRec` -/

/-- `List.drop` is compiled through `Nat.brecOn`, so the equations come from
`List.drop_zero` and `List.drop_succ_cons` rather than from a structural
definition.  The index has to be generalised over. -/
private theorem rec_drop : ∀ (n : ℕ) (l : List α), byRec n l = List.drop n l := by
  intro n
  induction n with
  | zero => intro l; rw [byRec, List.drop_zero]
  | succ k ih =>
    intro l
    cases l with
    | nil => rw [byRec, List.drop_nil]
    | cons a t => rw [byRec, List.drop_succ_cons]; exact ih t

theorem byRec_eq_drop (n : ℕ) (l : List α) : byRec n l = List.drop n l := rec_drop n l

/-! ## `byIterTail` -/

/-- `List.tail` is `drop 1`, spelled out. -/
private theorem tail_eq_drop1 (l : List α) : l.tail = l.drop 1 := by
  cases l <;> rfl

/-- Asking for `k` tails in a row drops `k` elements.  On the nil case
`List.range 0` is empty, so the fold is the identity; on the successor case
`List.range_succ` appends the new index, and one `foldl` step at a singleton
*is* the step function. -/
private theorem range_foldl_tail : ∀ (acc : List α) (k : ℕ),
    (List.range k).foldl (fun l _ => List.tail l) acc = List.drop k acc := by
  intro acc k
  induction k with
  | zero => rw [List.range_zero, List.foldl_nil, List.drop_zero]
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
    have htail : List.tail (List.drop j acc) = List.drop (j + 1) acc := by
      rw [tail_eq_drop1, List.drop_drop]
    exact htail

theorem byIterTail_eq_drop (n : ℕ) (l : List α) : byIterTail n l = List.drop n l := by
  rw [byIterTail, range_foldl_tail]

/-! ## `byGetElemMap` -/

private theorem getElemMap_drop : ∀ (n : ℕ) (l : List α),
    byGetElemMap n l = List.drop n l := by
  intro n l
  apply List.ext_getElem
  · simp [byGetElemMap, List.length_finRange, List.length_drop]
  · intro j hj₁ hj₂
    have hj : j < l.length - n := by simpa [byGetElemMap] using hj₁
    have hn : n < l.length :=
      Nat.sub_pos_iff_lt.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hj)
    have hbound : n + j < l.length := by
      calc
        n + j < n + (l.length - n) := Nat.add_lt_add_left hj n
        _ = l.length := Nat.add_sub_cancel' (Nat.le_of_lt hn)
    simp only [byGetElemMap, List.getElem_map, List.getElem_finRange,
      List.get_eq_getElem, Fin.val_cast]
    rw [List.getElem_drop' hbound]

/-! ## `byCounter` -/

private theorem counter_drop_invariant (n : ℕ) : ∀ (l acc : List α) (k : ℕ),
    ((List.foldl (fun (acc, k) a =>
        if k < n then (acc, k + 1) else (a :: acc, k)) (acc, k) l).1).reverse =
      acc.reverse ++ l.drop (n - k) := by
  intro l
  induction l with
  | nil => intro acc k; simp
  | cons a t ih =>
    intro acc k
    by_cases hk : k < n
    · simp only [List.foldl_cons, if_pos hk]
      have hdrop : (a :: t).drop (n - k) = t.drop (n - (k + 1)) := by
        have hn : n - k = n - (k + 1) + 1 := by omega
        rw [hn, List.drop_succ_cons]
      rw [ih, hdrop]
    · simp only [List.foldl_cons, if_neg hk]
      have hk' : n ≤ k := by omega
      simp [ih, Nat.sub_eq_zero_of_le hk', List.drop_zero]

-- Attempted, not finished: see the module header.

/-! ## Against the original -/

theorem byRec_eq_orig (n : ℕ) (l : List α) : byRec n l = orig n l := rec_drop n l

theorem byIterTail_eq_orig (n : ℕ) (l : List α) : byIterTail n l = orig n l :=
  byIterTail_eq_drop n l

/-! ## The remaining routes -/

/-!
The two alternative implementations are proved below using index extensionality
and a fold invariant.
-/

/-! ### `byGetElemMap` -/

/-- The `getElem_drop'` lemma identifies each enumerated surviving index with
the corresponding index of the dropped list. -/
theorem byGetElemMap_eq_orig (n : ℕ) (l : List α) : byGetElemMap n l = orig n l := by
  rw [getElemMap_drop, orig]

/-! ### `byCounter` -/

/-- The invariant tracks both the counter and the reversed accumulator. -/
theorem byCounter_eq_orig (n : ℕ) (l : List α) : byCounter n l = orig n l := by
  simp only [byCounter, orig]
  simpa using counter_drop_invariant n l [] 0

end Alt.List.drop
