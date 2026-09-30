import Scripts.Test.Equiv.List.Head

/-!
# Proofs: `List.head?` alternatives are equal to the original

All seven alternatives in `../Head.lean` are proved equal to `List.head?`.

Five of them are one-step functions and fall to `cases l`.  The two fold-based
ones need a latch lemma, and both are stated in terms of the *imported*
definition rather than by restating the fold step — for the reason recorded in
`../Proofs/FilterMap.lean`: a `match` written here would compile to a different
private auxiliary and would not unify with the definition's.
-/

namespace Alt.List.head?

variable {α : Type u}

/-! ## One-step alternatives -/

theorem direct_eq (l : List α) : direct l = List.head? l := by cases l <;> rfl

/-- `l[0]?`, which is `none` exactly on `[]`. -/
theorem viaIndex_eq (l : List α) : viaIndex l = List.head? l := by cases l <;> rfl

theorem viaTake_eq (l : List α) : viaTake l = List.head? l := by cases l <;> rfl

theorem viaSpan_eq (l : List α) : viaSpan l = List.head? l := by
  cases l with
  | nil => rfl
  | cons a t => simp [viaSpan]

/-- The head of `l` is the last element of `l.reverse`, so the emptiness test
is inherited from `getLast?` on the reversed list.  `List.getLast?_append`
handles the `(t.reverse ++ [a])` shape. -/
theorem viaRevLast_eq (l : List α) : viaRevLast l = List.head? l := by
  cases l with
  | nil => rfl
  | cons a t => simp [viaRevLast, List.reverse_cons, List.getLast?_append]

/-! ## `viaFoldr` -/

/-- Once the accumulator is `some`, the step is the identity — so
`foldr`/`foldl` over a latch seeded with `some y` is `some y` whatever the list.
Stated via `viaFoldl` so that the step is the imported one.

The outer step is the observation that matters for `viaFoldr`: `foldr` runs
right to left, so on `a :: t` the seed after the head has already been settled
to `some a` by `foldr_append`, and the latch takes over from there. -/
private theorem latch (s : List α) (y : α) : viaFoldl (y :: s) = some y := by
  induction s with
  | nil => rfl
  | cons b u ihu => simp only [viaFoldl, List.foldl_cons]; exact ihu

theorem viaFoldr_eq (l : List α) : viaFoldr l = List.head? l := by
  cases l with
  | nil => rfl
  | cons a t =>
    simp only [viaFoldr, List.reverse_cons, List.foldr_append, List.foldr_cons]
    simpa [viaFoldl, List.foldl_cons] using latch t a

/-! ## `viaFoldl` -/

/-- Left to right this time, so the head is latched first and never replaced.
The nested induction is what makes the auxiliary match harmless: the step in
the induction hypothesis and the step in the goal are the *same term*, because
both come from the unfolded definition rather than from anything written here. -/
theorem viaFoldl_eq (l : List α) : viaFoldl l = List.head? l := by
  cases l with
  | nil => simp [viaFoldl]
  | cons a t =>
    simp only [viaFoldl, List.foldl_cons]
    induction t with
    | nil => rfl
    | cons b u ihu => simp only [List.foldl_cons]; exact ihu

/-! ## Against the original -/

theorem direct_eq_orig (l : List α) : direct l = orig l := direct_eq l

theorem viaIndex_eq_orig (l : List α) : viaIndex l = orig l := viaIndex_eq l

theorem viaTake_eq_orig (l : List α) : viaTake l = orig l := viaTake_eq l

theorem viaSpan_eq_orig (l : List α) : viaSpan l = orig l := viaSpan_eq l

theorem viaRevLast_eq_orig (l : List α) : viaRevLast l = orig l := viaRevLast_eq l

theorem viaFoldr_eq_orig (l : List α) : viaFoldr l = orig l := viaFoldr_eq l

theorem viaFoldl_eq_orig (l : List α) : viaFoldl l = orig l := viaFoldl_eq l

end Alt.List.head?
