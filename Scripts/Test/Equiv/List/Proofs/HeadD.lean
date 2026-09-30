import Scripts.Test.Equiv.List.HeadD

/-!
# Proofs: `List.headD` alternatives are equal to the original

All four alternatives in `../HeadD.lean` are proved equal to `List.headD` here.

`byGetD` is the free one: `List.headD_eq_getD` says exactly that.  `byRec` and
`byFoldr` are `rfl` on both cases.  `byRevFoldl` needs a helper saying that
folding over the reversed list with an "overwrite" step is the same as folding
over the list itself with a "shadow" step.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.headD

universe u

variable {α : Type u}

/-! ## `byGetD` -/

/-- `List.headD_eq_getD` is exactly the statement, modulo the direction. -/
theorem byGetD_eq_headD (l : List α) (d : α) : byGetD l d = List.headD l d :=
  (List.headD_eq_getD (l := l) (fallback := d)).symm

/-! ## `byGetElemD` -/

theorem byGetElemD_eq_headD (l : List α) (d : α) : byGetElemD l d = List.headD l d := by
  induction l with
  | nil => rfl
  | cons a t ih => rfl

/-! ## `byFoldr` -/

theorem byFoldr_eq_headD (l : List α) (d : α) : byFoldr l d = List.headD l d := by
  induction l with
  | nil => rfl
  | cons a t ih => rfl

/-! ## `byRevFoldl` -/

/-- Folding the reversed list with a step that overwrites the accumulator is the
same as folding the list with a step that ignores it: both return the first
element of the original list, or the seed.  The cons case is where the two
directions meet — after `List.reverse_cons` the seed has been overwritten
exactly once, and `foldl` over a singleton is the step itself. -/
private theorem rev_foldl_eq_foldr : ∀ (l : List α) (d : α),
    (l.reverse).foldl (fun _ a => a) d = List.foldr (fun a _ => a) d l := by
  intro l
  induction l with
  | nil => intro d; rfl
  | cons a t ih =>
    intro d
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldr_cons]

theorem byRevFoldl_eq_headD (l : List α) (d : α) : byRevFoldl l d = List.headD l d := by
  rw [byRevFoldl, rev_foldl_eq_foldr]
  exact byFoldr_eq_headD l d

/-! ## Against the original -/

theorem byGetD_eq_orig (l : List α) (d : α) : byGetD l d = orig l d := byGetD_eq_headD l d

theorem byGetElemD_eq_orig (l : List α) (d : α) : byGetElemD l d = orig l d :=
  byGetElemD_eq_headD l d

theorem byFoldr_eq_orig (l : List α) (d : α) : byFoldr l d = orig l d := byFoldr_eq_headD l d

theorem byRevFoldl_eq_orig (l : List α) (d : α) : byRevFoldl l d = orig l d :=
  byRevFoldl_eq_headD l d

end Alt.List.headD
