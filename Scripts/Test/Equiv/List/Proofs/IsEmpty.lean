import Scripts.Test.Equiv.List.IsEmpty

/-!
# Proofs: `List.isEmpty` alternatives are equal to the original

All seven alternatives in `../IsEmpty.lean` are proved equal to `List.isEmpty`.

The whole file is `cases l`: every one of these is a one-step function, so
`[]` and `_ :: _` are the only two cases and each side reduces in both.  That
makes this the shortest file in the directory, and a good sanity check that the
`Bool`/`Prop` boundary noted in the source docstring really is not a problem —
no `decide` is needed beyond the one `viaLength` already contains.
-/

namespace Alt.List.isEmpty

variable {α : Type u}

/-! ## `direct` -/

theorem direct_eq (l : List α) : direct l = List.isEmpty l := by cases l <;> rfl

/-! ## `viaLength` -/

/-- `decide (l.length = 0)`.  Both sides reduce on the two cases. -/
theorem viaLength_eq (l : List α) : viaLength l = List.isEmpty l := by cases l <;> rfl

/-! ## `viaHead` -/

theorem viaHead_eq (l : List α) : viaHead l = List.isEmpty l := by cases l <;> rfl

/-! ## `viaFilter` -/

/-- Rebuilds the list with a constant-`true` predicate and then asks the same
question of the rebuild.  The source docstring calls this "pointless work, but a
different route", and that is exactly right: the two cases settle it. -/
theorem viaFilter_eq (l : List α) : viaFilter l = List.isEmpty l := by cases l <;> rfl

/-! ## `viaTake` -/

theorem viaTake_eq (l : List α) : viaTake l = List.isEmpty l := by cases l <;> rfl

/-! ## `viaAny` -/

theorem viaAny_eq (l : List α) : viaAny l = List.isEmpty l := by cases l <;> rfl

/-! ## `viaRevRev` -/

/-- Two reversals and then the test; `List.reverse_reverse` identifies the
rebuild with `l`. -/
theorem viaRevRev_eq (l : List α) : viaRevRev l = List.isEmpty l := by
  cases l with
  | nil => rfl
  | cons a t => simp [viaRevRev, List.reverse_reverse]

/-! ## Against the original -/

theorem direct_eq_orig (l : List α) : direct l = orig l := direct_eq l

theorem viaLength_eq_orig (l : List α) : viaLength l = orig l := viaLength_eq l

theorem viaHead_eq_orig (l : List α) : viaHead l = orig l := viaHead_eq l

theorem viaFilter_eq_orig (l : List α) : viaFilter l = orig l := viaFilter_eq l

theorem viaTake_eq_orig (l : List α) : viaTake l = orig l := viaTake_eq l

theorem viaAny_eq_orig (l : List α) : viaAny l = orig l := viaAny_eq l

theorem viaRevRev_eq_orig (l : List α) : viaRevRev l = orig l := viaRevRev_eq l

end Alt.List.isEmpty
