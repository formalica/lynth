import Scripts.Test.Equiv.List.Find

/-!
# Proofs: `List.find?` alternatives are equal to the original

`viaFilterHead` is free: `List.head?_filter` states exactly that the head of the
filtered list is the found element.  `byRec` and `byRevFoldl` are proved here.
`viaGetElemScan` is **attempted but not finished**; the module header records
where it stalls.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.find

universe u

variable {α : Type u}

/-! ## `viaFilterHead` -/

/-- `List.head?_filter` is the statement. -/
theorem viaFilterHead_eq_find? (p : α → Bool) (l : List α) :
    viaFilterHead p l = List.find? p l :=
  List.head?_filter

/-! ## `byRec` -/

/-- The recursion written out, against `List.find?_cons`.  The `Bool` test has to
be split on before the equation reduces, because `List.find?_cons` is stated as
a `match` while the alternative writes `if p a then`. -/
private theorem rec_find? : ∀ (p : α → Bool) (l : List α), byRec p l = List.find? p l := by
  intro p l
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hba : p a with
    | true => simp [byRec, hba]
    | false => simp [byRec, hba, ih]

theorem byRec_eq_find? (p : α → Bool) (l : List α) : byRec p l = List.find? p l :=
  rec_find? p l

/-! ## `byRevFoldl` -/

/-- Folding the reversed list with a step that *overwrites* on success returns
the leftmost match: the traversal runs right to left, so the value that survives
is the one furthest to the left.  The seed comes back untouched only when nothing
matches. -/
private theorem rev_foldl_find? : ∀ (l : List α) (p : α → Bool) (d : Option α),
    (l.reverse).foldl (fun acc a => if p a then some a else acc) d
      = match List.find? p l with
        | some a => some a
        | none => d := by
  intro l
  induction l with
  | nil =>
    intro p d
    rw [List.reverse_nil, List.foldl_nil, List.find?_nil]
  | cons a t ih =>
    intro p d
    cases hba : p a with
    | true =>
      simp [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, hba]
    | false =>
      simp [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
        hba, ih]

theorem byRevFoldl_eq_find? (p : α → Bool) (l : List α) : byRevFoldl p l = List.find? p l := by
  rw [byRevFoldl, rev_foldl_find?]
  cases h : List.find? p l <;> rfl

/-! ## `viaGetElemScan` -/

private theorem finRange_find? (p : α → Bool) : ∀ (l : List α),
    ((List.finRange l.length).find? (fun i => p (l.get i))).map l.get = List.find? p l := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.length_cons, List.finRange_succ]
    simp only [List.find?_cons, List.find?_map]
    cases h : p ((a :: t).get 0) with
    | true =>
      have hp : p a = true := by simpa using h
      simp [h, hp, List.get_cons_zero]
    | false =>
      have hp : p a = false := by simpa using h
      simp only [h, Bool.false_eq_true, ite_false, hp, Option.map_map]
      have hget : (fun i : Fin t.length => (a :: t).get (Fin.succ i)) = t.get := by
        funext i
        simp [List.get_cons_succ]
      have hget' : (a :: t).get ∘ Fin.succ = t.get := by
        funext i
        exact congrFun hget i
      have hpred :
          (fun i : Fin t.length => p ((a :: t).get (Fin.succ i))) =
            (fun i => p (t.get i)) := by
        funext i
        exact congrArg p (congrFun hget i)
      have hpred' : (fun i : Fin (t.length + 1) => p ((a :: t).get i)) ∘ Fin.succ =
          (fun i => p (t.get i)) := by
        funext i
        exact congrFun hpred i
      rw [hget', hpred', ih]

/-! ## Against the original -/

theorem viaFilterHead_eq_orig (p : α → Bool) (l : List α) :
    viaFilterHead p l = orig p l := viaFilterHead_eq_find? p l

theorem byRec_eq_orig (p : α → Bool) (l : List α) : byRec p l = orig p l := rec_find? p l

theorem byRevFoldl_eq_orig (p : α → Bool) (l : List α) : byRevFoldl p l = orig p l :=
  byRevFoldl_eq_find? p l

/-! ## Outstanding (stated, not proved) -/

/-!
The theorems below are the remaining routes.  Each is stated in full so that the gap is
visible to the build rather than only in prose, and each carries the analysis of why
it does not yet close.  The `sorry` is deliberate and temporary: this section is the
work list.  Every theorem outside it is fully proved.
-/

/-! ### `viaGetElemScan` -/

/-- Outstanding: not proved.  Needs a `Fin`-index characterisation of `find?` over `List.finRange`, plus the
`l[i]` bounds that `List.find?_cons` makes unnecessary. -/
theorem viaGetElemScan_eq_orig (p : α → Bool) (l : List α) : viaGetElemScan p l = orig p l := by
  simpa [viaGetElemScan, orig] using finRange_find? p l

end Alt.List.find
