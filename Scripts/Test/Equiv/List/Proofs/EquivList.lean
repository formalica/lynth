import Scripts.Test.Equiv.List.EquivList

/-!
# Proofs: every route in `../EquivList.lean` is the identity

All twenty-seven routes in `../EquivList.lean` are proved here.  Each is an
alternative route from `l : List α` back to `l`, doing redundant work first, so
each theorem has the shape

```lean
theorem viaFoo_eq_id (l : List α) : viaFoo l = l
```

Note the naming: these files have no `orig`, because they never reference a
Mathlib function as the definition — they *are* the claim.  The reference point is
the identity `fun l => l`, so `_eq_id` is the right suffix rather than `_eq_orig`.

## What the proofs actually needed

Most routes are discharged by a single library lemma, and the interesting content
is in *which* lemma:

* `viaAppendNil`, `viaDropZero`, `viaMapId`, `viaRevRev` are all `simp`;
* `viaTakeLength` and `viaTakeAppend` go through `List.take_length`;
* `viaSpanAllTrue`, `viaSpanAllFalse`, `viaPartitionT`, `viaPartitionF` and the two
  `viaSplitAt*` are `simp`, because `List.span_eq_takeWhile_dropWhile` and the
  `partition`/`splitAt` characterisations are already simp lemmas;
* `viaFoldrHead` and `viaRevFoldl` need induction, because there is no lemma for
  "`foldr` consing onto the accumulator" or for "reverse then `foldl` back on".

## Two traps worth recording

**Group E cannot be inducted on directly.**  `List.filter_cons` splits
`(a :: t).filter p` into `if p a then a :: t.filter p else t.filter p` — note the
tail keeps the *original* predicate `p`.  So for `p = fun x => x ∈ l` the tail is
filtered by `x ∈ a :: t` while the induction hypothesis is about `x ∈ t`, and the
two never meet.  The fix is `filter_mem_of_mem`, which takes the ambient list
`sub` as a separate parameter and carries `∀ x ∈ l, x ∈ sub`.

**`filterMap` needs the `Prop` form, not the `Bool` form.**  `filterMap_if_some`
has to be stated with `q : α → Prop` and a `DecidablePred`.  Stated with
`q : α → Bool` it does not match the definitions, because the definitions write
`if x ∈ sub then ...` — an `ite` on a `Prop` — whereas `if q x then ...` with a
`Bool` is an `ite` on `q x = true`, and `x ∈ sub` and `decide (x ∈ sub) = true` are
propositionally but *not* definitionally equal.

No `sorry`, no `axiom`, no `native_decide`, no `Classical`.
-/

namespace Equiv
namespace List

variable {α : Type u}

universe u

/-! ## Group A -/

open _root_.List in
/-- Append nothing. -/
theorem viaAppendNil_eq_id (l : List α) : viaAppendNil l = l := by
  simp [viaAppendNil]

/-- Drop nothing. -/
theorem viaDropZero_eq_id (l : List α) : viaDropZero l = l := by
  simp [viaDropZero]

/-- Apply the identity function to every element. -/
theorem viaMapId_eq_id (l : List α) : viaMapId l = l := by
  simp [viaMapId]

/-- Take the whole list. -/
theorem viaTakeLength_eq_id (l : List α) : viaTakeLength l = l := by
  simp [viaTakeLength]

/-- Keep everything: a constant `Bool` test. -/
theorem viaFilterTrue_eq_id (l : List α) : viaFilterTrue l = l := by
  simp [viaFilterTrue]

/-- `filterMap` keeping every `some`. -/
theorem viaFilterMapSome_eq_id (l : List α) : viaFilterMapSome l = l := by
  simp [viaFilterMapSome]

/-- `flatMap` with the singleton function. -/
theorem viaFlatMapSing_eq_id (l : List α) : viaFlatMapSing l = l := by
  simp [viaFlatMapSing]

/-- Reverse twice. -/
theorem viaRevRev_eq_id (l : List α) : viaRevRev l = l := by
  simp [viaRevRev]

/-- Compose `map id` with itself. -/
theorem viaMapIdTwice_eq_id (l : List α) : viaMapIdTwice l = l := by
  simp [viaMapIdTwice]

/-! ## Group B -/

open _root_.List in
/-- `foldl` with a left-absorbing step, seeded with the list itself. -/
theorem viaFoldlSeed_eq_id (l : List α) : viaFoldlSeed l = l := by
  simp [viaFoldlSeed]

/-- The `foldr` counterpart, seeded with the list. -/
theorem viaFoldrSeed_eq_id (l : List α) : viaFoldrSeed l = l := by
  simp [viaFoldrSeed]

/-- `foldr` consing every element onto the accumulator. -/
theorem viaFoldrHead_eq_id : ∀ (l : List α), viaFoldrHead l = l := by
  intro l
  induction l with
  | nil => rfl
  | cons a t _ => simp [viaFoldrHead]

/-- Reverse, then `foldl` the elements back on. -/
theorem viaRevFoldl_eq_id : ∀ (l : List α), viaRevFoldl l = l := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp [viaRevFoldl, List.reverse_cons, List.foldl_append, List.foldl_cons,
      List.foldl_nil]

/-! ## Group C -/

/-- `span` with an always-true predicate, keeping the first component. -/
theorem viaSpanAllTrue_eq_id (l : List α) : viaSpanAllTrue l = l := by
  simp [viaSpanAllTrue, List.span_eq_takeWhile_dropWhile]

/-- `span` with an always-false predicate, keeping the second component. -/
theorem viaSpanAllFalse_eq_id (l : List α) : viaSpanAllFalse l = l := by
  simp [viaSpanAllFalse, List.span_eq_takeWhile_dropWhile]

/-- `partition` with an always-true predicate, keeping the "true" half. -/
theorem viaPartitionT_eq_id (l : List α) : viaPartitionT l = l := by
  simp [viaPartitionT]

/-- `partition` with an always-false predicate, keeping the "false" half. -/
theorem viaPartitionF_eq_id (l : List α) : viaPartitionF l = l := by
  simp [viaPartitionF]

/-- `splitAt` the full length, keeping the prefix. -/
theorem viaSplitAtLen_eq_id (l : List α) : viaSplitAtLen l = l := by
  simp [viaSplitAtLen]

/-- `splitAt` zero, keeping the suffix. -/
theorem viaSplitAtZero_eq_id (l : List α) : viaSplitAtZero l = l := by
  simp [viaSplitAtZero]

open _root_.List in
/-- `zipIdx` the list with `range`, then project the list component back out. -/
theorem viaZipIdxMapFst_eq_id : ∀ (l : List α), viaZipIdxMapFst l = l := by
  intro l
  induction l with
  | nil => rfl
  | cons a t _ => simp [viaZipIdxMapFst]

/-- Duplicate the list, then take the first half. -/
theorem viaTakeAppend_eq_id (l : List α) : viaTakeAppend l = l := by
  simp [viaTakeAppend]

/-! ## Group D -/

/-- Cons a head, then drop it again. -/
theorem viaConsDrop1_eq_id (a : α) (l : List α) : viaConsDrop1 a l = l := by
  simp [viaConsDrop1]

/-- Cons a head, drop it, then take the whole remainder. -/
theorem viaConsTake_eq_id (a : α) (l : List α) : viaConsTake a l = l := by
  simp [viaConsTake]

/-! ## Group E -/

/-- Filtering a list by membership in a *superset* keeps everything.  The
superset has to be a parameter: `List.filter_cons` leaves the tail's predicate
alone, so the tail is filtered by `x ∈ sub` while the induction hypothesis is
about `x ∈ t`, and the two never meet.  Generalising `sub` is the fix. -/
private theorem filter_mem_of_mem : ∀ (sub l : List α), [DecidableEq α] →
    (∀ x ∈ l, x ∈ sub) → l.filter (fun x => x ∈ sub) = l := by
  intro sub l
  induction l with
  | nil => intro _ _; rfl
  | cons a t ih =>
    intro _ ha
    rw [List.filter_cons, ite_eq_left (by simpa using ha a List.mem_cons_self),
      ih (fun x hx => ha x (List.mem_cons_of_mem a hx))]

/-- Filtering by membership in the original list keeps everything. -/
private theorem filter_mem_id (l : List α) [DecidableEq α] :
    l.filter (fun x => x ∈ l) = l :=
  filter_mem_of_mem l l (fun _ hx => hx)

/-- Turning `filterMap` into `filter` when the test is an `if`.  Stated with a
`Prop`-valued predicate so that `rw` can match it against the `if x ∈ sub` the
definitions write; a `Bool`-valued version would not be defequal to those. -/
private theorem filterMap_if_some : ∀ (l : List α) (q : α → Prop) [DecidablePred q],
    l.filterMap (fun x => if q x then some x else none) = l.filter q := by
  intro l
  induction l with
  | nil => intro q _; rfl
  | cons a t ih =>
    intro q _
    by_cases h : q a
    · simp [h, ih]
    · simp [h, ih]

/-- `filterMap` through a membership test that always succeeds. -/
private theorem filterMap_mem_id (l : List α) [DecidableEq α] :
    l.filterMap (fun x => if x ∈ l then some x else none) = l := by
  rw [filterMap_if_some]
  exact filter_mem_id l

/-- Append the deduplicated list, then truncate back to the original length. -/
theorem viaEraseDupsTake_eq_id (l : List α) [DecidableEq α] : viaEraseDupsTake l = l := by
  simp [viaEraseDupsTake]

/-- Filtering by membership in the original list, twice. -/
theorem viaEraseDupsFilter_eq_id (l : List α) [DecidableEq α] : viaEraseDupsFilter l = l := by
  simp [viaEraseDupsFilter, filter_mem_id]

/-- Filter by membership in the original list. -/
theorem viaFilterMem_eq_id (l : List α) [DecidableEq α] : viaFilterMem l = l := by
  simp [viaFilterMem, filter_mem_id]

/-- `filterMap` through a membership test. -/
theorem viaFilterMapMem_eq_id (l : List α) [DecidableEq α] : viaFilterMapMem l = l := by
  simp [viaFilterMapMem, filterMap_mem_id]

end List
end Equiv
