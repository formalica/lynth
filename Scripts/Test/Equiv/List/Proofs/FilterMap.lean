import Scripts.Test.Equiv.List.FilterMap

/-!
# Proofs: `List.filterMap` alternatives are equal to the original

All five alternatives in `../FilterMap.lean` are proved equal to `List.filterMap`
here.  `orig` is imported, not redefined.  No `sorry`, no `axiom`, no
`native_decide`.

## The obstacle, and the two lemmas that get round it

Three of the five are seed-sensitive or tail-recursive, and for both of those the
obvious proof does not compile.  The reason is worth recording, because it cost
most of the effort here:

> A `match` written in one declaration compiles to a *private* auxiliary
> (`foldl_rev.match_1`); the same `match` written in another compiles to a
> different one (`byRec.match_1`).  They are not definitionally equal and do not
> unify.  So a seed-generalised helper that **restates the fold step** never
> matches the goal after `simp only [byFoldlRev]`, and `Option.casesOn` is no
> help — the auxiliary is not defeq to it either.

Two lemmas avoid the problem entirely, because both are stated purely in terms of
the *imported* definitions:

* `dropLast_getLast` — a nonempty list is its `dropLast` plus its last element,
  and that `dropLast` is strictly shorter.  Mathlib has no such lemma, and it is
  what lets the proofs recurse on `l.length` rather than on `l`: the underlying
  recursors (`List.foldl` in this file, `List.reverseRec` behind
  `List.reverseRecOn`) are **not** structural on the head, so `induction l` is
  simply unavailable for them.
* `via_some` / `via_none` — one-element-append lemmas, proved by
  `List.foldl_append` (or `List.flatMap_append`, or `List.map_append` +
  `List.filterMap_append`) with a `cases h : f a` to reduce the `match`.  The
  `match` involved is always the imported one, so it reduces.

Everything then closes with the strong induction, `List.filterMap_append`, and
the corresponding one-element case.
-/

namespace Alt.List.filterMap

universe u v

variable {α : Type u} {β : Type v}

/-! ## `byRec` -/

/-- The one easy case: a plain structural induction.  `cases h : f a` is needed
because `List.filterMap_cons` states the head test as a `match`, and that is what
lets the inductive hypothesis apply to the tail. -/
theorem byRec_eq_filterMap (f : α → Option β) (l : List α) :
    byRec f l = List.filterMap f l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [byRec, List.filterMap_cons]
    cases h : f a <;> simp_all

/-! ## `byFoldlRev` -/

private theorem dropLast_getLast : ∀ (l : List α) (h : l ≠ []),
    l.dropLast ++ [l.getLast h] = l ∧ l.dropLast.length < l.length
  | [], h => by simp at h
  | a :: t, _ => by
    cases t with
    | nil => exact ⟨rfl, by simp⟩
    | cons b t' =>
      obtain ⟨hd, hl⟩ := dropLast_getLast (b :: t') (by intro h; cases h)
      constructor
      · simp [hd]
      · simp only [List.dropLast_cons_cons, List.length_cons]
        simp only [List.length_cons] at hl
        omega

/-- Appending an accepted element contributes exactly that element, at the end.
The seed is fixed at `[]`, so `List.foldl_append` then `List.foldl_cons` reduce
the fold to the step at the new last element. -/
private theorem via_some (f : α → Option β) (b : β) : ∀ (l : List α) (a : α),
    f a = some b → byFoldlRev f (l ++ [a]) = byFoldlRev f l ++ [b] := by
  intro l a h
  simp only [byFoldlRev, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [h]
  simp

/-- Appending a rejected element contributes nothing at all. -/
private theorem via_none (f : α → Option β) : ∀ (l : List α) (a : α),
    f a = none → byFoldlRev f (l ++ [a]) = byFoldlRev f l := by
  intro l a h
  simp only [byFoldlRev, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [h]

theorem byFoldlRev_eq_filterMap (f : α → Option β) (l : List α) :
    byFoldlRev f l = List.filterMap f l := by
  induction hl : l.length using Nat.strong_induction_on generalizing l with
  | h n ihn =>
    cases l with
    | nil => simp [byFoldlRev]
    | cons a t =>
      obtain ⟨hd, hlt⟩ := dropLast_getLast (a :: t) (by simp)
      have key : ∃ pre last, a :: t = pre ++ [last] ∧ pre.length < (a :: t).length :=
        ⟨(a :: t).dropLast, (a :: t).getLast (by simp), hd.symm, hlt⟩
      obtain ⟨pre, last, hd', hlt'⟩ := key
      rw [hd']
      cases hf : f last with
      | none =>
        rw [via_none _ _ _ hf, ihn _ (by omega) _ rfl, List.filterMap_append]
        simp [hf]
      | some b =>
        rw [via_some _ b _ _ hf, ihn _ (by omega) _ rfl, List.filterMap_append]
        simp [hf]

/-! ## `byFinRange` -/

/-- `List.ofFn l.get = l`, and `ofFn f` is `map f` over `finRange`: so walking
the positions with `finRange` and reading with `get` visits exactly the elements
of `l`, in order. -/
private theorem finRange_get (l : List α) : List.map l.get (List.finRange l.length) = l := by
  rw [← List.ofFn_eq_map (f := l.get)]
  exact List.ofFn_get l

/-- `List.foldl_map` turns "fold the index function along `map l.get`" back into
"fold the element function along the list", so the two folds are literally the
same computation and `byFoldlRev`'s proof carries over. -/
private theorem finRange_foldl (f : α → Option β) (l : List α) :
    byFinRange f l
      = (List.foldl
          (fun acc a => match f a with
            | some b => b :: acc
            | none => acc) ([] : List β) l).reverse := by
  unfold byFinRange
  have h := List.foldl_map
      (f := l.get)
      (g := fun (acc : List β) a => match f a with
        | some b => b :: acc
        | none => acc)
      (init := ([] : List β)) (l := List.finRange l.length)
  rw [finRange_get l] at h
  exact congrArg List.reverse h.symm

theorem byFinRange_eq_filterMap (f : α → Option β) (l : List α) :
    byFinRange f l = List.filterMap f l := by
  rw [finRange_foldl f l]
  exact byFoldlRev_eq_filterMap f l

/-! ## `viaFlatMap` -/

/-- Each accepted element contributes a singleton list and each rejected one the
empty list, so the concatenation *is* the filtering.  `List.flatMap_append` and
`List.flatMap_cons` do all the work here. -/
private theorem fm_some (f : α → Option β) (b : β) : ∀ (l : List α) (a : α),
    f a = some b → viaFlatMap f (l ++ [a]) = viaFlatMap f l ++ [b] := by
  intro l a h
  simp only [viaFlatMap, List.flatMap_append, List.flatMap_cons, h,
    List.flatMap_nil]
  rfl

private theorem fm_none (f : α → Option β) : ∀ (l : List α) (a : α),
    f a = none → viaFlatMap f (l ++ [a]) = viaFlatMap f l := by
  intro l a h
  simp only [viaFlatMap, List.flatMap_append, List.flatMap_cons, h,
    List.flatMap_nil, List.append_nil]

theorem viaFlatMap_eq_filterMap (f : α → Option β) (l : List α) :
    viaFlatMap f l = List.filterMap f l := by
  induction hl : l.length using Nat.strong_induction_on generalizing l with
  | h n ihn =>
    cases l with
    | nil => simp [viaFlatMap]
    | cons a t =>
      obtain ⟨hd, hlt⟩ := dropLast_getLast (a :: t) (by simp)
      have key : ∃ pre last, a :: t = pre ++ [last] ∧ pre.length < (a :: t).length :=
        ⟨(a :: t).dropLast, (a :: t).getLast (by simp), hd.symm, hlt⟩
      obtain ⟨pre, last, hd', hlt'⟩ := key
      rw [hd']
      cases hf : f last with
      | none =>
        rw [fm_none _ _ _ hf, ihn _ (by omega) _ rfl, List.filterMap_append]
        simp [hf]
      | some b =>
        rw [fm_some _ b _ _ hf, ihn _ (by omega) _ rfl, List.filterMap_append]
        simp [hf]

/-! ## `viaMapThenId` -/

/-- The two-phase pipeline: `map` builds a list of `Option β` (output length
still matching the input), then `filterMap id` decodes it.  Here
`List.filterMap_append` distributes over the concatenation, so appending one
element to the input commutes with the decode. -/
private theorem mt_some (f : α → Option β) (b : β) : ∀ (l : List α) (a : α),
    f a = some b → viaMapThenId f (l ++ [a]) = viaMapThenId f l ++ [b] := by
  intro l a h
  simp only [viaMapThenId, List.map_append, List.filterMap_append, List.map_cons,
    List.map_nil, List.filterMap_cons, h]
  rfl

private theorem mt_none (f : α → Option β) : ∀ (l : List α) (a : α),
    f a = none → viaMapThenId f (l ++ [a]) = viaMapThenId f l := by
  intro l a h
  simp [viaMapThenId, h]

theorem viaMapThenId_eq_filterMap (f : α → Option β) (l : List α) :
    viaMapThenId f l = List.filterMap f l := by
  induction hl : l.length using Nat.strong_induction_on generalizing l with
  | h n ihn =>
    cases l with
    | nil => simp [viaMapThenId]
    | cons a t =>
      obtain ⟨hd, hlt⟩ := dropLast_getLast (a :: t) (by simp)
      have key : ∃ pre last, a :: t = pre ++ [last] ∧ pre.length < (a :: t).length :=
        ⟨(a :: t).dropLast, (a :: t).getLast (by simp), hd.symm, hlt⟩
      obtain ⟨pre, last, hd', hlt'⟩ := key
      rw [hd']
      cases hf : f last with
      | none =>
        rw [mt_none _ _ _ hf, ihn _ (by omega) _ rfl, List.filterMap_append]
        simp [hf]
      | some b =>
        rw [mt_some _ b _ _ hf, ihn _ (by omega) _ rfl, List.filterMap_append]
        simp [hf]

/-! ## Against the original -/

theorem byRec_eq_orig (f : α → Option β) (l : List α) : byRec f l = orig f l :=
  byRec_eq_filterMap f l

theorem byFoldlRev_eq_orig (f : α → Option β) (l : List α) : byFoldlRev f l = orig f l :=
  byFoldlRev_eq_filterMap f l

theorem byFinRange_eq_orig (f : α → Option β) (l : List α) : byFinRange f l = orig f l :=
  byFinRange_eq_filterMap f l

theorem viaFlatMap_eq_orig (f : α → Option β) (l : List α) : viaFlatMap f l = orig f l :=
  viaFlatMap_eq_filterMap f l

theorem viaMapThenId_eq_orig (f : α → Option β) (l : List α) : viaMapThenId f l = orig f l :=
  viaMapThenId_eq_filterMap f l

end Alt.List.filterMap
