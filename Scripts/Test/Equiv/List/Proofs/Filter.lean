import Scripts.Test.Equiv.List.Filter

/-!
# Proofs: `List.filter` alternatives are equal to the original

All four alternatives in `../Filter.lean` are proved equal to `List.filter` here.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.filter

universe u

variable {α : Type u}

/-! ## `byRec` -/

/-- `List.filter_cons` is stated with the test `p x = true`, whereas `byRec`
writes `if p a then`, so the head test needs a case split on the `Bool` before
the inductive hypothesis applies.  That mismatch is the only obstacle. -/
theorem byRec_eq_filter (p : α → Bool) (l : List α) : byRec p l = List.filter p l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [byRec, List.filter_cons]
    cases hp : p a <;> simp_all

/-! ## `byFoldlRev` -/

/-- Seed-generalised, for the same reason as in `Length.lean`: on a cons the
recursion runs at seed `f a :: init`, so an induction fixing the seed has
nothing to rewrite with.  The accumulator ends up holding the reverse of the
filtered list. -/
private theorem foldl_rev (p : α → Bool) (init : List α) (l : List α) :
    l.foldl (fun acc a => if p a then a :: acc else acc) init
      = (l.filter p).reverse ++ init := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih, List.filter_cons]
    cases hp : p a <;> simp_all

theorem byFoldlRev_eq_filter (p : α → Bool) (l : List α) :
    byFoldlRev p l = List.filter p l := by
  simp only [byFoldlRev, foldl_rev, List.append_nil, List.reverse_reverse]

/-! ## `viaFilterMap` -/

/-- Keep-or-drop restated as some-or-nothing.  The helper is stated with the
body already unfolded, so that the recursive call in the goal is syntactically
the same term as the inductive hypothesis. -/
private theorem fmap_filter (p : α → Bool) : ∀ l : List α,
    List.filterMap (fun a => if p a then some a else none) l = List.filter p l
  | [] => rfl
  | a :: t => by
    rw [List.filterMap_cons, List.filter_cons]
    simp only [fmap_filter]
    cases hp : p a <;> simp_all

theorem viaFilterMap_eq_filter (p : α → Bool) (l : List α) :
    viaFilterMap p l = List.filter p l := fmap_filter p l

/-! ## `byFinRange` -/

/-- The index list visits every position once, so `List.get` reads at each of
them produce `l` back as a `map`. -/
private theorem map_get_finRange (l : List α) :
    List.map l.get (List.finRange l.length) = l :=
  (List.ofFn_eq_map (f := l.get)).symm.trans (List.ofFn_get l)

/-- `List.foldl_map` moves the reads out of the step function, and the index
list then collapses — which hands over exactly the fold `foldl_rev` above was
stated for. -/
private theorem foldl_finRange (h : List α → α → List α) (l : List α) (acc : List α) :
    List.foldl (fun a i => h a (l.get i)) acc (List.finRange l.length) = List.foldl h acc l := by
  rw [← List.foldl_map, map_get_finRange]

theorem byFinRange_eq_filter (p : α → Bool) (l : List α) :
    byFinRange p l = List.filter p l := by
  simp only [byFinRange]
  rw [foldl_finRange (fun acc x => if p x then x :: acc else acc) l []]
  rw [foldl_rev]
  simp



/-! ## Against the original -/

theorem byRec_eq_orig (p : α → Bool) (l : List α) : byRec p l = orig p l := byRec_eq_filter p l

theorem byFoldlRev_eq_orig (p : α → Bool) (l : List α) : byFoldlRev p l = orig p l :=
  byFoldlRev_eq_filter p l

theorem viaFilterMap_eq_orig (p : α → Bool) (l : List α) : viaFilterMap p l = orig p l :=
  viaFilterMap_eq_filter p l

theorem byFinRange_eq_orig (p : α → Bool) (l : List α) : byFinRange p l = orig p l :=
  byFinRange_eq_filter p l

end Alt.List.filter
