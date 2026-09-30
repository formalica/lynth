import Scripts.Test.Equiv.List.Partition

/-!
# Proofs: `List.partition` alternatives are equal to the original

All four alternatives in `../Partition.lean` are proved.

The file opens on a pleasant surprise: `List.partition p l` is **already**
`(List.filter p l, List.filter (not ∘ p) l)` as a `simp` lemma, so the
`brecOn` that `List.partition` compiles through (`List.partition.loop`) never has
to be unfolded at all.  Only the `not ∘ p` versus `!p` mismatch stands between
that and the two-filter route, and `filter_congr` closes it.

The two fold routes are proved against seed-generalised fold lemmas, which is
what makes the `ys ++ [a]`-appending step work: the statement has to hold for
arbitrary seeds because the induction starts at an arbitrary seed.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.partition

universe u

variable {α : Type u}

/-! ## Recovering the loop's content -/

/-- `List.partition` is *stated* as the pair of filters, so this is free; the only
work is turning `not ∘ p` into `!p`. -/
theorem partition_eq_filters (p : α → Bool) (l : List α) :
    List.partition p l = (List.filter p l, List.filter (fun x => !p x) l) := by
  have h : List.partition p l = (List.filter p l, List.filter (not ∘ p) l) := by simp
  rw [h]
  apply Prod.ext
  · rfl
  · apply List.filter_congr
    intro x hx
    rfl

/-! ## `viaTwoFilters` -/

/-- The lemma just proved *is* the statement. -/
theorem viaTwoFilters_eq_partition (p : α → Bool) (l : List α) :
    viaTwoFilters p l = List.partition p l := (partition_eq_filters p l).symm

/-! ## `viaFilterMapPair` -/

private theorem filterMap_keep (p : α → Bool) : ∀ (l : List α),
    List.filterMap (fun a => if p a then some a else none) l = l.filter p := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hp : p a with
    | true => simp [hp, ih]
    | false => simp [hp, ih]

private theorem filterMap_drop (p : α → Bool) : ∀ (l : List α),
    List.filterMap (fun a => if p a then none else some a) l = l.filter (fun x => !p x) := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hp : p a with
    | true => simp [hp, ih]
    | false => simp [hp, ih]

theorem viaFilterMapPair_eq_partition (p : α → Bool) (l : List α) :
    viaFilterMapPair p l = List.partition p l := by
  rw [viaFilterMapPair, filterMap_keep, filterMap_drop, partition_eq_filters]

/-! ## `byFoldl` -/

/-- Appending each element to its own half is the same as appending *all* the
kept elements of the rest.  No invariant about the seed is needed: the step only
ever appends, so the seed's contents are irrelevant and the induction can start
anywhere. -/
private theorem foldl_partition : ∀ (p : α → Bool) (ys ns : List α) (rest : List α),
    List.foldl (fun (ys, ns) a => if p a then (ys ++ [a], ns) else (ys, ns ++ [a]))
      (ys, ns) rest = (ys ++ rest.filter p, ns ++ rest.filter (fun x => !p x)) := by
  intro p ys ns rest
  induction rest generalizing ys ns with
  | nil => simp
  | cons a t ih =>
    cases hp : p a with
    | true => simp [List.foldl_cons, hp, ih, List.append_assoc]
    | false => simp [List.foldl_cons, hp, ih, List.append_assoc]

theorem byFoldl_eq_partition (p : α → Bool) (l : List α) : byFoldl p l = List.partition p l := by
  rw [byFoldl, foldl_partition, partition_eq_filters]
  simp

/-! ## `byRevFoldl` -/

/-- Running right to left and consing means the survivors come out in the
original order, so the seed ends up *after* the filtered part rather than before
it — the opposite end from `byFoldl`, and the reason this route is linear. -/
private theorem revfoldl_partition : ∀ (p : α → Bool) (ys ns : List α) (rest : List α),
    List.foldl (fun (ys, ns) a => if p a then (a :: ys, ns) else (ys, a :: ns))
      (ys, ns) rest.reverse = (rest.filter p ++ ys, rest.filter (fun x => !p x) ++ ns) := by
  intro p ys ns rest
  induction rest generalizing ys ns with
  | nil => simp
  | cons a t ih =>
    cases hp : p a with
    | true =>
      simp [List.foldl_append, List.foldl_cons, List.reverse_cons, hp, ih]
    | false =>
      simp [List.foldl_append, List.foldl_cons, List.reverse_cons, hp, ih]

theorem byRevFoldl_eq_partition (p : α → Bool) (l : List α) :
    byRevFoldl p l = List.partition p l := by
  rw [byRevFoldl, revfoldl_partition, partition_eq_filters]
  apply Prod.ext <;> simp

/-! ## Against the original -/

theorem viaTwoFilters_eq_orig (p : α → Bool) (l : List α) : viaTwoFilters p l = orig p l :=
  viaTwoFilters_eq_partition p l

theorem viaFilterMapPair_eq_orig (p : α → Bool) (l : List α) :
    viaFilterMapPair p l = orig p l := viaFilterMapPair_eq_partition p l

theorem byFoldl_eq_orig (p : α → Bool) (l : List α) : byFoldl p l = orig p l :=
  byFoldl_eq_partition p l

theorem byRevFoldl_eq_orig (p : α → Bool) (l : List α) : byRevFoldl p l = orig p l :=
  byRevFoldl_eq_partition p l

end Alt.List.partition
