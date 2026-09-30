import Scripts.Test.Equiv.List.EquivTerm

/-!
# Proofs: every route in `../EquivTerm.lean` returns its first argument

`../EquivTerm.lean` collects routes from `(a : α, l : List α)` back to `a`, so each
theorem has the shape

```lean
theorem viaFoo_eq_self (a : α) (l : List α) : viaFoo a l = a
```

**All twenty-two routes are proved here.**  Routes that infer value equality
from `==`, as well as the two difference-based routes, require lawful equality.

## What the proofs actually needed

Most routes reduce to "a list built out of copies of `a` is either empty or starts
with `a`, and `headD` falls back to `a`".  That is the content of the three
helpers, and it is the *whole* argument for `viaReplicateLength`,
`viaCountReplicate`, `viaReplaceAllMap`, `viaFilterMapSome` and
`viaFlatMapConst` — in every case the count or the structure is irrelevant.  Worth
noting because `viaCountReplicate` looks like it needs to know something about
`List.count`; it does not.

The remaining proved routes are one-liners: `viaAppendLast`, `viaConsReverseLast`,
`viaInsertAtAtEnd`, `viaInsertAtFront`, `viaTakeDropRecompose` and
`viaSplitAtRecompose` are all `simp`, because `insertIdx` at either end, the
`take`/`drop` split and the `splitAt` split all have library characterisations.

## A trap worth recording

`List.headD l d` unfolds to `l.head?.getD d`, so `simp` will not line a `headD`
goal up with a lemma stated about `headD`.  The three helpers that needed it use
`change` to get back to the `headD` form.  Note also that `List.map_const` does not
fire on `fun x => a` — it is stated for the constant-curried form — so
`viaReplaceAllMap` needs its own hand-written helper.

## Instance requirements

Routes that conclude `x = a` from `x == a` carry `[LawfulBEq α]`.  The
`viaDiffHead` proof also needs lawfulness: with an arbitrary `BEq`, `diff` can
remove the leading `a` and leave a different tail element.  The find-index and
zip-index proofs use direct structural invariants, so they need no library
equation for the offset indices.

No `sorry`, no `axiom`, no `native_decide`, no `Classical`.
-/

namespace Equiv
namespace List

variable {α : Type u}

universe u

universe v

/-- Whatever the count, a replication of `a` is either empty (so the fallback
`a` wins) or starts with `a`.  This is the whole content of both `viaReplicateLength`
and `viaCountReplicate`: the count is irrelevant. -/
private theorem replicate_headD : ∀ (n : ℕ) (a : α), (List.replicate n a).headD a = a := by
  intro n
  induction n with
  | zero => intro a; simp [List.replicate_zero]
  | succ m _ => intro a; simp [List.replicate_succ]

/-- `map` to a constant `a`: either empty, or starting with `a`.  `List.map_const`
does not fire on `fun x => a` (it is stated for the constant-curried form), so
this is by hand. -/
private theorem map_const_headD : ∀ (l : List α) (a : α),
    (l.map (fun _ => a)).headD a = a := by
  intro l
  induction l with
  | nil => intro a; rfl
  | cons b l _ => intro a; simp

/-- `filterMap` to a constant `some a`: either empty, or starting with `a`. -/
private theorem filterMap_const_headD : ∀ (l : List α) (a : α),
    (l.filterMap (fun _ => some a)).headD a = a := by
  intro l
  induction l with
  | nil => intro a; rfl
  | cons b l _ => intro a; simp

/-- `flatMap` to a constant singleton: either empty, or starting with `a`. -/
private theorem flatMap_const_headD : ∀ (l : List v) (a : α),
    (l.flatMap (fun _ => [a])).headD a = a := by
  intro l
  induction l with
  | nil => intro a; rfl
  | cons b l _ => intro a; simp [List.flatMap_cons]

/-- Append `a` at the end, then read the last element back. -/
theorem viaAppendLast_eq_self (a : α) (l : List α) : viaAppendLast a l = a := by
  simp [viaAppendLast]

/-- Cons `a` at the front, reverse, then read the last element back. -/
theorem viaConsReverseLast_eq_self (a : α) (l : List α) : viaConsReverseLast a l = a := by
  simp [viaConsReverseLast]

/-- `insertIdx` at the end, then read the last element back. -/
theorem viaInsertAtEnd_eq_self (a : α) (l : List α) : viaInsertAtEnd a l = a := by
  simp [viaInsertAtEnd]

/-- `insertIdx` at the front, then read the head back. -/
theorem viaInsertAtFront_eq_self (a : α) (l : List α) : viaInsertAtFront a l = a := by
  simp [viaInsertAtFront]

/-- Replicate to the length of the list, then read the head back.  Note the
fallback: an empty list replicates to nothing, so the head is the fallback `a`. -/
theorem viaReplicateLength_eq_self (a : α) (l : List α) : viaReplicateLength a l = a := by
  change (List.replicate l.length a).headD a = a
  exact replicate_headD l.length a

/-- Map everything to `a`, then read the head back. -/
theorem viaReplaceAllMap_eq_self (a : α) (l : List α) : viaReplaceAllMap a l = a := by
  change (l.map (fun _ => a)).headD a = a
  exact map_const_headD l a

/-- `filterMap` keeping `a`, then read the head back. -/
theorem viaFilterMapSome_eq_self (a : α) (l : List α) : viaFilterMapSome a l = a := by
  change (l.filterMap (fun _ => some a)).headD a = a
  exact filterMap_const_headD l a

/-- `attach` the cons, project out the values, then read the head back. -/
theorem viaAttachCons_eq_self (a : α) (l : List α) : viaAttachCons a l = a := by
  simp [viaAttachCons]

/-- Take one off the front and drop the rest, then glue them back and read the
head. -/
theorem viaTakeDropRecompose_eq_self (a : α) (l : List α) : viaTakeDropRecompose a l = a := by
  simp [viaTakeDropRecompose]

/-- The same, routed through the pair-returning `splitAt`. -/
theorem viaSplitAtRecompose_eq_self (a : α) (l : List α) : viaSplitAtRecompose a l = a := by
  simp [viaSplitAtRecompose]

/-- `flatMap` every element to the singleton `[a]`, then read the head back. -/
theorem viaFlatMapConst_eq_self (a : α) (l : List α) : viaFlatMapConst a l = a := by
  change (l.flatMap (fun _ => [a])).headD a = a
  exact flatMap_const_headD l a

/-- Replicate `a` as many times as `a` occurs, then read the head back.  The count
is irrelevant: any count gives either a list of `a`s or the empty list, and the
empty list falls back to `a`.  So this needs no `LawfulBEq`. -/
theorem viaCountReplicate_eq_self [BEq α] (a : α) (l : List α) :
    viaCountReplicate a l = a := by
  change (List.replicate (l.count a) a).headD a = a
  exact replicate_headD (l.count a) a

/-- `erase` then `insertIdx` at the front, then read the head back.  Also
independent of what `erase` does, so no `LawfulBEq`. -/
theorem viaEraseReinsert_eq_self [BEq α] (a : α) (l : List α) :
    viaEraseReinsert a l = a := by
  simp [viaEraseReinsert]

/-! ## The `LawfulBEq` group -/

-- The eight routes above that compare with `==` are recorded as needing
-- `[LawfulBEq α]`; four of them are closed here.  The instance is not decoration:
-- `LawfulBEq.eq_of_beq` turns the route's `x == a` into `x = a`, and without it
-- the routes would be *false*, not merely unproved.  This is the `Count`/`Elem`
-- asymmetry for a third time.

variable {α : Type u}

open _root_.List

/-- `l.getD 0 a` and `l.headD a` agree, but they are not defeq and there is no
`List.headD_eq_getD`.  Both indices are `0`, so this is two cases. -/
private theorem getD_zero_eq_headD : ∀ (l : List α) (a : α), l.getD 0 a = l.headD a := by
  intro l
  cases l <;> intro a <;> rfl

/-- A filter on `· == a` is empty or starts with `a`, and `headD` falls back to
`a` in the empty case.  `LawfulBEq.eq_of_beq` is the load-bearing step. -/
private theorem filter_eq_headD : ∀ (l : List α) (a : α) [BEq α] [LawfulBEq α],
    (l.filter (· == a)).headD a = a := by
  intro l
  induction l with
  | nil => intro a instBEq instLaw; rfl
  | cons b t ih =>
    intro a instBEq instLaw
    cases hb : (b == a) with
    | true => simp [LawfulBEq.eq_of_beq hb]
    | false =>
      rw [List.filter_cons, ite_eq_right (by simpa using hb), ih a]

theorem viaFilterGetD_eq_self [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaFilterGetD a l = a := by
  change (l.filter (· == a)).getD 0 a = a
  rw [getD_zero_eq_headD]
  exact filter_eq_headD l a

/-- `find?` returns either nothing (so the fallback `a` wins) or an `x` with
`x == a`, which `LawfulBEq` makes `x = a`.  Same shape as `filter_eq_headD`, but
the cons equation is a `match` on the `Bool` rather than an `if`, so `simp` alone
reduces it. -/
private theorem find_getD : ∀ (l : List α) (a : α) [BEq α] [LawfulBEq α],
    (l.find? (· == a)).getD a = a := by
  intro l
  induction l with
  | nil => intro a _ _; rfl
  | cons b t ih =>
    intro a _ _
    cases hb : (b == a) with
    | true => simp [LawfulBEq.eq_of_beq hb]
    | false => simp [hb, ih a]

theorem viaFindGetD_eq_self [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaFindGetD a l = a :=
  find_getD l a

/-- The fold keeps the last `x` with `x == a`, or the seed `a` if there is none.
Same `LawfulBEq` step; the seed is what makes the empty and no-match cases work. -/
private theorem foldl_acc : ∀ (l : List α) (a : α) [BEq α] [LawfulBEq α],
    l.foldl (fun acc x => if x == a then x else acc) a = a := by
  intro l
  induction l with
  | nil => intro a _ _; rfl
  | cons b t ih =>
    intro a _ _
    rw [List.foldl_cons]
    cases hb : (b == a) with
    | true =>
      rw [ite_eq_left (by simp), LawfulBEq.eq_of_beq hb]
      exact ih a
    | false =>
      rw [ite_eq_right (by simp), ih a]

theorem viaFoldlAcc_eq_self [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaFoldlAcc a l = a :=
  foldl_acc l a

theorem viaPartitionHead_eq_self [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaPartitionHead a l = a := by
  have h : l.partition (· == a)
      = (l.filter (· == a), l.filter (not ∘ (· == a))) := by simp
  rw [viaPartitionHead, h]
  exact filter_eq_headD l a

/-! ## `viaScanlAbsorb` -/

/-- An absorbing `scanl` seeded with `a` produces only `a`s, and it is never
empty, so its `getLast?` is `some a`.  The step is the easy part — `f acc _ = acc`
makes `scanl f a (b :: t) = a :: scanl f a t` — and the work is all in the
`getLast?`.  Note the helper is stated with the leading `a ::` already attached,
because that is the shape `List.scanl_cons` leaves behind: `(a :: l).scanl f a`
reduces to `a :: scanl f a l`, and the seed is *not* a member of the visible
input, so it cannot be recovered by inspecting `l`. -/
private theorem scanl_absorb : ∀ (l : List α) (a : α),
    (a :: List.scanl (fun acc _ => acc) a l).getLast?.getD a = a := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons b t ih =>
    intro a
    rw [List.scanl_cons]
    simp only [getLast?_cons_cons]
    exact ih a

theorem viaScanlAbsorb_eq_self (a : α) (l : List α) : viaScanlAbsorb a l = a := by
  unfold viaScanlAbsorb
  rw [List.scanl_cons]
  exact scanl_absorb l a

/-! ## `viaSpanHead` -/

/-- A `takeWhile` prefix on `· == a` is all `a`s.  The fallback matters because an
empty prefix gives the empty list, whose `headD` is `a`.  `List.takeWhile_cons` is
available — the `if` condition is `p a = true`, a `Prop`, so the `Bool` has to be
split on before `rw` can line it up.  Note the induction hypothesis is not needed
in the `true` branch: the head of `b :: _` is `b` whatever the tail is, and
`LawfulBEq` gives `b = a`. -/
private theorem takeWhile_eq_headD : ∀ (l : List α) (a : α) [BEq α] [LawfulBEq α],
    (l.takeWhile (· == a)).headD a = a := by
  intro l
  induction l with
  | nil => intro a _ _; rfl
  | cons b t ih =>
    intro a _ _
    rw [List.takeWhile_cons]
    cases hb : (b == a) with
    | true =>
      rw [ite_eq_left (by simp)]
      simp [LawfulBEq.eq_of_beq hb]
    | false =>
      rw [ite_eq_right (by simp)]
      rfl

theorem viaSpanHead_eq_self [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaSpanHead a l = a := by
  rw [viaSpanHead, List.span_eq_takeWhile_dropWhile]
  exact takeWhile_eq_headD l a

/-! ## The remaining `diff` route

`viaDiffHead` needs `[LawfulBEq α]`.  With an arbitrary `BEq`, the behavior of
`diff` can remove the initial `a` while leaving a different tail element.  Under
lawfulness, the count theorem shows that every surviving head must equal `a`.
-/

/-- The output is empty or contains only `a`: a different head would have count
zero by `List.count_diff`, contradicting its membership in the result. -/
theorem viaDiffHead_eq_self [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaDiffHead a l = a := by
  change ((a :: l).diff l).headD a = a
  cases h : (a :: l).diff l with
  | nil => rfl
  | cons b t =>
    have hba : b = a := by
      by_contra hba
      have hmem : b ∈ (a :: l).diff l := by rw [h]; simp
      have hp : 0 < List.count b ((a :: l).diff l) := List.count_pos_iff.mpr hmem
      rw [List.count_diff] at hp
      have hab : (a == b) = false := by
        cases h' : (a == b) with
        | false => rfl
        | true =>
          have e : a = b := LawfulBEq.eq_of_beq h'
          exact False.elim (hba e.symm)
      simp [List.count_cons, hab] at hp
    subst b
    simp

/-- `[LawfulBEq α]` is required, not decorative: the
`getD` returns an element found by `x == a`, and only lawfulness turns that into
`x = a`.  The `l.length` fallback needs no instance, since it is out of range and
so returns `a` directly. -/
private theorem findIdx_fallback_getD [BEq α] [LawfulBEq α] :
    ∀ (a : α) (l : List α),
      l.getD (l.findIdx? (· == a) |>.getD l.length) a = a := by
  intro a l
  induction l with
  | nil => simp
  | cons b t ih =>
    rw [List.findIdx?_cons]
    cases hb : (b == a) with
    | true => simp [LawfulBEq.eq_of_beq hb]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      simpa using ih

theorem viaFindIdxFallback_eq_self [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaFindIdxFallback a l = a := findIdx_fallback_getD a l

/-- `[LawfulBEq α]` is required, for the same reason as
above.  The route also needs `List.zipIdx l k = l.zip ((range l.length).map (k + ·))`,
the shared missing lemma for three theorems across two files. -/
private theorem zipIdx_find_getD [BEq α] [LawfulBEq α] :
    ∀ (a : α) (l : List α) (k : ℕ),
      (((List.zipIdx l k).find? (fun p => p.1 == a)).map Prod.fst).getD a = a := by
  intro a l
  induction l with
  | nil => intro k; simp
  | cons b t ih =>
    intro k
    rw [List.zipIdx_cons]
    cases hb : (b == a) with
    | true => simp [LawfulBEq.eq_of_beq hb]
    | false =>
      simp only [List.find?_cons, hb]
      exact ih (k + 1)

theorem viaZipIdxSearch_eq_self [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaZipIdxSearch a l = a := zipIdx_find_getD a l 0

end List
end Equiv
