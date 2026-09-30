import Scripts.Test.Equiv.List.Map

/-!
# Proofs: `List.map` alternatives are equal to the original

All four alternatives in `../Map.lean` are proved equal to `List.map`.
`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.map

universe u v

variable {α : Type u} {β : Type v}

/-! ## `byRec` -/

/-- Both are structural recursions, but not definitionally equal: `byRec` is
compiled by the equation compiler and `List.map` is not. -/
theorem byRec_eq_map (f : α → β) (l : List α) : byRec f l = List.map f l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [byRec, ih]

/-! ## `byFoldlCons` -/

/-- The fold conses each image onto the *front* of the accumulator, so what it
accumulates is the reverse of `List.map f l`; appending the seed on the right
keeps the statement in that orientation, and the `reverse` in the definition
cancels the reversal.  The seed must be generalised, because on a cons the
recursion runs at seed `f a :: init`. -/
private theorem foldl_rev (f : α → β) (init : List β) (l : List α) :
    l.foldl (fun acc a => f a :: acc) init = (l.map f).reverse ++ init := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, ih, List.singleton_append, List.append_assoc,
      List.reverse_cons, List.map_cons]

theorem byFoldlCons_eq_map (f : α → β) (l : List α) : byFoldlCons f l = List.map f l := by
  simp only [byFoldlCons, foldl_rev, List.append_nil, List.reverse_reverse]

/-! ## `byOfFn` -/

/-- Index-driven, so the induction has to re-index rather than cons.  The inner
step is `List.ofFn_succ`, which splits the index type `Fin (n + 1)` into `0` and
`succ`; `List.get_cons_zero` handles the head, and the tail needs the `Fin`
shift `(a :: t).get i.succ = t.get i`. -/
theorem byOfFn_eq_map (f : α → β) (l : List α) :
    List.ofFn (fun i : Fin l.length => f (l.get i)) = List.map f l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.length_cons, List.ofFn_succ, List.get_cons_zero, List.map_cons]
    have h : (fun i : Fin t.length => f ((a :: t).get i.succ))
        = (fun i : Fin t.length => f (t.get i)) := by
      funext i
      simp
    rw [h, ih]

/-! ## `byReverseRec`

The awkward one, for a structural reason rather than a mathematical one.

`List.reverseRecOn` is implemented through `List.reverseRec`, which — as
`simp only [List.reverseRec]` shows — recurses on `l.dropLast` and produces the
head via `l.getLast`.  So:

* the recursion is **not** structural on the head, which rules out `induction l`;
* Mathlib has `List.reverseRecOn_nil` and `List.reverseRecOn_concat` (both on
  the `xs ++ [x]` shape) but **no induction principle** — I checked
  `List.reverseRecOn.induct` and `List.reverseRecOn_induct`, neither exists.

The way through is to recurse on the *length* instead, which needs a
decomposition lemma that Mathlib also lacks.  Both are supplied here:

* `dropLast_getLast` — a nonempty list is its `dropLast` plus its last element,
  and that `dropLast` is strictly shorter;
* `via_append` — stated purely in terms of `byReverseRec` itself, by appending
  one element.  Writing the step out instead does *not* work: a `match` written
  in a new declaration compiles to a different private auxiliary than the
  imported one, and the two do not unify.

Note the base value lands on the **left**: the general statement is
`l.reverseRecOn m (fun _ a ih => ih ++ [f a]) = m ++ l.map f`, not
`l.map f ++ m`.  The latter is false, and an earlier attempt used it.
-/

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

private theorem via_append (f : α → β) : ∀ (l : List α) (a : α),
    byReverseRec f (l ++ [a]) = byReverseRec f l ++ [f a] := by
  intro l a
  simp only [byReverseRec, List.reverseRecOn_concat]

theorem byReverseRec_eq_map (f : α → β) (l : List α) : byReverseRec f l = List.map f l := by
  induction hl : l.length using Nat.strong_induction_on generalizing l with
  | h n ihn =>
    cases l with
    | nil => simp [byReverseRec]
    | cons a t =>
      obtain ⟨hd, hlt⟩ := dropLast_getLast (a :: t) (by simp)
      have key : ∃ pre last, a :: t = pre ++ [last] ∧ pre.length < (a :: t).length :=
        ⟨(a :: t).dropLast, (a :: t).getLast (by simp), hd.symm, hlt⟩
      obtain ⟨pre, last, hd', hlt'⟩ := key
      rw [hd', via_append, ihn _ (by omega) _ rfl]
      rw [List.map_append, List.map_cons, List.map_nil]

/-! ## Against the original -/

theorem byRec_eq_orig (f : α → β) (l : List α) : byRec f l = orig f l := byRec_eq_map f l

theorem byFoldlCons_eq_orig (f : α → β) (l : List α) : byFoldlCons f l = orig f l :=
  byFoldlCons_eq_map f l

theorem byOfFn_eq_orig (f : α → β) (l : List α) : byOfFn f l = orig f l := byOfFn_eq_map f l

theorem byReverseRec_eq_orig (f : α → β) (l : List α) : byReverseRec f l = orig f l :=
  byReverseRec_eq_map f l

end Alt.List.map
