import Scripts.Test.Equiv.List.Foldl

/-!
# Proofs: `List.foldl` alternatives are equal to the original

All four alternatives in `../Foldl.lean` are proved equal to `List.foldl` here.

The file's own docstring makes the important point: a plausible-looking rewrite
of a fold is only valid for *some* `f`.  Everything proved below is valid for an
arbitrary `f : α → β → α` — no associativity, no commutativity, and the elements
are never reordered.  `byFoldrRev` is the one worth reading: it looks like it
reassociates the calls, but it does not.  `List.foldr` merely re-associates an
already left-nested chain while reading the list backwards.
-/

namespace Alt.List.foldl

universe u v

variable {α : Type u} {β : Type v}

/-! ## `byRec` -/

/-- The textbook structural recursion.  The `show ... = ... from rfl` step is
what lets the induction hypothesis be applied at the shifted accumulator
`f init a`. -/
theorem byRec_eq (f : α → β → α) (init : α) : ∀ (l : List β),
    byRec f init l = List.foldl f init l
  | [] => rfl
  | a :: t => by
    rw [show byRec f init (a :: t) = byRec f (f init a) t from rfl]
    exact byRec_eq f _ t

/-! ## `byFoldrRev` -/

/-- The general fact, stated for a fixed seed: reversing the list and folding
right with the arguments swapped visits the elements in their original order
and rebuilds the same left-nested chain.  `init` is fixed rather than
generalised because `List.foldr_append` is what lets the induction close. -/
private theorem foldl_rev_gen (f : α → β → α) (init : α) : ∀ (l : List β),
    List.foldr (fun a acc => f acc a) init l.reverse = List.foldl f init l
  | [] => by rfl
  | a :: t => by
    simp only [List.reverse_cons, List.foldr_append, List.foldr_cons, List.foldr_nil,
      List.foldl_cons, foldl_rev_gen]

theorem byFoldrRev_eq (f : α → β → α) (init : α) (l : List β) :
    byFoldrRev f init l = List.foldl f init l := by
  simp only [byFoldrRev, foldl_rev_gen]

/-! ## `byTailLoop` -/

/-- The same chain of `f` calls as `byRec`, but every recursive call is in tail
position.  Unlike `FilterMap`'s and `ZipWith`'s equivalents this one *is*
reducible by `rfl`: the accumulator is a plain argument of the `where`-bound
loop rather than something built by a destructuring `match`, so the equation
compiler leaves it reducible.  `byRec` is not tail-recursive, so this is the
version with bounded stack depth on long lists. -/
theorem byTailLoop_eq (f : α → β → α) (init : α) (l : List β) :
    byTailLoop f init l = List.foldl f init l := by
  induction l generalizing init with
  | nil => rfl
  | cons a t ih =>
    simp only [show byTailLoop f init (a :: t) = byTailLoop f (f init a) t from rfl,
      List.foldl_cons]
    exact ih _

/-! ## `byFinRange` -/

/-- The index list `List.finRange l.length` visits every position once, so reading
`l.get` at each of them yields `l` back — but as a `map`, not as a `fold`. -/
private theorem map_get_finRange (l : List β) :
    List.map l.get (List.finRange l.length) = l :=
  (List.ofFn_eq_map (f := l.get)).symm.trans (List.ofFn_get l)

/-- Which is enough: `List.foldl_map` pushes the `get` reads out of the step and
into the list being folded, and the index list then collapses to `l` itself.
The accumulator stays a parameter, so the cons case never has to shift it. -/
private theorem foldl_finRange (h : α → β → α) (l : List β) (acc : α) :
    List.foldl (fun a i => h a (l.get i)) acc (List.finRange l.length) = List.foldl h acc l := by
  rw [← List.foldl_map, map_get_finRange]

theorem byFinRange_eq (f : α → β → α) (init : α) (l : List β) :
    byFinRange f init l = List.foldl f init l := by
  simp only [byFinRange]
  rw [foldl_finRange f l init]

/-! ## Against the original -/

theorem byRec_eq_orig (f : α → β → α) (init : α) (l : List β) : byRec f init l = orig f init l :=
  byRec_eq f init l

theorem byTailLoop_eq_orig (f : α → β → α) (init : α) (l : List β) :
    byTailLoop f init l = orig f init l := byTailLoop_eq f init l

theorem byFoldrRev_eq_orig (f : α → β → α) (init : α) (l : List β) :
    byFoldrRev f init l = orig f init l := byFoldrRev_eq f init l

theorem byFinRange_eq_orig (f : α → β → α) (init : α) (l : List β) :
    byFinRange f init l = orig f init l := byFinRange_eq f init l

end Alt.List.foldl
