import Scripts.Test.Equiv.List.Sublists

/-!
# Proofs: `List.sublists` alternatives are equal to the original

All three alternatives in `../Sublists.lean` are proved.  `List.sublists` is a
plain `foldr`, so unlike `List.splitAt` or `List.span` it has usable equations,
and the only real work is the two collection lemmas that say `map`+`flatten` and
`foldr`+`++` are the two faces of `flatMap`.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.sublists

universe u

variable {α : Type u}

/-! ## A shared helper -/

/-- The cons equation, spelled out.  `List.sublists` is a `foldr`, so the cons
case is `flatMap (fun x => [x, a :: x])` applied to the tail's family. -/
private theorem sublists_cons (a : α) (l : List α) :
    List.sublists (a :: l) = (List.sublists l).flatMap (fun x => [x, a :: x]) := by
  simp only [List.sublists, List.foldr_cons]

/-- `map` followed by `flatten` is `flatMap`. -/
private theorem map_flatten : ∀ (L : List α) (f : α → List β), (L.map f).flatten = L.flatMap f
  | [], _ => rfl
  | a :: L, f => by
    rw [List.map_cons, List.flatten_cons, List.flatMap_cons, map_flatten]

/-- Concatenating the bundles with a `foldr` is also `flatMap`. -/
private theorem foldr_map_foldr : ∀ (L : List α) (f : α → List β),
    (L.map f).foldr (fun b acc => b ++ acc) [] = L.flatMap f
  | [], _ => rfl
  | a :: L, f => by
    rw [List.map_cons, List.foldr_cons, foldr_map_foldr, List.flatMap_cons]

/-! ## `byConsEq` -/

/-- The cons equation taken in the `flatMap` form the definition uses, so both
sides are literally the same term. -/
theorem byConsEq_eq_sublists : ∀ (l : List α), byConsEq l = List.sublists l := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => rw [byConsEq, sublists_cons, ih]

/-! ## `byConsPlain` -/

theorem byConsPlain_eq_sublists : ∀ (l : List α), byConsPlain l = List.sublists l := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => rw [byConsPlain, sublists_cons, map_flatten, ih]

/-! ## `byAppendStep` -/

theorem byAppendStep_eq_sublists : ∀ (l : List α), byAppendStep l = List.sublists l := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => rw [byAppendStep, sublists_cons, foldr_map_foldr, ih]

/-! ## Against the original -/

theorem byConsEq_eq_orig (l : List α) : byConsEq l = orig l := byConsEq_eq_sublists l

theorem byConsPlain_eq_orig (l : List α) : byConsPlain l = orig l := byConsPlain_eq_sublists l

theorem byAppendStep_eq_orig (l : List α) : byAppendStep l = orig l := byAppendStep_eq_sublists l

end Alt.List.sublists
