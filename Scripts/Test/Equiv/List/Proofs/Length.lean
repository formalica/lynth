import Scripts.Test.Equiv.List.Length

/-!
# Proofs: `List.length` alternatives are equal to the original

Every `def` in `../Length.lean` is proved equal to `List.length`.

## Why this file imports

`Scripts/Test/Equiv` is declared as the `EquivCorpus` library in `lakefile.toml`
(see the comment on that `[[lean_lib]]` for the globs it uses).  So the
definitions live in exactly one place and this file contains only proofs.  Build
the library first:

```
lake build EquivCorpus
```

An earlier version of this file copied the definitions in verbatim, on the
grounds that `Scripts/` was not a library.  That was true when written, but it
made every `def` a copy-paste drift hazard, so the library was added instead.

## Conventions

* Every alternative gets a theorem `viaX_eq_orig : viaX l = orig l`.
* Statements are oriented alternative-first, so the goal reads as "the
  alternative computes the same thing".
* Proofs are by structural induction unless a generalised helper is genuinely
  needed — the seed of a `foldl` shifts as the induction proceeds, so those two
  cases get an `init`-generalised lemma.
* No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.length

variable {α : Type u}

/-! ## `direct` -/

/-- The two structural recursions coincide.  Not `rfl`: `direct` is compiled by
the equation compiler and `List.length` is not, so they are equal but not
definitionally so. -/
theorem direct_eq_length (l : List α) : direct l = List.length l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [direct, ih, List.length_cons]

/-! ## `viaFoldl` -/

/-- `foldl` with an incrementing counter, for any seed.  The seed must be
generalised: on a cons the recursion runs with seed `init + 1`, so an induction
that fixes the seed at `0` has nothing to rewrite with. -/
theorem foldl_add (l : List α) (init : ℕ) :
    l.foldl (fun acc _ => acc + 1) init = init + l.length := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih => simp only [List.foldl_cons, ih, List.length_cons]; omega

theorem viaFoldl_eq_length (l : List α) : viaFoldl l = List.length l := by
  simp only [viaFoldl, foldl_add, Nat.zero_add]

/-! ## `viaFoldr` -/

/-- No seed generalisation needed: `foldr` threads the accumulator from the tail
outwards, so the induction hypothesis applies at the same seed. -/
theorem foldr_eq_length (l : List α) :
    l.foldr (fun _ acc => acc + 1) 0 = List.length l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.foldr_cons, ih, List.length_cons]

/-! ## `viaSumMap` -/

theorem sumMap_eq_length (l : List α) :
    (l.map fun _ => (1 : ℕ)).sum = List.length l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.add_comm]

/-! ## `viaCountP` -/

/-- `List.countP_cons` states the increment as `+ if p a = true then 1 else 0`;
with the constant-`true` predicate that branch collapses, which is what
`ite_true` discharges. -/
theorem countP_eq_length (l : List α) :
    l.countP (fun _ => true) = List.length l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.countP_cons, ite_true, ih, List.length_cons]

/-! ## `viaRevFoldl` -/

/-- Reversing then folding left.  Seed-generalised for the same reason as
`foldl_add`; the rewrite of the inductive hypothesis is preceded by
`List.reverse_cons`, `List.foldl_append` and `List.foldl_nil` to get down to a
single `foldl` at the shifted seed.  The closing step is `Nat.add_assoc`. -/
theorem revFoldl_add (l : List α) (init : ℕ) :
    l.reverse.foldl (fun acc _ => acc + 1) init = init + l.length := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_nil, List.foldl_cons,
      ih, List.length_cons, Nat.add_assoc]

theorem viaRevFoldl_eq_length (l : List α) : viaRevFoldl l = List.length l := by
  simp only [viaRevFoldl, revFoldl_add, Nat.zero_add]

/-! ## All six against the original -/

theorem direct_eq_orig (l : List α) : direct l = orig l := direct_eq_length l

theorem viaFoldl_eq_orig (l : List α) : viaFoldl l = orig l := viaFoldl_eq_length l

theorem viaFoldr_eq_orig (l : List α) : viaFoldr l = orig l := foldr_eq_length l

theorem viaSumMap_eq_orig (l : List α) : viaSumMap l = orig l := sumMap_eq_length l

theorem viaCountP_eq_orig (l : List α) : viaCountP l = orig l := countP_eq_length l

theorem viaRevFoldl_eq_orig (l : List α) : viaRevFoldl l = orig l :=
  viaRevFoldl_eq_length l

end Alt.List.length
