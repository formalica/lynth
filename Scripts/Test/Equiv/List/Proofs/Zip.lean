import Scripts.Test.Equiv.List.Zip

/-!
# Proofs: `List.zip` alternatives are equal to the original

All four alternatives in `../Zip.lean` are proved equal to `List.zip` here.

The only non-obvious part of the function is that it truncates to the shorter of
its two arguments, so the two degenerate cases (`[]` on either side) come first
in every definition and in every induction here.  The pairing itself is forced —
there is nothing to choose — which is why the alternatives differ in *how the
two lists are walked together* rather than in what is computed.
-/

namespace Alt.List.zip

universe u v

variable {α : Type u} {β : Type v}

/-! ## `byRec` -/

/-- Structural recursion on the pair of lists, with the two empty equations
first so the interesting one only fires when both are nonempty. -/
theorem byRec_eq : ∀ (xs : List α) (ys : List β), byRec xs ys = List.zip xs ys
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: t, b :: s => by simp [byRec, byRec_eq]

/-! ## `viaZipWith` -/

/-- The pairing handed to `List.zipWith`, so the truncation is inherited rather
than re-derived.  `List.zip_eq_zipWith` does the whole job. -/
theorem viaZipWith_eq (xs : List α) (ys : List β) : viaZipWith xs ys = List.zip xs ys := by
  simp [viaZipWith, List.zip_eq_zipWith]

/-! ## `byAccum` -/

/-- A tail-recursive walk over both lists with an explicit accumulator.

The helper is worth reading, because the statement is easy to get wrong: `go`
reverses the **accumulator** as well as the pairs it collects.  So the right
generalisation is

```
go xs ys acc = acc.reverse ++ List.zip xs ys
```

not `(List.zip xs ys).reverse ++ acc` — that version is false, and the
`acc = []` case of the main theorem is exactly where it shows up.

The equation lemmas `byAccum.go.eq_1` (first list empty) and
`byAccum.go.eq_2` (second list empty, guarded by `a = [] → False`) are what the
two degenerate cases use; the cons/cons case goes through `go.eq_def` to expose
the `match`, which `simp` then reduces since both scrutinees are syntactically
conses.  The accumulator-inward shape here is the *same* as the broken
`Foldr.byTailLoop` — see `../Proofs/Foldr.lean` — but this one is correct
because of the final `reverse`. -/
theorem byAccum_eq (xs : List α) (ys : List β) : byAccum xs ys = List.zip xs ys := by
  have go : ∀ (xs : List α) (ys : List β) (acc : List (α × β)),
      byAccum.go xs ys acc = acc.reverse ++ List.zip xs ys := by
    intro xs
    induction xs with
    | nil => intro ys acc; cases ys <;> rw [byAccum.go.eq_1] <;> simp
    | cons a t ih =>
      intro ys acc
      cases ys with
      | nil => rw [byAccum.go.eq_2 (a :: t) acc (by simp)]; simp
      | cons b s => rw [byAccum.go.eq_def]; simp [ih]
  simp only [byAccum]
  rw [go]
  simp

/-! ## `byOfFn` -/

/-- Three steps, none of them an induction.

First, `List.get_eq_getElem` turns the two `List.get` reads — each carrying its
own `Nat.lt_of_lt_of_le i.isLt (min_le_…)` bound proof — into plain `getElem`
notation, so the bound proof stops mattering.

Second, the two sides have to be brought to the *same* `Fin` index.  They differ:
the `ofFn` on the left is indexed by `Fin (min xs.length ys.length)` and the one
produced by `List.ofFn_getElem` on the right by `Fin (xs.zip ys).length`.  These
are equal but not definitionally, and every `rw` over the equality blows up —
`List.length_zip` sits inside a `Fin` binder that a `getElem` bound proof depends
on, so the motive is ill-typed.  `List.ofFn_congr` is the tool that avoids the
`rw` entirely: it casts the index with `Fin.cast` instead of rewriting. -/
private theorem ofFn_eq_zip (xs : List α) (ys : List β) :
    List.ofFn (fun i : Fin (min xs.length ys.length) => (xs[↑i], ys[↑i])) = xs.zip ys := by
  have hlen : (xs.zip ys).length = min xs.length ys.length := List.length_zip
  refine Eq.trans ?_ (List.ofFn_getElem (xs := List.zip xs ys))
  refine Eq.trans ?_ (List.ofFn_congr hlen
    (fun i : Fin (xs.zip ys).length => (List.zip xs ys)[↑i])).symm
  exact List.ofFn_inj.mpr (funext fun i =>
    (@List.getElem_zip _ _ xs ys ↑i (hlen.symm ▸ i.isLt)).symm)

/-- Third step: `List.ofFn_inj` for the closing equality, once both `ofFn`s share
a `Fin` index and only the pointwise value is left — and that is
`List.getElem_zip`. -/
theorem byOfFn_eq (xs : List α) (ys : List β) : byOfFn xs ys = List.zip xs ys := by
  simp only [byOfFn, List.get_eq_getElem]
  exact ofFn_eq_zip xs ys

/-! ## Against the original -/

theorem byRec_eq_orig (xs : List α) (ys : List β) : byRec xs ys = orig xs ys :=
  byRec_eq xs ys

theorem viaZipWith_eq_orig (xs : List α) (ys : List β) : viaZipWith xs ys = orig xs ys :=
  viaZipWith_eq xs ys

theorem byAccum_eq_orig (xs : List α) (ys : List β) : byAccum xs ys = orig xs ys :=
  byAccum_eq xs ys

theorem byOfFn_eq_orig (xs : List α) (ys : List β) : byOfFn xs ys = orig xs ys :=
  byOfFn_eq xs ys

end Alt.List.zip
