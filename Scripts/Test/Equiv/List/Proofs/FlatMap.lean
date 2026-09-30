import Scripts.Test.Equiv.List.FlatMap

/-!
# Proofs: `List.flatMap` alternatives are equal to the original

All five alternatives in `../FlatMap.lean` are proved equal to
`List.flatMap` here.

Note the orientation of the two fold helpers in this file, and that they differ.
For `byFoldlAppend` — which appends whole blocks onto the *back* of the
accumulator — the generalised statement puts the seed on the **left**:

```
l.foldl (fun acc a => acc ++ f a) acc = acc ++ l.flatMap f
```

Getting that the wrong way round (seed on the right) produces a statement that is
simply false, and the failure looks like a tactic problem rather than a statement
problem: the goal becomes `flatMap f t ++ (acc ++ f a) = f a ++ (flatMap f t ++ acc)`,
which is the commutativity of `++` on a list it does not hold for.
-/

namespace Alt.List.flatMap

universe u v

variable {α : Type u} {β : Type v}

/-! ## `byRec` -/

/-- Structural recursion with `++`: the head contributes its own block, the tail
the recursive result, and the two are appended. -/
theorem byRec_eq (f : α → List β) : ∀ (l : List α), byRec f l = List.flatMap f l
  | [] => rfl
  | a :: t => by simp [byRec, byRec_eq]

/-! ## `viaFlattenMap` -/

/-- The two-phase reading taken literally.  Mathlib has no `List.flatten_map`, so
the identification is proved here by the same induction as `byRec`. -/
private theorem flatten_map_eq (f : α → List β) : ∀ (l : List α),
    (List.map f l).flatten = List.flatMap f l
  | [] => rfl
  | a :: t => by
    simp only [List.map_cons, List.flatten_cons, flatten_map_eq, List.flatMap_cons]

theorem viaFlattenMap_eq (f : α → List β) (l : List α) :
    viaFlattenMap f l = List.flatMap f l := flatten_map_eq f l

/-! ## `byFoldlAppend` -/

/-- Blocks stay in order with no `reverse` at all, at the price of re-copying
the accumulator every step.  The seed goes on the left of the equation; see the
file docstring for why the other orientation is false. -/
private theorem foldl_append_gen (f : α → List β) (acc : List β) (l : List α) :
    l.foldl (fun acc a => acc ++ f a) acc = acc ++ l.flatMap f := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih => simp only [List.foldl_cons, ih, List.flatMap_cons, List.append_assoc]

theorem byFoldlAppend_eq (f : α → List β) (l : List α) :
    byFoldlAppend f l = List.flatMap f l := by
  simp only [byFoldlAppend, foldl_append_gen, List.nil_append]

/-! ## `byFoldlCons` -/

/-- Each block is reversed as it is consed, and the accumulator lands on the
**right**: consing `(f a).reverse` onto the front means the head's block ends up
innermost once the final `reverse` runs, so the seed has to sit outside the
flattened result.  Compare `foldl_append_gen` above, whose seed goes on the
*left*.  The cons case closes by `reverse_append` putting the two reversals
together, then `append_assoc` re-associating them to the shape of the
induction hypothesis. -/
private theorem foldl_cons_gen (f : α → List β) (acc : List β) (l : List α) :
    l.foldl (fun acc a => (f a).reverse ++ acc) acc = (List.flatMap f l).reverse ++ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, ih, List.flatMap_cons, List.reverse_append]
    rw [← List.append_assoc]

theorem byFoldlCons_eq (f : α → List β) (l : List α) :
    byFoldlCons f l = List.flatMap f l := by
  simp only [byFoldlCons, foldl_cons_gen, List.append_nil, List.reverse_reverse]

/-! ## `byFinRange` -/

/-- The index list visits every position once, so `List.get` reads at each of
them give `l` back as a `map`. -/
private theorem map_get_finRange (l : List α) :
    List.map l.get (List.finRange l.length) = l :=
  (List.ofFn_eq_map (f := l.get)).symm.trans (List.ofFn_get l)

/-- `List.foldl_map` moves the reads out of the step function and the index list
collapses, which leaves the very fold `byFoldlAppend` already proved. -/
private theorem foldl_finRange (h : List β → α → List β) (l : List α) (acc : List β) :
    List.foldl (fun a i => h a (l.get i)) acc (List.finRange l.length) = List.foldl h acc l := by
  rw [← List.foldl_map, map_get_finRange]

theorem byFinRange_eq (f : α → List β) (l : List α) : byFinRange f l = List.flatMap f l := by
  simp only [byFinRange]
  rw [foldl_finRange (fun acc x => acc ++ f x) l []]
  exact byFoldlAppend_eq f l

/-! ## Against the original -/

theorem byRec_eq_orig (f : α → List β) (l : List α) : byRec f l = orig f l :=
  byRec_eq f l

theorem viaFlattenMap_eq_orig (f : α → List β) (l : List α) : viaFlattenMap f l = orig f l :=
  viaFlattenMap_eq f l

theorem byFoldlAppend_eq_orig (f : α → List β) (l : List α) : byFoldlAppend f l = orig f l :=
  byFoldlAppend_eq f l

theorem byFoldlCons_eq_orig (f : α → List β) (l : List α) : byFoldlCons f l = orig f l :=
  byFoldlCons_eq f l

theorem byFinRange_eq_orig (f : α → List β) (l : List α) : byFinRange f l = orig f l :=
  byFinRange_eq f l

end Alt.List.flatMap
