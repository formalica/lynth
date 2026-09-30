import Scripts.Test.Equiv.List.Append

/-!
# Proofs: `List.append` alternatives are equal to the original

All three alternatives in `../Append.lean` are proved.  Append is the function
`List` is *defined* by, so there is no equation theorem to lean on and no
`List.append_eq` to instantiate: all three are established by hand from
`rfl` on the two base cases and one induction step each.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.append

universe u

variable {α : Type u}

/-! ## `byFoldr` -/

/-- `List.foldr` with cons and the second list as the seed *is* append.  No
equation theorem is needed: on a cons the fold reduces to a cons on both sides
and the induction hypothesis is the whole problem. -/
private theorem foldr_append : ∀ (l₁ l₂ : List α),
    List.foldr (fun a acc => a :: acc) l₂ l₁ = l₁ ++ l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; rfl
  | cons a t ih =>
    intro l₂
    rw [List.foldr_cons]
    exact congrArg (fun L => a :: L) (ih l₂)

theorem byFoldr_eq_append (l₁ l₂ : List α) : byFoldr l₁ l₂ = l₁ ++ l₂ := foldr_append l₁ l₂

/-! ## `bySplitFold` -/

/-- Appending each element of the second list to the end of the first.  The
induction is on the *second* list, and the step is closed with append
associativity. -/
private theorem split_fold : ∀ (l₂ : List α) (l₁ : List α),
    List.foldl (fun acc a => acc ++ [a]) l₁ l₂ = l₁ ++ l₂ := by
  intro l₂
  induction l₂ with
  | nil => intro l₁; rw [List.foldl_nil, List.append_nil]
  | cons b t ih =>
    intro l₁
    rw [List.foldl_cons, ih, List.append_assoc, List.cons_append]
    rfl

theorem bySplitFold_eq_append (l₁ l₂ : List α) : bySplitFold l₁ l₂ = l₁ ++ l₂ :=
  split_fold l₂ l₁

/-! ## `byMapCons` -/

/-- Bundling each element into a singleton and concatenating the bundles.  The
`foldr` here is over the *bundles*, so on a cons the step is an append rather
than a cons and the step closes by `rfl`. -/
private theorem map_cons_fold : ∀ (l₁ l₂ : List α),
    (l₁.map (fun a => [a])).foldr (fun bundle acc => bundle ++ acc) l₂ = l₁ ++ l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; rfl
  | cons a t ih =>
    intro l₂
    exact congrArg (fun L => [a] ++ L) (ih l₂)

theorem byMapCons_eq_append (l₁ l₂ : List α) : byMapCons l₁ l₂ = l₁ ++ l₂ :=
  map_cons_fold l₁ l₂

/-! ## Against the original -/

theorem byFoldr_eq_orig (l₁ l₂ : List α) : byFoldr l₁ l₂ = orig l₁ l₂ := foldr_append l₁ l₂

theorem bySplitFold_eq_orig (l₁ l₂ : List α) : bySplitFold l₁ l₂ = orig l₁ l₂ :=
  split_fold l₂ l₁

theorem byMapCons_eq_orig (l₁ l₂ : List α) : byMapCons l₁ l₂ = orig l₁ l₂ := map_cons_fold l₁ l₂

end Alt.List.append
