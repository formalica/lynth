import Scripts.Test.Equiv.List.EquivTermList

/-!
# Proofs: every route in `../EquivTermList.lean` returns its argument

`../EquivTermList.lean` collects routes from `a : α` back to `a` that pass through
a *container* on the way, so each theorem has the shape

```lean
theorem viaFoo_eq_self (a : α) : viaFoo a = a
```

**All ten routes are proved here.**

## What the proofs actually needed

Six are one-liners: the `Array` round trip, `ofFn` over `Fin 1`, `flatMap`
duplication, `flatten` of a nested `Option`, `attach` of a singleton, and the
absorbing `scanl`.  The content is uniformly "the detour builds `[a]` (or
`[a, a]`, or `[[a]]`) and the fallback is `a`", so the fallback carries the empty
cases and the `simp` lemma carries the rest.

Two needed a `Bool` case split rather than a `simp`, and the reason is worth
recording: both conclude their result by *either* finding the value *or* falling
back to it, so the `==` test's outcome does not matter.  Concretely,
`viaAssocLookup`'s `lookup` returns the *stored* value, so even a failed lookup
gives `a`; likewise `viaSublistsFind` falls back to `[a]`.  Neither route needs
`[LawfulBEq α]`, which is the opposite of the `EquivTerm` routes that conclude
`x = a` from `x == a`.  Case-splitting on `a == a` and closing both branches by
`simp` is what makes this work for an arbitrary `BEq`.

## The two not proved

`viaTranspose` and `viaPermutationsFind` are both blocked by functions that expose
no equations at all in this Mathlib — `List.transpose` (no `transpose_singleton`,
`transpose_cons`, `transpose_nil` or `transpose_ofFn`) and `List.permutations`
(no `permutations_succ`, no `insertAll`).  Both are `#eval`-confirmed correct; only
the proofs are missing.  See the note at the end of the file.

No `sorry`, no `axiom`, no `native_decide`, no `Classical`.
-/

namespace Equiv
namespace List

universe u

variable {α : Type u}

/-- `attach` a singleton, project out the values, read the head. -/
theorem viaAttachSubtype_eq_self (a : α) : viaAttachSubtype a = a := by
  simp [viaAttachSubtype]

/-- `List α → Array α → List α` and back. -/
theorem viaArrayRoundTrip_eq_self (a : α) : viaArrayRoundTrip a = a := by
  simp [viaArrayRoundTrip]

/-- `flatten` of a nested `Option`, read the head twice. -/
theorem viaNestedOptionFlatten_eq_self (a : α) : viaNestedOptionFlatten a = a := by
  simp [viaNestedOptionFlatten]

/-- `scanl` with an absorbing step over `[a, a]`, read the last.  Note the list
is built from `[a, a]`, not from `a :: l`, so the seed is *not* visibly a member
of the input — the argument has to be that the seed is what ends up last. -/
theorem viaScanlAbsorb_eq_self (a : α) : viaScanlAbsorb a = a := by
  simp [viaScanlAbsorb]

/-- `ofFn` over `Fin 1`. -/
theorem viaOfFn_eq_self (a : α) : viaOfFn a = a := by
  simp [viaOfFn]

/-- `flatMap` duplicating each element, then read index `1`. -/
theorem viaFlatMapDuplicate_eq_self (a : α) : viaFlatMapDuplicate a = a := by
  simp [viaFlatMapDuplicate]

/-- `List.lookup` on an association list.  The result is the *stored* value, so
no `LawfulBEq` is needed — unlike the `EquivTerm` routes that conclude `x = a`
from `x == a`. -/
theorem viaAssocLookup_eq_self [BEq α] (a : α) : viaAssocLookup a = a := by
  cases h : (a == a) with
  | true => simp [viaAssocLookup, h]
  | false => simp [viaAssocLookup, h]

/-- `find?` over the sublists of a singleton.  The sublists of `[a]` are
`[[], [a]]`, so the search finds `[a]` at index `1`, not at index `0` — the `[]`
has to be stepped over, and the step is a *structural* one (`List.beq` on `nil`
is `false` for any `BEq`), so no `LawfulBEq` is needed to clear it.  The `a == a`
that the search lands on is not needed either, since the fallback is `[a]`. -/
theorem viaSublistsFind_eq_self [BEq α] (a : α) : viaSublistsFind a = a := by
  cases h : (a == a) with
  | true => simp [viaSublistsFind, h]
  | false => simp [viaSublistsFind, h]

/-! ## The final routes

The transpose proof evaluates the singleton through `List.transpose.go`; the
permutations proof uses the exposed `permutationsAux` equations.  The search
fallback stores `[a]`, so no `LawfulBEq` assumption is needed. -/

/-- Transposing the one-row singleton yields the same singleton. -/
private theorem transpose_go_singleton (a : α) :
    List.transpose.go [a] (#[] : Array (List α)) = #[[a]] := by
  unfold List.transpose.go
  rw [Array.mapM_empty]
  rfl

private theorem transpose_singleton (a : α) :
    List.transpose ([[a]] : List (List α)) = [[a]] := by
  simp [List.transpose, transpose_go_singleton]

theorem viaTranspose_eq_self (a : α) : viaTranspose a = a := by
  simp [viaTranspose, transpose_singleton]

/-- The singleton is the only permutation returned; either search outcome gives
the same stored or fallback value. -/
theorem viaPermutationsFind_eq_self [BEq α] (a : α) : viaPermutationsFind a = a := by
  simp only [viaPermutationsFind, List.permutations, List.permutationsAux_cons,
    List.permutationsAux_nil]
  cases h : (a == a) <;> simp [h]

end List
end Equiv
