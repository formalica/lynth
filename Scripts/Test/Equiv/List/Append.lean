import Mathlib

/-!
# Alternative definitions: `List.append` (`++`)

Append is the one function here that `List` is *defined* by, so an alternative
cannot simply recurse structurally — that would be the original.  Three routes
that genuinely differ:

* `byFoldr` — `List.foldr` with cons, so the recursion is performed by the fold
  combinator with the second list as the seed;
* `byMapCons` — bundle each element of the first list into a singleton with
  `map`, then concatenate the bundles with a `foldr` using `++`.  The recursion is
  performed by `foldr` over the *bundles* rather than over the elements;
* `bySplitFold` — recursion over the *second* list, appending each of its
  elements to the end of the first.  The roles of the two arguments are
  interchanged relative to the original.

Append is the one function here that `List` is *defined* by, so the
alternatives necessarily stay close to it: what can vary is which combinator
carries the recursion (`foldr` with cons, `foldr` with `++` over bundles, or a
`foldl` over the other argument), not the order of traversal.
-/

namespace Alt.List.append

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (l₁ l₂ : List α) : List α := l₁ ++ l₂

/-- `List.foldr` with cons, seeded by the second list: the recursion over the
first list is carried out by the fold combinator rather than by the definition
of `++`. -/
def byFoldr (l₁ l₂ : List α) : List α := List.foldr (fun a acc => a :: acc) l₂ l₁

/-- Bundle each element of the first list into a singleton with `map`, then
concatenate the bundles with a `foldr` using `++`: the recursion is carried out
by `foldr` over the bundles rather than over the elements. -/
def byMapCons (l₁ l₂ : List α) : List α :=
  (l₁.map (fun a => [a])).foldr (fun bundle acc => bundle ++ acc) l₂

/-- Recursion over the *second* list, appending each of its elements to the end
of the first.  The original recurses on the first argument and simply returns
the second; here the recursion is on the other argument and the first plays the
role of the running result. -/
def bySplitFold (l₁ l₂ : List α) : List α :=
  List.foldl (fun acc a => acc ++ [a]) l₁ l₂

end Alt.List.append
