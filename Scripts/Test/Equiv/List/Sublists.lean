import Mathlib

/-!
# Alternative definitions: `List.sublists`

`List.sublists l` is the list of all sublists of `l`, i.e. all lists `s` with
`s.Sublist l`, in the particular order the definition produces.

Three other routes, all resting on the cons equation — which is worth saying
plainly, because the order is forced.  A sublist of `a :: t` either avoids `a`
or has `a` as its first element, and the definition lists the ones that avoid it
first.  Any correct rendering has to reproduce that split in that order, so what
varies is the combinator used to perform the "cons onto every sublist" step:

* `byConsEq` — `List.flatMap`, the shape `List.sublists_cons` is stated in once
  the `do` notation is expanded;
* `byConsPlain` — `List.map` followed by `List.flatten`, so the two-step shape is
  visible rather than folded into one combinator;
* `byAppendStep` — the same interleaving, but the "two-element bundle" is built
  with a `map` and the bundles are concatenated by a `foldr` with `++`, rather
  than combined in one go by `flatMap`.  This is what instantiating
  `List.sublists_append` at the split `l = [a] ++ t` amounts to after the
  `do` notation is expanded by hand.

A fourth shape was tried and is **not** correct: generating the family as the
contiguous windows `l.take i ++ l.drop i` gives only the `2^(n-1)` contiguous
sublists, missing `[1, 3]` in `l = [1, 2, 3]`.
-/

namespace Alt.List.sublists

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (l : List α) : List (List α) := l.sublists

/-- The cons equation, built from `List.sublists_cons` with the `do` notation
spelled out as `flatMap`: every sublist of `a :: t` is either a sublist of `t`, or
`a` consed onto one. -/
def byConsEq : List α → List (List α)
  | [] => [[]]
  | a :: t => (byConsEq t).flatMap (fun x => [x, a :: x])

/-- The same equation, but combining with `List.flatten` over a `List.map` rather
than with `flatMap`, so the two-step shape is visible. -/
def byConsPlain : List α → List (List α)
  | [] => [[]]
  | a :: t => ((byConsPlain t).map (fun x => [x, a :: x])).flatten

/-- The same split, but the "bundle `x` together with `a :: x`" step is done by
a `List.map` and the bundles are then concatenated by a `foldr` with `++`,
instead of being combined in one go by `flatMap`. -/
def byAppendStep : List α → List (List α)
  | [] => [[]]
  | a :: t =>
    ((byAppendStep t).map (fun x => [x, a :: x])).foldr
      (fun bundle acc => bundle ++ acc) []

end Alt.List.sublists
