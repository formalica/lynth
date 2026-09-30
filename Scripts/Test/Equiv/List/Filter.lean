import Mathlib

/-!
# Alternative definitions: `List.filter`

`List.filter` is the first function here whose output length is *not* the input
length, so the alternatives have to differ in something more interesting than
traversal order.  Four of them:

* structural recursion (`byRec`);
* a `foldl` with a reversed accumulator (`byFoldlRev`) — the same accounting
  as for `map`, but the accumulator is now updated conditionally;
* a fold over `List.finRange`, reading elements with `List.get`
  (`byFinRange`) — the search is over *positions* rather than over elements;
* a re-expression through `List.filterMap` (`viaFilterMap`) — keep-or-drop is
  turned into some-or-nothing.

The predicate is a `Bool`-valued function, so every `if` here is a `Bool`
test; no `Decidable` instance is needed or used, and nothing is assumed about
the predicate beyond its type.
-/

namespace Alt.List.filter

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (p : α → Bool) (l : List α) : List α := List.filter p l

/-- Structural recursion: the head is kept exactly when the predicate holds,
and the tail is handled the same way. -/
def byRec (p : α → Bool) : List α → List α
  | [] => []
  | a :: t => if p a then a :: byRec p t else byRec p t

/-- A left fold that conses each kept element onto the *front* of the
accumulator, followed by one `reverse`.  The kept elements are in the same
order relative to each other as before, and their order is restored at the
end. -/
def byFoldlRev (p : α → Bool) (l : List α) : List α :=
  (List.foldl (fun acc a => if p a then a :: acc else acc) ([] : List α) l).reverse

/-- Index-driven: fold over the positions `0 … l.length - 1` and fetch each
element with `List.get`.  The fold visits the list front to back but addresses
it by index, which is a genuinely different access pattern from the
element-driven folds above. -/
def byFinRange (p : α → Bool) (l : List α) : List α :=
  List.foldl (fun acc i => if p (l.get i) then l.get i :: acc else acc)
    ([] : List α) (List.finRange l.length) |>.reverse

/-- Through `List.filterMap`, turning the keep-or-drop decision into a
some-or-nothing one.  Reuses a different `List` function as a substep, and
adds the encoding of the predicate as an `Option`. -/
def viaFilterMap (p : α → Bool) (l : List α) : List α :=
  List.filterMap (fun a => if p a then some a else none) l

end Alt.List.filter
