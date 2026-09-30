import Mathlib

/-!
# Alternative definitions: `List.filterMap`

`List.filterMap` threads an `Option` through the recursion, so it is the
interesting middle case between `List.map` and `List.filter`: the function may
*change the type* and *drop elements at the same time*.  The five alternatives
below vary the recursion, the traversal direction, and the combinator used to
express "keep or drop":

* structural recursion, matching on the `Option` (`byRec`);
* a `foldl` with a reversed accumulator (`byFoldlRev`);
* a fold over `List.finRange` reading with `List.get` (`byFinRange`);
* through `List.flatMap`, where each surviving element is a singleton list
  (`viaFlatMap`);
* through `List.map` followed by `List.filterMap id` (`viaMapThenId`), i.e.
  keeping the `Option`s as data and only decoding them at the very end.

None of these touch the `Option` other than by matching on it, so the
rejection branch costs nothing extra in any of them.
-/

namespace Alt.List.filterMap

universe u v

variable {α : Type u} {β : Type v}

/-- The original, kept as the reference point. -/
def orig (f : α → Option β) (l : List α) : List β := List.filterMap f l

/-- Structural recursion, matching on the `Option` returned for the head.  The
two branches differ only in whether the decoded element is consed. -/
def byRec (f : α → Option β) : List α → List β
  | [] => []
  | a :: t =>
    match f a with
    | some b => b :: byRec f t
    | none => byRec f t

/-- A `foldl` that conses each decoded element onto the front of the
accumulator, with a single `reverse` at the end.  Left fold, reversed output —
the opposite direction from `byRec`. -/
def byFoldlRev (f : α → Option β) (l : List α) : List β :=
  List.foldl
      (fun acc a => match f a with
        | some b => b :: acc
        | none => acc) ([] : List β) l
    |>.reverse

/-- Index-driven: walk the positions with `List.finRange` and read the elements
with `List.get`, keeping the ones the function accepts. -/
def byFinRange (f : α → Option β) (l : List α) : List β :=
  List.foldl
      (fun acc i => match f (l.get i) with
        | some b => b :: acc
        | none => acc) ([] : List β) (List.finRange l.length)
    |>.reverse

/-- Through `List.flatMap`: every accepted element contributes a one-element
list and every rejected one contributes the empty list, so concatenation does
the filtering.  A different combinator, and a different account of why the
output is shorter than the input. -/
def viaFlatMap (f : α → Option β) (l : List α) : List β :=
  List.flatMap (fun a => match f a with
    | some b => [b]
    | none => []) l

/-- A two-stage pipeline: `List.map` builds a list of `Option β` (so the output
length still matches the input), and `List.filterMap id` decodes it in one
more pass.  Keeps the intermediate list explicit instead of fusing the two
steps. -/
def viaMapThenId (f : α → Option β) (l : List α) : List β :=
  List.filterMap id (List.map f l)

end Alt.List.filterMap
