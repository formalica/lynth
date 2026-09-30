import Mathlib

/-!
# Alternative definitions: `List.map`

`List.map` is the shortest function in this family, which makes it the cleanest
place to see what "an alternative implementation" can possibly mean: there is no
arithmetic to disguise, so the only thing left to vary is *how the recursion is
organised*.  The four alternatives below differ along four genuinely different
axes:

* structural recursion driven by the equation compiler (`byRec`);
* a `foldl` that conses each image onto the front of the accumulator, so the
  result comes out backwards and one `reverse` undoes it (`byFoldlCons`);
* the `List.reverseRecOn` recursor, which grows the list by appending rather
  than by consing (`byReverseRec`);
* `List.ofFn` over `Fin` indices: index-driven rather than list-driven, with
  no recursion over the list at all (`byOfFn`).

Nothing here assumes anything about `f` — no injectivity, no surjectivity — and
`byFoldlCons`/`byReverseRec` cost more memory than they need to, which is the
point: they are a different *plan*, not a faster one.
-/

namespace Alt.List.map

universe u v

variable {α : Type u} {β : Type v}

/-- The original, kept as the reference point. -/
def orig (f : α → β) (l : List α) : List β := List.map f l

/-- Structural recursion: cons the image of the head onto the recursive result
on the tail.  `List.map` itself is written with `List.rec`; this is the same
shape handed to the equation compiler, and is the most direct thing there is
to write. -/
def byRec (f : α → β) : List α → List β
  | [] => []
  | a :: t => f a :: byRec f t

/-- `foldl` consing onto a reversed accumulator.  The fold runs *left to right*
and the output runs *right to left*, so a single `reverse` restores the order.
The mirror image of `byRec` in both directions. -/
def byFoldlCons (f : α → β) (l : List α) : List β :=
  (List.foldl (fun acc a => f a :: acc) ([] : List β) l).reverse

/-- The `List.reverseRecOn` recursor: instead of recursing on the tail, it
recurses on the *whole* list so far and extends it by a singleton.  That
forces `++` (and hence quadratic time) where `byRec` conses for free — a
different decomposition of the same computation. -/
def byReverseRec (f : α → β) (l : List α) : List β :=
  l.reverseRecOn [] (fun _ a ih => ih ++ [f a])

/-- Index-driven: build the answer from `Fin` indices with `List.ofFn` and read
each source element with `List.get`.  No recursion on the list at all, and the
recursion that `List.ofFn` does internally is on the (always finite) index
type. -/
def byOfFn (f : α → β) (l : List α) : List β :=
  List.ofFn (fun i : Fin l.length => f (l.get i))

end Alt.List.map
