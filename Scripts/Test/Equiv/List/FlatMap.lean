import Mathlib

/-!
# Alternative definitions: `List.flatMap`

`List.flatMap` is `List.map` followed by a concatenation, and the four
alternatives below make that visible in four different ways.  They also show
that "flat" admits several genuinely different accumulation strategies:

* structural recursion with `++` (`byRec`);
* a `foldl` consing whole *lists* onto the front of the accumulator, plus a
  `reverse` (`byFoldlCons`);
* a `foldl` appending whole lists onto the *back* (`byFoldlAppend`) — same
  answer, quadratic time, and the reason `byRec` cannot be written this way
  without a cost argument;
* a `map`/`flatten` pair that makes the two-phase structure explicit
  (`viaFlattenMap`);
* a fold over `List.finRange` reading with `List.get` (`byFinRange`).

Note the difference from `AltListMap`: here the accumulated objects are
`List β`, not `β`, so the reversal in `byFoldlCons` moves whole blocks around
rather than single elements.
-/

namespace Alt.List.flatMap

universe u v

variable {α : Type u} {β : Type v}

/-- The original, kept as the reference point. -/
def orig (f : α → List β) (l : List α) : List β := List.flatMap f l

/-- Structural recursion: the head contributes its own block, the tail
contributes the recursive result, and the two are appended. -/
def byRec (f : α → List β) : List α → List β
  | [] => []
  | a :: t => f a ++ byRec f t

/-- A `foldl` consing whole blocks onto the front of the accumulator.  The
blocks end up in reverse order, so one `reverse` puts them back — but each
block must also be reversed *as it is consed*, since the final `reverse` would
otherwise flip the order inside every block as well. -/
def byFoldlCons (f : α → List β) (l : List α) : List β :=
  List.foldl (fun acc a => (f a).reverse ++ acc) ([] : List β) l |>.reverse

/-- A `foldl` appending whole blocks onto the back.  Blocks stay in order with
no `reverse` at all, at the price of re-copying the accumulator every step. -/
def byFoldlAppend (f : α → List β) (l : List α) : List β :=
  List.foldl (fun acc a => acc ++ f a) ([] : List β) l

/-- The two-phase reading taken literally: `List.map` produces a list of
lists, `List.flatten` concatenates them.  Reuses both as substeps but pins down
exactly where the type change happens. -/
def viaFlattenMap (f : α → List β) (l : List α) : List β :=
  List.flatten (List.map f l)

/-- Index-driven: fold over the positions and read each element with
`List.get`, so the source list is addressed by index rather than by
destructuring. -/
def byFinRange (f : α → List β) (l : List α) : List β :=
  List.foldl (fun acc i => acc ++ f (l.get i)) ([] : List β) (List.finRange l.length)

end Alt.List.flatMap
