import Mathlib

/-!
# Alternative definitions: `List.foldl`

`List.foldl` is where the alternatives have to be genuinely careful: several
plausible-looking rewrites are *wrong* unless the combining function happens to
be associative, and this file is the record of which rewrites are safe
regardless.

Safe for an arbitrary `f : α → β → α`:

* `byRec` — structural recursion; the textbook definition;
* `byTailLoop` — the same computation as a tail-recursive loop with an
  explicit accumulator;
* `byFoldrRev` — `List.foldr` applied to the reversed list, with the operands
  of `f` swapped.  This works for *every* `f`: `List.foldr` just reassociates
  an already left-nested chain of calls, reading the list backwards instead
  of forwards.  No associativity of `f` is used — only that a list can be
  reversed;
* `byFinRange` — a fold over `List.finRange` that reads the elements with
  `List.get`, so the fold is over positions rather than over the list itself.

The trap: a "parallel pairwise reduction" fold would need `f` to be
associative, and reordering the elements would need it to commute too.  Neither
is assumed anywhere below, which is why every alternative here processes the
elements in the original order.
-/

namespace Alt.List.foldl

universe u v

variable {α : Type u} {β : Type v}

/-- The original, kept as the reference point. -/
def orig (f : α → β → α) (init : α) (l : List β) : α := List.foldl f init l

/-- Structural recursion: apply `f` to the accumulator and the head, then
recurse on the tail with the new accumulator.  The accumulator is threaded
through the recursion, so the function is not tail-recursive. -/
def byRec (f : α → β → α) (init : α) : List β → α
  | [] => init
  | a :: t => byRec f (f init a) t

/-- The same chain of `f` calls, but as a tail-recursive loop: the accumulator
lives in a `where` helper and every recursive call is in tail position.  Same
result as `byRec`, different evaluation plan (and a different stack depth for
long lists). -/
def byTailLoop (f : α → β → α) (init : α) (l : List β) : α := go l init where
  go : List β → α → α
    | [], acc => acc
    | a :: t, acc => go t (f acc a)

/-- A left fold expressed with `List.foldr` by feeding it the reversed list
and swapping the arguments of `f`.  `List.foldr` walks right to left, so
reversing first makes it visit the elements left to right and rebuild exactly
the same left-nested chain.  Valid for arbitrary `f` — no associativity, no
commutativity, no reordering of the elements. -/
def byFoldrRev (f : α → β → α) (init : α) (l : List β) : α :=
  List.foldr (fun a acc => f acc a) init l.reverse

/-- Index-driven: fold over the positions `0 … l.length - 1` and fetch each
element with `List.get`.  The elements are visited in order, but the recursion
is over the index list rather than over `l` itself. -/
def byFinRange (f : α → β → α) (init : α) (l : List β) : α :=
  List.foldl (fun acc i => f acc (l.get i)) init (List.finRange l.length)

end Alt.List.foldl
