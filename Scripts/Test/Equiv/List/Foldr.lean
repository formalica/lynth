import Mathlib

/-!
# Alternative definitions: `List.foldr`

The mirror image of `AltListFoldl`, and a good illustration of which
transformations of a fold need hypotheses.  Every alternative below is valid
for an arbitrary `f : α → β → β`; none of them reorders the elements or
reassociates the chain of calls.

* `byRec` — structural recursion, the textbook definition;
* `byTailLoop` — two tail-recursive loops rather than one: a push phase that
  moves the elements onto a stack, and a pop phase that applies `f` on the way
  back out.  A single accumulator is not enough, and the definition below says
  why;
* `byRevFoldl` — reverse the list and use `List.foldl`, which consumes the
  reversed list back to front and therefore threads the accumulator in the
  same order `List.foldr` would;
* `byFinRange` — a `List.foldl` over `List.finRange.reverse`, i.e. over the
  positions from the back of the list to the front.

What would *not* be safe: folding the list in its original order with
`List.foldl` (that computes a left-nested chain, not a right-nested one), or
reordering elements.  Both are avoided here.
-/

namespace Alt.List.foldr

universe u v

variable {α : Type u} {β : Type v}

/-- The original, kept as the reference point. -/
def orig (f : α → β → β) (init : β) (l : List α) : β := List.foldr f init l

/-- Structural recursion: apply `f` to the head and to the recursive result on
the tail.  The accumulator is only reached at the very end, which is the
defining feature of a right fold. -/
def byRec (f : α → β → β) (init : β) : List α → β
  | [] => init
  | a :: t => f a (byRec f init t)

/-- A genuine tail-recursive right fold, and the price of that: it needs an
explicit stack.  `List.foldr` builds its result *outwards* — the head of the list
is applied last, to whatever the tail produced — whereas any single loop that
walks the list front to back has already fixed the accumulator by the time it
reaches the tail.  So this splits the job in two: `go` pushes the elements onto
`stk` front to back, and `unwind` pops them, applying `f` innermost first.  Both
loops have every recursive call in tail position and decrease structurally, which
is the shape a compiler produces for a right fold. -/
def byTailLoop (f : α → β → β) (init : β) (l : List α) : β := go l [] init where
  /-- Pop phase: apply `f` to the pending elements, innermost first. -/
  unwind : List α → β → β
    | [], acc => acc
    | a :: stk, acc => unwind stk (f a acc)
  /-- Push phase: move the elements of the first list onto the stack. -/
  go : List α → List α → β → β
    | [], stk, acc => unwind stk acc
    | a :: t, stk, acc => go t (a :: stk) acc

/-- `List.foldl` over the reversed list.  `List.foldl` consumes its argument
front to back, so feeding it `l.reverse` makes it visit `l` from the back, and
`f a acc` threads the accumulator in exactly the order `List.foldr` needs.
Valid for arbitrary `f` — the elements are never reordered relative to each
other, only the direction of traversal changes. -/
def byRevFoldl (f : α → β → β) (init : β) (l : List α) : β :=
  List.foldl (fun acc a => f a acc) init l.reverse

/-- Index-driven: a left fold over the positions of the list taken in reverse,
i.e. `l.length - 1` down to `0`, fetching each element with `List.get`.  The
recursion is over an index list, not over `l`. -/
def byFinRange (f : α → β → β) (init : β) (l : List α) : β :=
  List.foldl (fun acc i => f (l.get i) acc) init (List.finRange l.length).reverse

end Alt.List.foldr
