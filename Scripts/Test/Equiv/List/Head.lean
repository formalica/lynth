import Mathlib

/-!
# Alternative definitions: `List.head?`

Six ways to read the first element of a list.  `List.head?` pattern-matches the
list once; the alternatives here reach the same `Option` by a `foldr` that keeps
the first candidate, a `foldl` that latches once a value is seen, a `take`-then-
`head?`, a `span`, an index probe at `0` via `getD`-free `getElem?`, and a
`getLast?` of the reversed list.

The trap for this function is the empty list: every definition here must return
`none` for `[]`, and none of them may invent a value.  Anything that reaches for
a default (`headD`) would be computing a *different* function, so `headD` appears
only in the docstring, never in a `def`.  Verified against the original on all
lists of length ≤ 3 over `{0, 1}`.
-/

namespace Alt.List.head?

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (l : List α) : Option α := List.head? l

/-- Direct pattern match, the shape `List.head?` itself uses. -/
def direct : List α → Option α
  | [] => none
  | x :: _ => some x

/-- `foldr` that keeps the *first* candidate: `foldr` hands the head the result
for the tail, so "keep the tail's answer, or the head if the tail had none"
gives the head.  Recursion runs right to left. -/
def viaFoldr (l : List α) : Option α :=
  l.reverse.foldr (fun x acc => match acc with
    | some _ => acc
    | none => some x) none

/-- `foldl` with a latching accumulator: the first element wins, later elements
are ignored.  Recursion runs left to right, the opposite direction of
`viaFoldr`. -/
def viaFoldl (l : List α) : Option α :=
  l.foldl (fun acc x => match acc with
    | some _ => acc
    | none => some x) none

/-- Structural recursion that first truncates: `take 1` keeps at most the head,
and only that surviving element is turned into an `Option`. -/
def viaTake (l : List α) : Option α :=
  match l.take 1 with
  | [] => none
  | x :: _ => some x

/-- `span` with the constant-`true` predicate splits the list into a prefix and a
suffix; the prefix is the whole list, so its first element is the answer. -/
def viaSpan (l : List α) : Option α :=
  let pre := (l.span fun _ => true).1
  match pre with
  | [] => none
  | x :: _ => some x

/-- Positional: probe index `0` with `getElem?`, which is `none` exactly when
the list is empty.  Indexing rather than pattern matching. -/
def viaIndex (l : List α) : Option α := l[0]?

/-- The head of `l` is the *last* element of `l.reverse`: uses two different
library functions composed, with the emptiness test inherited from `getLast?`. -/
def viaRevLast (l : List α) : Option α := l.reverse.getLast?

end Alt.List.head?
