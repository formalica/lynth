import Mathlib

/-!
# Alternative definitions: `List.isEmpty`

Six ways to ask whether a list has no elements.  `List.isEmpty` is a one-step
pattern match; the alternatives compare the length against `0`, pattern match on
`head?`, use `List.filter` on a constant-true predicate, use `drop 1` and check
whether anything came back, and use `List.any` negated.

The trap is the `Bool` vs `Prop` boundary.  `isEmpty` returns `Bool`, so
`l.isEmpty = true` is a `BEq` on `Bool` and `(decide (l = []))` is a `decide`
over a `Prop` — they agree, but writing `def bad (l : List α) : Bool := l = []`
does not typecheck, and writing `l.length = 0` produces a `Prop` that has to be
pushed through `decide`.  All definitions below return `Bool` and were checked
against the original on all lists of length ≤ 3 over `{0, 1}`.
-/

namespace Alt.List.isEmpty

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (l : List α) : Bool := List.isEmpty l

/-- Direct pattern match, the shape `List.isEmpty` itself uses. -/
def direct : List α → Bool
  | [] => true
  | _ :: _ => false

/-- Emptiness as a length comparison, pushed through `decide` to get a `Bool`.
No pattern match on the list at all. -/
def viaLength (l : List α) : Bool := decide (l.length = 0)

/-- Emptiness as "the head is missing": `head?` is `none` exactly on `[]`.
Reuses a different library function as the emptiness oracle. -/
def viaHead (l : List α) : Bool := (l.head?).isNone

/-- Filter with the constant-`true` predicate, which rebuilds the list, and then
ask whether the rebuild is empty.  Pointless work, but a different route. -/
def viaFilter (l : List α) : Bool := (l.filter fun _ => true).isEmpty

/-- `take 1` and measure: the list is empty iff its first one-element chunk has
length `0`.  A truncation-based reading rather than a head read. -/
def viaTake (l : List α) : Bool := (l.take 1).length == 0

/-- `any` with the constant-`true` predicate is `true` exactly when some element
exists; negate it.  A search-shaped emptiness test rather than a scan. -/
def viaAny (l : List α) : Bool := (l.any fun _ => true) == false

/-- `rev` twice, then test: composition of three library calls, with the
emptiness question asked of a rebuilt list. -/
def viaRevRev (l : List α) : Bool := (l.reverse.reverse).isEmpty

end Alt.List.isEmpty
