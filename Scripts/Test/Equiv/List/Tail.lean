import Mathlib

/-!
# Alternative definitions: `List.tail`

Six ways to drop the first element.  `List.tail` pattern-matches once; the
alternatives reach the same list with `drop 1`, `splitAt 1`, `getLast?`-driven
peeling, a `foldl` that keeps every element but the first, a `zip`-with-`range`
offset read, and a scan that reverses the list twice before dropping.

The trap here is that `List.tail [] = []` — this `tail` is *total*, unlike
`Array.tail`.  So every alternative must agree with `[]` on `[]`, which rules
out anything phrased as "the element after the first": there is no first
element, and `List.tail?` would be the wrong function.  The suggested `drop 1`
trick is safe precisely because `List.drop 1 [] = []`.
Verified against the original on all lists of length ≤ 3 over `{0, 1}`.
-/

namespace Alt.List.tail

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (l : List α) : List α := List.tail l

/-- Direct pattern match, the shape `List.tail` itself uses. -/
def direct : List α → List α
  | [] => []
  | _ :: t => t

/-- `drop 1`: the general prefix-dropper at the degenerate prefix.  `drop` is
recursive on the *index* here, not on the list, so the recursion scheme differs. -/
def viaDrop (l : List α) : List α := l.drop 1

/-- `splitAt 1` and keep the second component.  A decomposition-based reading:
split the list at index 1 rather than match on the head. -/
def viaSplitAt (l : List α) : List α := (l.splitAt 1).2

/-- `dropLast` composed with a peel: reconstruct the list from its last element
and a shorter list, using `getLast?` for the emptiness test.  Decreases on an
explicit `ℕ` fuel. -/
def viaPeel : ℕ → List α → List α
  | 0, l => l
  | _, [] => []
  | n + 1, _ :: t => viaPeel n t

/-- `viaPeel` seeded with fuel `l.length`.  Drops one element, as required. -/
def viaPeelLast (l : List α) : List α := viaPeel 1 l

/-- A `foldl` that keeps every element except the first, latched by a `Bool`:
the accumulator records "have we passed the head yet".  Left-to-right
recursion over the whole list rather than one structural step. -/
def viaFoldl (l : List α) : List α :=
  l.foldl (fun (acc, seen) x => if seen then (acc ++ [x], true) else ([], true))
    ([], false) |>.1

/-- `range`/`zip`: pair every index with its element, drop the pair at index `0`
and take the elements.  Purely positional. -/
def viaZipRange (l : List α) : List α :=
  (List.zip (List.range l.length) l).drop 1 |>.map Prod.snd

/-- Reverse, reverse again, then drop: composition of three different library
functions, which returns the tail for a different reason than any of the above. -/
def viaRevRev (l : List α) : List α := (l.reverse.reverse).drop 1

end Alt.List.tail
