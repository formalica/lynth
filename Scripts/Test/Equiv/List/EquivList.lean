import Mathlib

/-!
# `Equiv.List` — functions that return their input unchanged

A collection of `def`s of type `List α → List α` whose value is *always* the
argument they were given, but which get there by doing redundant work first.
Every one of these satisfies

```lean
def f (l : List α) : List α := ...
-- and  f l  is equal to  l
```

The point is to have a supply of "compute something, then discard it" shapes for
testing: rewriters, simplifiers, and folding/unfolding experiments need target
terms that *look* like they change but do not, and the cheapest such terms are
these.

They are deliberately wasteful.  `viaRevRev` is two full passes, `viaTakeAppend`
materialises a list twice the length and throws half of it away.  Do not copy any
of these into performance-sensitive code — they are here to be analysed, not
used.

## Groups

| group | shape | needs |
|---|---|---|
| A | structural no-ops | — |
| B | fold identities | — |
| C | decomposition round-trips | — |
| D | needs a witness element | — |
| E | membership/erase round-trips | `[DecidableEq α]` |

## A note on the trivial cases

A few entries (`viaAppendNil`, `viaDropZero`, `viaMapId`) are *definitionally*
equal to the identity — the elaborator discharges them with `rfl`, because there
is no work to do.  They are still included deliberately: the contrast between
"discharged by `rfl`" and "needs a real traversal" (`viaTakeLength`,
`viaFilterTrue`) is itself the interesting measurement when testing a rewriter.
-/

namespace Equiv.List

/-! ## Group A — structural no-ops -/

/-- Append nothing.  Definitional identity. -/
def viaAppendNil (l : List α) : List α := l ++ []

/-- Drop nothing.  Definitional identity. -/
def viaDropZero (l : List α) : List α := l.drop 0

/-- Apply the identity function to every element.  Definitional identity. -/
def viaMapId (l : List α) : List α := l.map id

/-- Take the whole list: a real `Nat` comparison per element, but the same
answer. -/
def viaTakeLength (l : List α) : List α := l.take l.length

/-- Keep everything: a real `Bool` test per element. -/
def viaFilterTrue (l : List α) : List α := l.filter (fun _ => true)

/-- `filterMap` keeping every `some`. -/
def viaFilterMapSome (l : List α) : List α := l.filterMap (fun x => some x)

/-- `flatMap` with the singleton function, which is the identity as a monoid
morphism. -/
def viaFlatMapSing (l : List α) : List α := l.flatMap (fun x => [x])

/-- Reverse twice.  Two O(n) passes and an allocation, for the original. -/
def viaRevRev (l : List α) : List α := l.reverse.reverse

/-- Compose `map id` with itself.  Two traversals, zero effect. -/
def viaMapIdTwice (l : List α) : List α := (List.map id ∘ List.map id) l

/-! ## Group B — fold identities -/

/-- `foldl` with a left-absorbing step, seeded with the list itself: the seed is
returned untouched, but the list is still walked. -/
def viaFoldlSeed (l : List α) : List α := l.foldl (fun acc _ => acc) l

/-- The `foldr` counterpart, again seeded with the list. -/
def viaFoldrSeed (l : List α) : List α := l.foldr (fun _ acc => acc) l

/-- `foldr` consing every element onto the accumulator.  A left fold written
right-to-left. -/
def viaFoldrHead (l : List α) : List α := l.foldr (fun x acc => x :: acc) []

/-- Reverse, then `foldl` the elements back on.  A round trip through the
reverse-then-rebuild path. -/
def viaRevFoldl (l : List α) : List α := l.reverse.foldl (fun acc x => x :: acc) []

/-! ## Group C — decomposition round-trips -/

/-- `span` with an always-true predicate: the first component is the whole
list, the second is empty, and we keep the first. -/
def viaSpanAllTrue (l : List α) : List α := (l.span (fun _ => true)).1

/-- The mirror image: an always-false predicate, keeping the second component. -/
def viaSpanAllFalse (l : List α) : List α := (l.span (fun _ => false)).2

/-- `partition` with an always-true predicate, keeping the "true" half. -/
def viaPartitionT (l : List α) : List α := (l.partition (fun _ => true)).1

/-- `partition` with an always-false predicate, keeping the "false" half. -/
def viaPartitionF (l : List α) : List α := (l.partition (fun _ => false)).2

/-- `splitAt` the full length, keeping the prefix.  Same as `viaTakeLength` but
routed through the pair-returning combinator. -/
def viaSplitAtLen (l : List α) : List α := (l.splitAt l.length).1

/-- `splitAt` zero, keeping the suffix.  Same as `viaDropZero`, different
combinator. -/
def viaSplitAtZero (l : List α) : List α := (l.splitAt 0).2

/-- `zipIdx` the list with `range`, then project the list component back out. -/
def viaZipIdxMapFst (l : List α) : List α := l.zipIdx.map Prod.fst

/-- Duplicate the list, then take the first half.  Allocates 2n elements to
recover n. -/
def viaTakeAppend (l : List α) : List α := (l ++ l).take l.length

/-! ## Group D — needs a witness element -/

/-- Cons a head, then drop it again.  The consed element has to be supplied:
there is no way to fabricate an inhabitant of an arbitrary `α` out of a
`List α`, so this takes the element as an extra argument. -/
def viaConsDrop1 (a : α) (l : List α) : List α := (a :: l).drop 1

/-- Cons a head, drop it, then take the whole remainder.  Two redundant
operations where `viaConsDrop1` uses one.  (Note that `List.replicate 1 l` is
not available here: `replicate`'s element parameter is an `α`, not a `List α`.) -/
def viaConsTake (a : α) (l : List α) : List α := ((a :: l).drop 1).take l.length

/-! ## Group E — needs `[DecidableEq α]` -/

/-- Append the deduplicated list, then truncate back to the original length.
Deliberately redundant: `eraseDups` can only ever *shorten* `l`, so it is used
purely to make the appended list a different length before the truncation throws
the difference away.  The two `append` orders are not interchangeable — putting
`l.eraseDups` first would truncate into the deduplicated prefix. -/
def viaEraseDupsTake (l : List α) [DecidableEq α] : List α :=
  (l ++ l.eraseDups).take l.length

/-- Filtering by membership in the original list.  Every element of `l` is
trivially in `l`, so the filter keeps everything — but it is a real `DecidableEq`
lookup per element, unlike `viaFilterTrue`'s constant test.  A second, redundant
`filter` of the same shape follows. -/
def viaEraseDupsFilter (l : List α) [DecidableEq α] : List α :=
  (l.filter (fun x => x ∈ l)).filter (fun x => x ∈ l)

/-- Filter by membership in the original list: always true for every element of
it.  Distinct from `viaFilterTrue` in that the test is a real (decidable) lookup
rather than a constant. -/
def viaFilterMem (l : List α) [DecidableEq α] : List α :=
  l.filter (fun x => x ∈ l)

/-- `filterMap` through a membership test that always succeeds. -/
def viaFilterMapMem (l : List α) [DecidableEq α] : List α :=
  l.filterMap (fun x => if x ∈ l then some x else none)

end Equiv.List
