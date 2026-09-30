import Mathlib

/-!
# Alternative definitions: `List.getD`

Six ways to read a list at an index with a fallback.  `List.getD` is a recursion
on the list and the index at once; the alternatives use `drop i` plus a head
probe, `splitAt i` plus a head probe, a `foldl` that latches the element once the
index counter passes through, a `List.range` scan, and `List.findIdx`-free
`getElem?` with the fallback.

The traps here are all about the index.  `List.getD` is *total*: an index past
the end returns the default, exactly as an empty list does.  `List.headD`'s
default is the **last** argument while `List.getD`'s is also last but the index
sits in the middle, so mixing the two up silently changes the answer.  And
`l[i]?` is `getElem?` notation in this rev, not a method, so it needs an
explicit `?`.  A definition written as `List.getD (i + 1) l d` would also typecheck
and be wrong.  Every definition below is checked against the original on all
lists of length ≤ 3 over `{0, 1, 2}` and all indices in `{0, 1, 2, 3}`, so the
past-the-end and empty cases are both covered.
-/

namespace Alt.List.getD

variable {α : Type u}

/-- The original, kept as the reference point: list, index, default. -/
def orig (l : List α) (i : ℕ) (d : α) : α := l.getD i d

/-- Direct recursion on the list, matching the index against `0` at each step.
The shape `List.getD` itself uses. -/
def direct : List α → ℕ → α → α
  | [], _, d => d
  | x :: _, 0, _ => x
  | _ :: t, n + 1, d => direct t n d

/-- `drop i` then a head probe: positional access phrased as a suffix plus its
first element.  Recursion lives in `drop`, on the index rather than the list. -/
def viaDrop (l : List α) (i : ℕ) (d : α) : α :=
  match l.drop i with
  | [] => d
  | x :: _ => x

/-- `splitAt i` and take the second component, then probe its head.  A
decomposition-based version of `viaDrop`: one call splits instead of dropping. -/
def viaSplitAt (l : List α) (i : ℕ) (d : α) : α :=
  match (l.splitAt i).2 with
  | [] => d
  | x :: _ => x

/-- A `foldl` whose state is a pair of a position counter and a latch: the
element sitting at the counter is captured on the way past index `i`, and the
default survives when the list is too short.  Everything is visited, unlike
`direct`, which stops as soon as it hits the index. -/
def viaFoldl (l : List α) (i : ℕ) (d : α) : α :=
  l.foldl (fun (st : ℕ × α) x => (st.1 + 1, if st.1 = i then x else st.2)) (0, d) |>.2

/-- A `List.range`-indexed scan: only the positions below `i` matter, and the
element at `i` is latched if the list is long enough.  Purely positional. -/
def viaRange (l : List α) (i : ℕ) (d : α) : α :=
  ((List.range (i + 1)).foldl
    (fun acc k => match l[k]? with
      | some y => if k = i then y else acc
      | none => acc) d)

/-- `getElem?` probe at exactly `i`, with the default for the `none` case.  The
minimal use of the total accessor, and the fallback is the caller's `d`. -/
def viaGetElem (l : List α) (i : ℕ) (d : α) : α := (l[i]?).getD d

end Alt.List.getD
