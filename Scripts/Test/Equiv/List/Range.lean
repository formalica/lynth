import Mathlib

/-!
# Alternative definitions: `List.range`

`List.range n` is `0, 1, …, n - 1`, built in one pass.  Four other routes to the
same list:

* `byOfFn` — as the enumeration of a function on `Fin n`, the generic
  "apply to every position" combinator, with the function reading its own index;
* `byFinRangeVal` — from the *bounded* index list `List.finRange`, projecting the
  bound away and keeping only the values;
* `byRangePrime` — from the general stepping version, started at `0`;
* `bySuccRec` — primitive recursion on the bound, written out by hand: each
  step shifts the values produced so far up by one and puts the new smallest one
  in front.

The last two stay in `ℕ` throughout; the first two route through `Fin n` and so
exercise the finite-index machinery instead.
-/

namespace Alt.List.range

/-- The original, kept as the reference point. -/
def orig (n : ℕ) : List ℕ := List.range n

/-- As the enumeration of a function on `Fin n`.  `List.ofFn` is the generic
"apply a function to every position" combinator; here the function reads its own
index, so the result is the position list itself. -/
def byOfFn (n : ℕ) : List ℕ := List.ofFn (fun i : Fin n => i.val)

/-- From the bounded index list `List.finRange n`.  Each element is a `Fin n`;
only the value is kept, so the bound is discarded and the shape of the list is
irrelevant. -/
def byFinRangeVal (n : ℕ) : List ℕ := (List.finRange n).map Fin.val

/-- From the general stepping version `List.range' s n`, started at `s = 0`.
This is the same computation with the starting point left as a free parameter
and then instantiated. -/
def byRangePrime (n : ℕ) : List ℕ := List.range' 0 n

/-- Primitive recursion on the bound, written out rather than delegated to
`List.range`.  Each step shifts every previously produced value up by one and
puts the new smallest one in front, rather than appending at the back. -/
def bySuccRec : ℕ → List ℕ
  | 0 => []
  | n + 1 => 0 :: (bySuccRec n).map Nat.succ

end Alt.List.range
