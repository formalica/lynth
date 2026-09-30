import Mathlib

/-!
# Alternative definitions: `List.zip`

`List.zip` truncates to the shorter of its two arguments, which is the only
non-obvious part of it — the pairing itself is forced.  So the alternatives
below differ in *how the two lists are walked together* and in where the
truncation is enforced:

* `byRec` — structural recursion on both lists at once, stopping as soon as
  either runs out;
* `viaZipWith` — the pairing handed to `List.zipWith`, so the truncation is
  inherited rather than re-derived;
* `byOfFn` — index-driven: `List.ofFn` over `Fin (min xs.length ys.length)`,
  reading each list with `List.get`.  The length is computed once, up front,
  and the two proofs that the indices are in bounds are the *only* place the
  truncation is encoded;
* `byAccum` — a `let rec` loop that walks both lists together, consing onto a
  reversed accumulator and reversing once at the end.

The `Fin` indices in `byOfFn` are re-witnessed for each list: `i.val` is below
`min xs.length ys.length`, which is below each of the two lengths.
-/

namespace Alt.List.zip

universe u v

variable {α : Type u} {β : Type v}

/-- The original, kept as the reference point. -/
def orig (xs : List α) (ys : List β) : List (α × β) := List.zip xs ys

/-- Structural recursion on the pair of lists.  The two "empty" equations come
first, so the interesting equation only fires when both lists are nonempty,
and the answer is `(α × β)`-shaped consing. -/
def byRec : List α → List β → List (α × β)
  | [], _ => []
  | _, [] => []
  | a :: t, b :: s => (a, b) :: byRec t s

/-- The pairing is not re-derived at all: it is handed to `List.zipWith` and
the truncation is inherited from that function.  Reuses a different `List`
function as the substep, and adds the choice of which argument of the binary
function receives which list. -/
def viaZipWith (xs : List α) (ys : List β) : List (α × β) :=
  List.zipWith (fun a b => (a, b)) xs ys

/-- Index-driven.  The output length is `min xs.length ys.length`, computed
once; `List.ofFn` then walks those positions and `List.get` reads the two
lists at the same index.  The two bound proofs are what re-establish that
`i.val` is a legal index into each list separately. -/
def byOfFn (xs : List α) (ys : List β) : List (α × β) :=
  List.ofFn (fun i : Fin (min xs.length ys.length) =>
    (xs.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.min_le_left xs.length ys.length)⟩,
     ys.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.min_le_right xs.length ys.length)⟩))

/-- A tail-recursive walk over both lists with an explicit accumulator: the
pairs are consed onto the front as they are produced, and a single `reverse`
puts them in order.  Each step is in tail position, unlike `byRec`. -/
def byAccum (xs : List α) (ys : List β) : List (α × β) :=
  let rec go : List α → List β → List (α × β) → List (α × β)
    | [], _, acc => acc.reverse
    | _, [], acc => acc.reverse
    | a :: t, b :: s, acc => go t s ((a, b) :: acc)
  go xs ys []

end Alt.List.zip
