import Scripts.Test.Equiv.List.ZipIdx

/-!
# Proofs: `List.zipIdx` alternatives are equal to the original

`byCounter` is proved.  The other two routes are **attempted but not finished**;
each is recorded below.

`List.zipIdx` carries a legacy `optParam ℕ 0` offset, so `List.zipIdx l k` numbers
from `k`.  That is exactly what makes the other two routes awkward: an alternative
that is genuinely offset-`0` cannot be matched against `List.zipIdx l k` by plain
cons induction, because the tail of `List.zipIdx (a :: t) k` is
`List.zipIdx t (k + 1)`, not `List.zipIdx t 0`.  Getting past that needs the
general lemma `List.zipIdx l k = l.zip ((range l.length).map (k + ·))`, which in
turn needs the index-shift identity

    (range (m + 1)).map (k + ·) = k :: (range m).map (k + 1 + ·)

because `List.range (m + 1) = List.range m ++ [m]`, *not* `0 :: List.range m`.
That is the trap: the identity one reaches for first is false (`range 3 = [0,1,2]`
but `0 :: range 2 = [0,0,1]`).

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.zipIdx

universe u

variable {α : Type u}

private theorem range'_zero : ∀ n : ℕ, List.range' 0 n = List.range n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => rw [List.range'_1_concat, ih, List.range_succ, Nat.zero_add]

/-! ## `byCounter` -/

/-- Consing each pair onto a front accumulator and reversing at the end puts the
pairs back in the order the elements arrived, so the survivors are exactly
`List.zipIdx l k` with the seed tacked on behind them.  The seed appears *after*
the index list, which is why tracking the accumulator reversed is what makes the
induction close. -/
private theorem counter_zipIdx : ∀ (k : ℕ) (acc : List (α × ℕ)) (l : List α),
    (List.foldl (fun (acc, k) a => ((a, k) :: acc, k + 1)) (acc, k) l).1.reverse
      = acc.reverse ++ List.zipIdx l k := by
  intro k acc l
  induction l generalizing acc k with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, List.zipIdx.eq_2]
    have h := ih (acc := (a, k) :: acc) (k := k + 1)
    simp only [List.reverse_cons] at h
    rw [h]
    simp

theorem byCounter_eq_zipIdx (l : List α) : byCounter l = List.zipIdx l := by
  rw [byCounter, counter_zipIdx (k := 0) (acc := []) l]
  simp

/-! ## `byRangeZip` -/

/- Attempted, not finished.  Two pieces are needed and only one is in hand.

First, the swap lemma `r.zip l |>.map (fun pr => (pr.2, pr.1)) = l.zip r`, which
is a two-line induction on `r` and is *not* the problem.

The problem is the offset.  Reaching `List.zipIdx l 0` from
`(range l.length).zip l |>.map (·)` by cons induction requires

    List.zipIdx l k = l.zip ((List.range l.length).map (fun j => k + j))

proved by induction on `l` generalising `k`, and that induction needs

    (range (m + 1)).map (fun j => k + j) = k :: (range m).map (fun j => k + (j + 1))

which is true, but not for the reason one first tries.  `List.range_succ` gives
`range (m + 1) = range m ++ [m]`, so the identity is
`map (k + ·) (range m) ++ [k + m] = k :: map (k + (· + 1)) (range m)`, and the
base case `m = 0` is where `k + 0` has to be spotted.  Unfinished. -/

/-! ## `byFinRangeGet` -/

/- Attempted, not finished.  Needs

    (finRange l.length).map (fun i => (l.get i, i.val)) = l.zip (List.range l.length)

as a `List.ext` argument.  Two pieces are missing: `List.get_zip` and
`List.get_range` do **not** exist in this Mathlib, so `(l.zip (range n)).get i`
has to be broken up some other way; and `List.finRange n` is a `pmap` over
`range n`, not a `map`, so `(finRange n).map Fin.val = range n` has to be
re-derived.  Same `pmap`-versus-`map` obstacle that stopped `List.attach`. -/

/-! ## Against the original -/

theorem byCounter_eq_orig (l : List α) : byCounter l = orig l := byCounter_eq_zipIdx l

/-! ## Outstanding (stated, not proved) -/

/-!
The theorems below are the remaining routes.  Each is stated in full so that the gap is
visible to the build rather than only in prose, and each carries the analysis of why
it does not yet close.  The `sorry` is deliberate and temporary: this section is the
work list.  Every theorem outside it is fully proved.
-/

/-! ### `byRangeZip` -/

/-- Outstanding: not proved.  Reaching `zipIdx l 0` from an offset-0 form by cons induction requires
`List.zipIdx l k = l.zip ((List.range l.length).map (fun j => k + j))` proved
by induction generalising `k`, whose step needs
`(range (m+1)).map (k + ·) = k :: (range m).map (k + (· + 1))`.  The identity one
reaches for first is FALSE: `range (m+1) = range m ++ [m]`, not `0 :: range m`
(`range 3 = [0,1,2]` but `0 :: range 2 = [0,0,1]`). -/
theorem byRangeZip_eq_orig (l : List α) : byRangeZip l = orig l := by
  simp only [byRangeZip, orig]
  change List.map Prod.swap ((List.range l.length).zip l) =
    List.zipIdx l 0
  rw [List.zipIdx_eq_zip_range', range'_zero, List.zip_swap]

/-! ### `byFinRangeGet` -/

/-- Outstanding: not proved.  `List.get_zip` and `List.get_range` do not exist in this Mathlib, so
`(l.zip (range n)).get i` cannot be broken up; and `List.finRange n` is a
`pmap` over `range n`, not a `map`, so `(finRange n).map Fin.val = range n` has
to be re-derived.  Same `pmap`-versus-`map` wall that stopped `List.attach`. -/
private theorem finRange_zipIdx : ∀ (l : List α) (k : ℕ),
    (List.finRange l.length).map (fun i => (l.get i, k + i.val)) = List.zipIdx l k := by
  intro l
  induction l with
  | nil => intro k; simp
  | cons a t ih =>
    intro k
    simp only [List.length_cons, List.finRange_succ, List.map_cons, List.map_map]
    simp only [List.get_cons_zero, Fin.val_zero, Nat.add_zero]
    have htail :
        (List.finRange t.length).map
          (fun i => ((a :: t).get (Fin.succ i), k + (Fin.succ i).val)) =
        (List.finRange t.length).map (fun i => (t.get i, (k + 1) + i.val)) := by
      apply List.map_congr_left
      intro i hi
      simp [Fin.val_succ]
      omega
    change (a, k) :: (List.finRange t.length).map
        (fun i => ((a :: t).get (Fin.succ i), k + (Fin.succ i).val)) =
      List.zipIdx (a :: t) k
    rw [htail, ih, List.zipIdx.eq_2]

theorem byFinRangeGet_eq_orig (l : List α) : byFinRangeGet l = orig l := by
  simpa [byFinRangeGet, orig] using finRange_zipIdx l 0

end Alt.List.zipIdx
