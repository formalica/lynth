import Scripts.Test.Equiv.List.Tail

/-!
# Proofs: `List.tail` alternatives are equal to the original

Seven of the seven alternatives in `../Tail.lean` are proved equal to `List.tail`
here.

The point of the file, as the source docstring says, is that `List.tail` is
*total*: `List.tail [] = []`, unlike `Array.tail`.  So every alternative has to
agree on the empty list, and the one thing that rules out "the element after the
first" as a phrasing.
-/

namespace Alt.List.tail

variable {α : Type u}

/-! ## One-step alternatives -/

theorem direct_eq (l : List α) : direct l = List.tail l := by cases l <;> rfl

/-- The general prefix-dropper at the degenerate prefix. -/
theorem viaDrop_eq (l : List α) : viaDrop l = List.tail l := by cases l <;> rfl

/-- `splitAt 1` and keep the suffix. -/
theorem viaSplitAt_eq (l : List α) : viaSplitAt l = List.tail l := by
  cases l with
  | nil => rfl
  | cons a t => simp [viaSplitAt]

/-- The fuel loop *is* `drop`: `List.drop_succ_cons` is the cons step in the
opposite direction, and the two boundary cases are `rfl`. -/
theorem viaPeel_eq (n : ℕ) (l : List α) : viaPeel n l = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ k ih => cases l with
    | nil => simp [viaPeel]
    | cons a t => rw [viaPeel, List.drop_succ_cons, ih]

/-- Fuel `1` into the peel loop: `viaPeel 0 _ _ = _` and `viaPeel _ [] _ = []`,
so only the cons case is live, and it is `rfl`. -/
theorem viaPeelLast_eq (l : List α) : viaPeelLast l = List.tail l := by
  cases l <;> rfl

/-- Two reversals and a drop.  Wasted work, but the argument is the same two
cases as everything else. -/
theorem viaRevRev_eq (l : List α) : viaRevRev l = List.tail l := by
  cases l with
  | nil => rfl
  | cons a t => simp [viaRevRev, List.reverse_reverse]

/-! ## `viaFoldl` -/

/-- The accumulator is a pair of a list and a "have we passed the head yet" flag,
so the flag is `false` for exactly the first step and `true` forever after.  The
helper covers the `true` case, which is the whole of the tail; it needs the
accumulator generalised because the cons case shifts it. -/
private theorem foldl_seen (l : List α) (acc : List α) :
    (l.foldl (fun (a, s) x => if s then (a ++ [x], true) else ([], true))
        (acc, true)).1 = acc ++ l := by
  induction l generalizing acc with
  | nil => simp
  | cons b t ih => simp [List.foldl_cons, ih]

theorem viaFoldl_eq (l : List α) : viaFoldl l = List.tail l := by
  cases l with
  | nil => simp [viaFoldl]
  | cons a t => simp [viaFoldl, List.foldl_cons, foldl_seen t []]

/-! ## `viaZipRange` -/

/-- The `snd` projection of a `zip` recovers the shorter list exactly, so the only
work is asking `List.map_snd_zip` for its bound and getting the length of
`List.range` to line up.  Note `List.range (n + 1)` is *not* `0 :: List.range n`
(`range 3 = [0,1,2]`, `0 :: range 2 = [0,0,1]`), so nothing here relies on the
index list being a cons — it never has to be, because the hypothesis
`(a :: t).length ≤ (List.range (a :: t).length).length` is `length_range` away
from being `x ≤ x`. -/
theorem viaZipRange_eq (l : List α) : viaZipRange l = List.tail l := by
  cases l with
  | nil => simp [viaZipRange]
  | cons a t =>
    have hlen : (a :: t).length ≤ (List.range (a :: t).length).length := by
      rw [List.length_range]
    simp only [viaZipRange]
    rw [List.map_drop, List.map_snd_zip hlen]
    simp

/-! ## Against the original -/

theorem direct_eq_orig (l : List α) : direct l = orig l := direct_eq l

theorem viaDrop_eq_orig (l : List α) : viaDrop l = orig l := viaDrop_eq l

theorem viaSplitAt_eq_orig (l : List α) : viaSplitAt l = orig l := viaSplitAt_eq l

theorem viaPeelLast_eq_orig (l : List α) : viaPeelLast l = orig l := viaPeelLast_eq l

theorem viaPeel_eq_orig (n : ℕ) (l : List α) : viaPeel n l = l.drop n := viaPeel_eq n l

theorem viaRevRev_eq_orig (l : List α) : viaRevRev l = orig l := viaRevRev_eq l

theorem viaFoldl_eq_orig (l : List α) : viaFoldl l = orig l := viaFoldl_eq l

theorem viaZipRange_eq_orig (l : List α) : viaZipRange l = orig l := viaZipRange_eq l

end Alt.List.tail
