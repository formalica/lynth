import Scripts.Test.Equiv.List.Range

/-!
# Proofs: `List.range` alternatives are equal to the original

All four alternatives in `../Range.lean` are proved equal to `List.range` here.

Three of the four go through one shared fact: projecting the values out of
`List.finRange` gives `List.range`.  Proving that by induction needs one more
lemma — that `0` consed onto the successors of `List.range` is `List.range` with
the new largest element appended — because the `finRange` recursion and the
`range` recursion disagree about whether the new element goes at the front or
the back.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.range

/-! ## A shared helper -/

/-- `0` consed onto the successors of `List.range n` is `List.range n` with `n`
appended.  The `range` recursion appends, the `finRange` recursion conses, and
this lemma reconciles the two on the way up. -/
private theorem zero_succ_range : ∀ (n : ℕ),
    0 :: List.map Nat.succ (List.range n) = List.range n ++ [n] := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, ← List.cons_append, ih]

/-- `Fin.val ∘ Fin.succ` *is* `Nat.succ ∘ Fin.val`: `Fin.succ` bumps the value
by one (`Fin.val_succ`) and the bound proofs are irrelevant, so `congr` closes it.
-/
private theorem comp_def' (k : ℕ) :
    (Fin.val ∘ (Fin.succ : Fin k → Fin (k + 1))) = fun i : Fin k => Fin.val (Fin.succ i) :=
  rfl

private theorem val_succ_map (k : ℕ) : ∀ (L : List (Fin k)),
    L.map (fun i : Fin k => Fin.val (Fin.succ i)) = List.map Nat.succ (L.map Fin.val) := by
  intro L
  induction L with
  | nil => rfl
  | cons i L ih =>
    have e1 : Fin.val (Fin.succ i) = Nat.succ (Fin.val i) := Fin.val_succ i
    rw [List.map_cons, List.map_cons, ih, e1, List.map_cons]

/-- Projecting the values out of `List.finRange` gives `List.range`.  The
`finRange` successor equation conses a fresh `0` and shifts the rest up, so the
induction hypothesis is consumed through `zero_succ_range`. -/
private theorem val_finRange : ∀ (n : ℕ), (List.finRange n).map Fin.val = List.range n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.finRange_succ, List.map_cons, List.map_map]
    have hc : (Fin.val ∘ (Fin.succ : Fin k → Fin (k + 1)))
        = fun i : Fin k => Fin.val (Fin.succ i) := comp_def' k
    have h1 : (List.finRange k).map (fun i : Fin k => Fin.val (Fin.succ i))
        = List.map Nat.succ ((List.finRange k).map Fin.val) := val_succ_map k _
    rw [hc, h1, ih, List.range_succ]
    exact zero_succ_range k

/-! ## `byFinRangeVal` -/

theorem byFinRangeVal_eq_range (n : ℕ) : byFinRangeVal n = List.range n := val_finRange n

/-! ## `byOfFn` -/

/-- `List.ofFn_eq_map` puts `byOfFn` on the same footing as `byFinRangeVal`. -/
theorem byOfFn_eq_range (n : ℕ) : byOfFn n = List.range n := by
  rw [byOfFn, List.ofFn_eq_map (f := fun i : Fin n => i.val)]
  exact val_finRange n

/-! ## `byRangePrime` -/

/-- The stepping version started at `0` is the plain version: `List.range'_1_concat`
supplies the successor step, and `0 + n` simplifies. -/
private theorem range'_zero : ∀ (n : ℕ), List.range' 0 n = List.range n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range'_1_concat, ih, List.range_succ, Nat.zero_add]

theorem byRangePrime_eq_range (n : ℕ) : byRangePrime n = List.range n := range'_zero n

/-! ## `bySuccRec` -/

theorem bySuccRec_eq_range : ∀ (n : ℕ), bySuccRec n = List.range n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [bySuccRec, ih, zero_succ_range, List.range_succ]

/-! ## Against the original -/

theorem byOfFn_eq_orig (n : ℕ) : byOfFn n = orig n := byOfFn_eq_range n

theorem byFinRangeVal_eq_orig (n : ℕ) : byFinRangeVal n = orig n := byFinRangeVal_eq_range n

theorem byRangePrime_eq_orig (n : ℕ) : byRangePrime n = orig n := byRangePrime_eq_range n

theorem bySuccRec_eq_orig (n : ℕ) : bySuccRec n = orig n := bySuccRec_eq_range n

end Alt.List.range
