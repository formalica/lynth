import Scripts.Test.Equiv.List.GetD

/-!
# Proofs: `List.getD` alternatives are equal to the original

All six alternatives in `../GetD.lean` are proved equal to `List.getD` here.

The function is *total*: an index past the end returns the default, exactly as an
empty list does.  Every proof therefore has to discharge both the past-the-end
case and the empty-list case, which is why each is a two-dimensional induction (on
the list, then on the index) rather than a one-line `cases`.

`orig` is imported, not redefined.  No `sorry`, no `axiom`.
-/

namespace Alt.List.getD

universe u

variable {α : Type u}

/-! ## `direct` -/

/-- Structural recursion on the list, matching the index at each step.  The
index is a second argument of the theorem (rather than being generalised inside
the induction) so that the two degenerate cases — empty list, and index `0` — are
separate equations and fall to `simp`. -/
theorem direct_eq : ∀ (l : List α) (i : ℕ) (d : α), direct l i d = List.getD l i d
  | [], _, d => by simp [direct]
  | _ :: _, 0, d => by simp [direct]
  | a :: t, n + 1, d => by simp [direct, direct_eq]

/-! ## `viaDrop` -/

/-- `drop i` then a head probe.  Note the seed is *not* the reason this needs a
two-dimensional induction: the `match` on `l.drop i` cannot be reduced until the
list and the index are both known, and at `(a :: t, n + 1)` it becomes a `match`
on `t.drop n` — exactly the shape of the induction hypothesis, which is why the
`show` there is legitimate rather than a rewrite. -/
private theorem drop_headD : ∀ (l : List α) (i : ℕ) (d : α),
    (match l.drop i with | [] => d | x :: _ => x) = List.getD l i d
  | [], i, d => by simp
  | a :: t, 0, d => by simp
  | a :: t, n + 1, d => by
    change (match List.drop n t with | [] => d | x :: _ => x) = List.getD t n d
    exact drop_headD t n d

theorem viaDrop_eq (l : List α) (i : ℕ) (d : α) : viaDrop l i d = List.getD l i d := by
  change (match l.drop i with | [] => d | x :: _ => x) = List.getD l i d
  exact drop_headD l i d

/-! ## `viaSplitAt` -/

/-- `List.splitAt_eq` says `splitAt i l = (take i l, drop i l)`, so the second
component *is* `drop i` and `drop_headD` applies verbatim.  Nothing here needs the
compiled `.go` form, which is why the well-founded recursion is not an obstacle
after all. -/
theorem viaSplitAt_eq (l : List α) (i : ℕ) (d : α) :
    viaSplitAt l i d = List.getD l i d := by
  change (match (l.splitAt i).2 with | [] => d | x :: _ => x) = List.getD l i d
  rw [List.splitAt_eq]
  exact drop_headD l i d

/-! ## `viaGetElem` -/

/-- `getElem?` at exactly `i` with the caller's `d` for the `none` case.  The
simplest use of the total accessor. -/
theorem viaGetElem_eq (l : List α) (i : ℕ) (d : α) : viaGetElem l i d = List.getD l i d := by
  cases l with
  | nil => simp [viaGetElem]
  | cons a t => cases i with
    | zero => simp [viaGetElem]
    | succ n => simp [viaGetElem]

/-! ## `viaFoldl` -/

/-- Once the counter has passed `i` the latch can never fire again, so the
accumulator is frozen at the seed.  This is the half of the statement the naive
generalisation misses: the `if st.1 = i then x else st.2` step is the identity
from then on, and that is what carries `c = i` through the cons case below. -/
private theorem foldl_past (i c : ℕ) (d : α) : ∀ (l : List α), i < c →
    (l.foldl (fun (st : ℕ × α) x => (st.1 + 1, if st.1 = i then x else st.2)) (c, d)).2 = d
  | [], _ => rfl
  | x :: t, h => by
    have hne : c ≠ i := by omega
    have hE : ((c, d).1 + 1, if (c, d).1 = i then x else (c, d).2) = (c + 1, d) := by
      simp [hne]
    rw [List.foldl_cons, hE]
    exact foldl_past i (c + 1) d t (by omega)

/-- The latch, read as a *positional* statement: starting the counter at `c`, the
latched value is the head of `l.drop (i - c)`.  At `c = i` the latch fires on the
head and the rest of the list is already past the index, which is exactly the
`foldl_past` case; below `i` the tail is the induction hypothesis. -/
private theorem foldl_gen (i c : ℕ) : ∀ (l : List α) (d : α), c ≤ i →
    (l.foldl (fun (st : ℕ × α) x => (st.1 + 1, if st.1 = i then x else st.2)) (c, d)).2
      = (match l.drop (i - c) with | [] => d | x :: _ => x)
  | [], d, _ => by rw [List.drop_nil]; rfl
  | a :: t, d, h => by
    by_cases hci : c = i
    · have hE : ((c, d).1 + 1, if (c, d).1 = i then a else (c, d).2) = (c + 1, a) := by
        simp [hci]
      rw [List.foldl_cons, hE]
      rw [foldl_past i (c + 1) a t (by omega)]
      have hz : i - c = 0 := by omega
      rw [hz]
      rfl
    · have hne : c ≠ i := by omega
      have hE : ((c, d).1 + 1, if (c, d).1 = i then a else (c, d).2) = (c + 1, d) := by
        simp [hne]
      rw [List.foldl_cons, hE]
      have hz : i - c = i - (c + 1) + 1 := by omega
      rw [hz, List.drop_succ_cons]
      exact foldl_gen i (c + 1) t d (by omega)

theorem viaFoldl_eq (l : List α) (i : ℕ) (d : α) : viaFoldl l i d = List.getD l i d := by
  simp only [viaFoldl]
  rw [foldl_gen i 0 l d (Nat.zero_le i)]
  have hz : i - 0 = i := by omega
  rw [hz]
  exact drop_headD l i d

/-! ## `viaRange` -/

/-- One step of the range scan below the target index: the probe may succeed or
fail, but neither changes the accumulator. -/
private theorem range_step (i n : ℕ) (d : α) (l : List α) (hne : n ≠ i) :
    (match l[n]? with | some y => if n = i then y else d | none => d) = d := by
  cases hd : l[n]? <;> simp [hne]

/-- `range (n + 1)` is `range n ++ [n]`, and `foldl` over an append folds the
left part first — so everything below `i` is inert and only the final `i` can
latch.  The hypothesis `n ≤ i` (rather than `n < i + 1`) is what makes `n ≠ i`
automatic in the successor case. -/
private theorem range_foldl (i : ℕ) (l : List α) (d : α) : ∀ (n : ℕ), n ≤ i →
    (List.range n).foldl
      (fun acc k => match l[k]? with | some y => if k = i then y else acc | none => acc) d = d
  | 0, _ => rfl
  | n + 1, h => by
    have hn : n ≤ i := by omega
    have hne : n ≠ i := by omega
    rw [List.range_succ, List.foldl_append]
    rw [range_foldl i l d n hn]
    exact range_step i n d l hne

/-- The last step, at the index itself: the guard is now `i = i`, so the result is
`l[i]?.getD d`, which is `List.getD`. -/
private theorem range_last (i : ℕ) (l : List α) (d : α) :
    (List.foldl (fun acc k => match l[k]? with
      | some y => if k = i then y else acc
      | none => acc) d [i]) = l[i]?.getD d := by
  cases hd : l[i]? <;> simp [hd]

theorem viaRange_eq (l : List α) (i : ℕ) (d : α) : viaRange l i d = List.getD l i d := by
  change (List.range (i + 1)).foldl
    (fun acc k => match l[k]? with | some y => if k = i then y else acc | none => acc) d
    = List.getD l i d
  have h1 : (List.range i).foldl
      (fun acc k => match l[k]? with | some y => if k = i then y else acc | none => acc) d = d :=
    range_foldl i l d i (Nat.le_refl i)
  have h2 : List.range (i + 1) = List.range i ++ [i] := by simp [List.range_succ]
  rw [h2, List.foldl_append, h1, List.getD_eq_getElem?_getD]
  exact range_last i l d

/-! ## Against the original -/

theorem direct_eq_orig (l : List α) (i : ℕ) (d : α) : direct l i d = orig l i d :=
  direct_eq l i d

theorem viaDrop_eq_orig (l : List α) (i : ℕ) (d : α) : viaDrop l i d = orig l i d :=
  viaDrop_eq l i d

theorem viaSplitAt_eq_orig (l : List α) (i : ℕ) (d : α) : viaSplitAt l i d = orig l i d :=
  viaSplitAt_eq l i d

theorem viaFoldl_eq_orig (l : List α) (i : ℕ) (d : α) : viaFoldl l i d = orig l i d :=
  viaFoldl_eq l i d

theorem viaRange_eq_orig (l : List α) (i : ℕ) (d : α) : viaRange l i d = orig l i d :=
  viaRange_eq l i d

theorem viaGetElem_eq_orig (l : List α) (i : ℕ) (d : α) : viaGetElem l i d = orig l i d :=
  viaGetElem_eq l i d

end Alt.List.getD
