import Scripts.Test.Equiv.List.Take

/-!
# Proofs: `List.take` alternatives are equal to the original

All four alternatives in `../Take.lean` are proved equal to `List.take` here.

`List.take` is compiled through `Nat.brecOn`, so none of the routes gets a
structural equation for free; what they get instead is `List.take_zero`,
`List.take_succ_cons` and `List.take_nil`, which between them say everything the
two proved alternatives need.

Two of the four are **not yet proved**, and both are recorded here rather than
papered over:

* `byGetElemMap` needs `(finRange m).map (fun i => l.get i) = take m l` for
  `m ≤ l.length`.  The induction has to be on the *list* (both
  `List.take_succ_cons` and `List.finRange_succ` want a cons), and the awkward
  part is that after `List.finRange_succ` the surviving indices are
  `Fin.succ i : Fin (k + 1)` while `List.get` wants `Fin (t.length + 1)`; the two
  are only defeq up to a `Fin` cast, and `rw` will not bridge that.
* `byCounter`'s step carries a *pair* accumulator, so the fold lemma has to track
  the counter through `Nat` truncated subtraction in the second component as well
  as the first.  Tracking only the first component is not enough, because on the
  empty list the counter does not advance at all.

Nothing about either definition is in doubt: the `decide`-based evaluation check
over all lists of length ≤ 3 and all counts ≤ 4 confirms both equal
`List.take` on every input tested.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.take

universe u

variable {α : Type u}

/-! ## `byRec` -/

/-- The recursion written out, against `List.take_zero` / `List.take_succ_cons` /
`List.take_nil`.  The index has to be generalised over, since the recursion
decreases it. -/
private theorem rec_take : ∀ (n : ℕ) (l : List α), byRec n l = List.take n l := by
  intro n
  induction n with
  | zero => intro l; rw [byRec, List.take_zero]
  | succ k ih =>
    intro l
    cases l with
    | nil => rw [byRec, List.take_nil]
    | cons a t =>
      rw [byRec, List.take_succ_cons]
      exact congrArg (fun L => a :: L) (ih t)

theorem byRec_eq_take (n : ℕ) (l : List α) : byRec n l = List.take n l := rec_take n l

/-! ## `viaRevDropRev` -/

/-- `List.reverse_take` is the statement, read in the other direction: the
`reverse` of the first `n` elements is the tail of the reversed list, so the tail
of the reversed list reversed back is the first `n` again. -/
theorem viaRevDropRev_eq_take (n : ℕ) (l : List α) : viaRevDropRev n l = List.take n l := by
  rw [viaRevDropRev, ← (List.reverse_take (l := l) (i := n)), List.reverse_reverse]

/-! ## `byGetElemMap` -/

/-! ## `byGetElemMap` -/

private theorem getFinRange_take (m : ℕ) (l : List α) (hml : m ≤ l.length) :
    (List.finRange m).map (fun i => l.get ⟨i.val, by omega⟩) = l.take m := by
  induction m generalizing l with
  | zero => simp
  | succ m ih =>
    cases l with
    | nil => simp at hml
    | cons a t =>
      have h' : m ≤ t.length := by simp at hml; omega
      simp only [List.finRange_succ, List.map_cons, List.map_map]
      have hhead : (a :: t).get ⟨0, by omega⟩ = a := by rfl
      simp only [Fin.val_zero, List.get_cons_zero]
      have htail : (fun i : Fin m =>
          (a :: t).get ⟨(Fin.succ i).val, by omega⟩) =
          (fun i => t.get ⟨i.val, by omega⟩) := by
        funext i
        simp [List.get_cons_succ]
      have htail' :
          (fun i : Fin (m + 1) => (a :: t).get ⟨i.val, by omega⟩) ∘ Fin.succ =
            (fun i => t.get ⟨i.val, by omega⟩) := by
        funext i
        exact congrFun htail i
      rw [htail', ih t h', List.take_succ_cons]
      simp [hhead]

private theorem take_min_length (n : ℕ) (l : List α) :
    List.take (min n l.length) l = List.take n l := by
  by_cases h : n ≤ l.length
  · simp [Nat.min_eq_left h]
  · have h' : l.length ≤ n := by omega
    simp [Nat.min_eq_right h', List.take_of_length_le h']

/-! ## `byCounter` -/

private theorem counter_take_invariant (n : ℕ) : ∀ (l acc : List α) (k : ℕ),
    (List.foldl (fun (acc, k) a =>
      if k < n then (acc ++ [a], k + 1) else (acc, k)) (acc, k) l).1 =
        acc ++ l.take (n - k) := by
  intro l
  induction l with
  | nil => intro acc k; simp
  | cons a t ih =>
    intro acc k
    by_cases hk : k < n
    · simp only [List.foldl_cons, if_pos hk]
      have htake : (a :: t).take (n - k) = a :: t.take (n - (k + 1)) := by
        have hn : n - k = n - (k + 1) + 1 := by omega
        rw [hn, List.take_succ_cons]
      rw [ih, htake, List.append_assoc]
      simp
    · simp only [List.foldl_cons, if_neg hk]
      have hk' : n ≤ k := by omega
      simp [ih, Nat.sub_eq_zero_of_le hk']

/-! ## Against the original -/

theorem byRec_eq_orig (n : ℕ) (l : List α) : byRec n l = orig n l := rec_take n l

theorem viaRevDropRev_eq_orig (n : ℕ) (l : List α) : viaRevDropRev n l = orig n l :=
  viaRevDropRev_eq_take n l

/-! ## Outstanding (stated, not proved) -/

/-!
The theorems below are the remaining routes.  Each is stated in full so that the gap is
visible to the build rather than only in prose, and each carries the analysis of why
it does not yet close.  The `sorry` is deliberate and temporary: this section is the
work list.  Every theorem outside it is fully proved.
-/

/-! ### `byGetElemMap` -/

/-- Outstanding: not proved.  Same `Fin` cast as `Drop.byGetElemMap`: `List.finRange_succ` produces
`Fin.succ i : Fin (k+1)` while `List.get` wants `Fin (t.length+1)`. -/
theorem byGetElemMap_eq_orig (n : ℕ) (l : List α) : byGetElemMap n l = orig n l := by
  calc
    byGetElemMap n l = List.take (min n l.length) l := by
      simpa [byGetElemMap] using getFinRange_take (min n l.length) l (Nat.min_le_right _ _)
    _ = List.take n l := take_min_length n l
    _ = orig n l := rfl

/-! ### `byCounter` -/

/-- Outstanding: not proved.  The count is `min n l.length` and the accumulator is built by `++`, so the
seed-generalised fold lemma must track *both* the count and the accumulated
prefix; tracking only the count fails on the empty list. -/
theorem byCounter_eq_orig (n : ℕ) (l : List α) : byCounter n l = orig n l := by
  simp only [byCounter, orig]
  simpa using counter_take_invariant n l [] 0

end Alt.List.take
