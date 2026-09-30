import Scripts.Test.Equiv.List.FindIdx

/-!
# Proofs: `List.findIdx` alternatives are equal to the original

`byCounterRec` is proved, on top of two recovered equations for `List.findIdx`
that are worth stating on their own:

* `findIdx_cons` — the cons equation `findIdx p (a :: t) = if p a then 0 else
  1 + findIdx p t`;
* `findIdx_go_add` — the accumulator offset, `findIdx.go p l k = k + findIdx p l`.

`List.findIdx` is a `List.brecOn` (`List.findIdx.go`), and its only exposed
equation `List.findIdx.eq_1` is the unrolling equation, so at first sight there is
nothing to induct against.  But `List.findIdx.go._f.eq_1` is `@[defeq]`, so

    simp [List.findIdx, List.findIdx.go]

already reduces the cons case — the `brecOn` is structural after all and the
missing equation is only missing from the *namespace*, not from the kernel.  That
is the unlock the whole `findIdx` family depends on.

The other three routes are **attempted but not finished**; each is recorded below.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.findIdx

universe u

variable {α : Type u}

/-! ## Recovering the loop -/

/-- The offset the loop carries, absorbed: every step adds its position to the
answer, so starting from `k` rather than `0` shifts the answer by `k`. -/
private theorem findIdx_go_add : ∀ (l : List α) (p : α → Bool) (k : ℕ),
    List.findIdx.go p l k = k + List.findIdx.go p l 0 := by
  intro l
  induction l with
  | nil => intro p k; simp [List.findIdx.go]
  | cons a t ih =>
    intro p k
    cases hpa : p a with
    | true =>
      have hc : List.findIdx.go p (a :: t) k = k := by
        simp [List.findIdx.go, hpa]
      rw [hc]
      simp [List.findIdx.go, hpa]
    | false =>
      have hc : List.findIdx.go p (a :: t) k = List.findIdx.go p t (k + 1) := by
        simp [List.findIdx.go, hpa]
      have hc0 : List.findIdx.go p (a :: t) 0 = List.findIdx.go p t 1 := by
        simp [List.findIdx.go, hpa]
      rw [hc, ih p (k + 1), hc0, ih p 1]
      omega

/-- The cons equation.  Note it is stated with a `match`, because the recovered
form from the loop is a `match`; writing `if p a then` instead leaves the `Bool`
coercion mismatch that `simp only [Bool.false_eq_true]` cannot repair. -/
private theorem findIdx_cons (p : α → Bool) (a : α) (t : List α) :
    List.findIdx p (a :: t) = match p a with
      | true => 0
      | false => 1 + List.findIdx p t := by
  have hc : List.findIdx p (a :: t) = match p a with
    | true => 0
    | false => List.findIdx.go p t 1 := by
    cases hpa : p a <;> simp [List.findIdx, List.findIdx.go, hpa]
  rw [hc]
  cases hp : p a with
  | true => rfl
  | false =>
    exact findIdx_go_add t p 1

/-! ## `byCounterRec` -/

/-- "Count the failures until the first success" is the same number as "the
position of the first success", because a list that never succeeds contributes
its whole length to the count and `l.length` is also the answer in that case.  The
`+ 1` versus `1 +` mismatch is `Nat.add_comm`. -/
private theorem counterRec_findIdx : ∀ (p : α → Bool) (l : List α),
    byCounterRec p l = List.findIdx p l := by
  intro p l
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [byCounterRec, findIdx_cons]
    cases hp : p a with
    | true => simp
    | false => simp [ih, Nat.add_comm]

theorem byCounterRec_eq_findIdx (p : α → Bool) (l : List α) :
    byCounterRec p l = List.findIdx p l := counterRec_findIdx p l

/-! ## `viaZipIdx` -/

private theorem findIdx_zipIdx (p : α → Bool) : ∀ (l : List α) (k : ℕ),
    List.findIdx (fun pr : α × ℕ => p pr.1) (List.zipIdx l k) = List.findIdx p l := by
  intro l
  induction l with
  | nil => intro k; simp
  | cons a t ih =>
    intro k
    rw [List.zipIdx.eq_2, findIdx_cons, findIdx_cons]
    cases h : p a <;> simp [ih]

/- Attempted, not finished.  Needs
`List.findIdx (fun pr => p pr.1) (List.zipIdx l) = List.findIdx p l`.  With
`findIdx_cons` in hand this is a cons induction whose cons case needs
`List.zipIdx.eq_2` *and* the fact that `findIdx` of `zipIdx (a :: t) k` starting
from offset `0` finds the same index as `findIdx` of `t` — which is precisely the
offset-shift problem already recorded in `../ZipIdx.lean`, arriving here from the
other side.  Unfinished. -/

/-! ## `viaGetElemScan` -/

/- Attempted, not finished.  Needs
`List.find? (fun i => p (l.get i)) (List.finRange l.length) = (findIdx p l).getD 0`
combined with the fallback, and the "nothing found" case has to agree with
`l.length`, not `0`.  Two things are missing: a `Fin`-index characterisation of
`find?` over `finRange`, and the `l[i]`-style bounds that `List.findIdx_cons`
above makes unnecessary.  Unfinished. -/

/-! ## `byFoldlCounter` -/

private def findIdxFoldStep (p : α → Bool) : Option ℕ × ℕ → α → Option ℕ × ℕ
  | state, a =>
    match state.1 with
    | some _ => (state.1, state.2 + 1)
    | none => if p a then (some state.2, state.2 + 1) else (none, state.2 + 1)

private theorem foldl_findIdx_some (p : α → Bool) : ∀ (l : List α) (i k : ℕ),
    (List.foldl (findIdxFoldStep p) (some i, k) l).1 = some i := by
  intro l
  induction l with
  | nil => intro i k; rfl
  | cons a t ih => intro i k; simpa [List.foldl_cons, findIdxFoldStep] using ih i (k + 1)

private theorem foldl_counter_findIdx (p : α → Bool) : ∀ (l : List α)
    (acc : Option ℕ) (k : ℕ),
    (List.foldl (findIdxFoldStep p)
      (acc, k) l).1 =
      (match acc with
      | some i => some i
      | none => if List.findIdx p l < l.length then some (k + List.findIdx p l) else none) := by
  intro l
  induction l with
  | nil => intro acc k; cases acc <;> rfl
  | cons a t ih =>
    intro acc k
    cases acc with
    | some i =>
      simp only [List.foldl_cons, findIdxFoldStep]
      exact foldl_findIdx_some p t i (k + 1)
    | none =>
      cases hp : p a with
      | true =>
        simp only [List.foldl_cons, findIdxFoldStep, hp, ite_true]
        rw [foldl_findIdx_some]
        simp [List.findIdx_cons, hp]
      | false =>
        simp only [List.foldl_cons, findIdxFoldStep, hp, Bool.false_eq_true, ite_false]
        rw [ih none (k + 1)]
        simp only [List.findIdx_cons, hp, Bool.false_eq_true, ite_false]
        by_cases ht : List.findIdx p t < t.length
        · simp [ht]
          omega
        · simp [ht]
          

/- Attempted, not finished.  The fold needs the invariant "the latch is `some k`
exactly when `k` is the index of the first success", which is the same content as
`findIdx_cons` but for a two-component accumulator.  The `match` on the `Option`
makes the statement longer than it looks, since the counter still advances in
both branches.  Unfinished. -/

/-! ## Against the original -/

theorem byCounterRec_eq_orig (p : α → Bool) (l : List α) : byCounterRec p l = orig p l :=
  byCounterRec_eq_findIdx p l

private theorem finRange_findIdx (p : α → Bool) : ∀ (l : List α),
    ((List.finRange l.length).findIdx? (fun i => p (l.get i))).getD l.length =
      List.findIdx p l := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.length_cons, List.finRange_succ]
    simp only [List.findIdx?_cons]
    have htail :
        (fun i : Fin t.length => p ((a :: t).get (Fin.succ i))) =
          (fun i => p (t.get i)) := by
      funext i
      simp [List.get_eq_getElem, Fin.succ]
    have hscan :
        List.findIdx? (fun i : Fin (t.length + 1) => p ((a :: t).get i))
            ((List.finRange t.length).map Fin.succ) =
          List.findIdx? (fun i : Fin t.length => p (t.get i)) (List.finRange t.length) := by
      rw [List.findIdx?_map]
      congr 1
    
    have hmap :
        (Option.map (fun i => i + 1)
          ((List.finRange t.length).findIdx? (fun i => p (t.get i)))).getD
            (t.length + 1) =
          (((List.finRange t.length).findIdx? (fun i => p (t.get i))).getD t.length) + 1 := by
      simpa using (Option.getD_map (fun i : ℕ => i + 1) t.length
        ((List.finRange t.length).findIdx? (fun i => p (t.get i))))
    cases h : p ((a :: t).get 0)
    · have hp : p a = false := by simpa using h
      simp only [h, Bool.false_eq_true, ite_false]
      rw [hscan, hmap, ih]
      simp [hp, List.findIdx_cons, Nat.add_comm]
    · have hp : p a = true := by simpa using h
      simp [h, hp, List.get_cons_zero, List.findIdx_cons]

/-! ## Outstanding (stated, not proved) -/

/-!
The theorems below are the remaining routes.  Each is stated in full so that the gap is
visible to the build rather than only in prose, and each carries the analysis of why
it does not yet close.  The `sorry` is deliberate and temporary: this section is the
work list.  Every theorem outside it is fully proved.
-/

/-! ### `viaZipIdx` -/

/-- Outstanding: not proved.  The cons case closes against `findIdx_cons` and `List.zipIdx.eq_2`, but the
tail of `zipIdx (b :: t) 0` is `zipIdx t 1`, not `zipIdx t 0`.  Converting needs
`findIdx_go_add` AND a `zipIdx`-offset lemma at once -- the same missing lemma as
`ZipIdx.byRangeZip` and `ZipIdx.byFinRangeGet`. -/
theorem viaZipIdx_eq_orig (p : α → Bool) (l : List α) : viaZipIdx p l = orig p l := by
  simp [viaZipIdx, orig, findIdx_zipIdx]

/-! ### `viaGetElemScan` -/

/-- Outstanding: not proved.  Two gaps: a `Fin`-index characterisation of `find?` over `finRange`, and the
"nothing found" case, whose fallback `l.length` must be shown equal to the
`findIdx` answer rather than to `0`. -/
theorem viaGetElemScan_eq_orig (p : α → Bool) (l : List α) : viaGetElemScan p l = orig p l := by
  simpa [viaGetElemScan, orig] using finRange_findIdx p l

/-! ### `byFoldlCounter` -/

/-- Outstanding: not proved.  Same content as `findIdx_cons` but for a three-component state: the latch, the
position, and the count that still advances in both branches. -/
theorem byFoldlCounter_eq_orig (p : α → Bool) (l : List α) : byFoldlCounter p l = orig p l := by
  have hfold :
      List.foldl (fun (acc, k) a =>
        match acc with
        | some _ => (acc, k + 1)
        | none => if p a then (some k, k + 1) else (none, k + 1))
        (none, 0) l = List.foldl (findIdxFoldStep p) (none, 0) l := by
    rfl
  unfold byFoldlCounter
  calc
    _ = ((List.foldl (findIdxFoldStep p) (none, 0) l).1).getD l.length :=
      congrArg (fun state : Option ℕ × ℕ => state.1.getD l.length) hfold
    _ = _ := by
      rw [foldl_counter_findIdx]
      dsimp [orig]
      by_cases h : ∃ x ∈ l, p x = true
      · have hlt := List.findIdx_lt_length_of_exists h
        simp [h, hlt]
      · have hfalse : ∀ x ∈ l, p x = false := by
          intro x hx
          cases hp : p x with
          | false => rfl
          | true => exact (h ⟨x, hx, hp⟩).elim
        have hidx := List.findIdx_eq_length.mpr hfalse
        simp [h, hidx]

end Alt.List.findIdx
