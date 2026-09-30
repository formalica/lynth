import Scripts.Test.Equiv.List.Erase

/-!
# Proofs: `List.erase` alternatives are equal to the original

`byRec` and `viaTakeDrop` are proved.  `viaEraseIdx` and `byFoldlLatch` are
**attempted but not finished**; each is recorded below.

Two loops have to be confronted, and both turn out to yield to the same trick.
`List.erase` and `List.eraseIdx` are plain recursions with usable equations
(`List.erase.eq_1/eq_2`, and `List.eraseIdx` reducible by `simp`), while
`List.findIdx` is a `List.brecOn` whose only *exposed* equation is the unrolling
equation `List.findIdx.eq_1` — but whose underlying `List.findIdx.go._f.eq_1` is
`@[defeq]`, so `simp [List.findIdx, List.findIdx.go]` recovers the cons case after
all.  `findIdx_cons` below is that recovered equation; it is duplicated from
`../FindIdx.lean`, where the same helper and its companion `findIdx_go_add` are
proved and kept.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.erase

universe u

variable {α : Type u}

/-! ## Recovering `findIdx`'s cons equation -/

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

private theorem findIdx_cons_true (p : α → Bool) (a : α) (t : List α) (h : p a = true) :
    List.findIdx p (a :: t) = 0 := by
  have hf := findIdx_cons p a t
  rw [hf]
  cases hpa : p a with
  | true => rfl
  | false => simp_all

private theorem findIdx_cons_false (p : α → Bool) (a : α) (t : List α) (h : p a = false) :
    List.findIdx p (a :: t) = 1 + List.findIdx p t := by
  have hf := findIdx_cons p a t
  rw [hf]
  cases hpa : p a with
  | true => simp_all
  | false => rfl

/-! ## `List.erase` as "cut at the first match" -/

/-- `erase` deletes at the index `findIdx` reports, and does nothing when there is
no such index.  Stated with `findIdx` repeated rather than bound by a `let`,
because repeating it is what makes `rw` able to replace the whole cut point in one
go. -/
private theorem erase_take_drop [BEq α] : ∀ (a : α) (l : List α),
    l.erase a
      = if l.findIdx (fun b => b == a) < l.length
        then List.take (l.findIdx (fun b => b == a)) l
          ++ List.drop (l.findIdx (fun b => b == a) + 1) l
        else l := by
  intro a l
  induction l with
  | nil => simp [List.findIdx.eq_1]
  | cons b t ih =>
    cases hba : b == a with
    | true =>
      have he : (b :: t).erase a = t := by simp [List.erase.eq_2, hba]
      have hf : List.findIdx (fun c => c == a) (b :: t) = 0 :=
        findIdx_cons_true _ b t hba
      rw [he, hf, ite_eq_left (by simp), List.take_zero, List.nil_append,
        List.drop_succ_cons, List.drop_zero]
    | false =>
      have he : (b :: t).erase a = b :: t.erase a := by
        simp [hba]
      rw [he]
      have hj : List.findIdx (fun c => c == a) (b :: t)
          = List.findIdx (fun c => c == a) t + 1 := by
        rw [findIdx_cons_false _ b t hba]
        omega
      rw [hj]
      by_cases hlt : List.findIdx (fun c => c == a) t < t.length
      · have hguard : List.findIdx (fun c => c == a) t + 1 < (b :: t).length := by
          rw [List.length_cons]
          omega
        rw [ite_eq_left hguard, List.take_succ_cons, List.drop_succ_cons]
        have ih' : t.erase a = List.take (List.findIdx (fun c => c == a) t) t
            ++ List.drop (List.findIdx (fun c => c == a) t + 1) t := by
          rw [ih, ite_eq_left hlt]
        rw [ih', List.cons_append]
      · have hguard : ¬(List.findIdx (fun c => c == a) t + 1 < (b :: t).length) := by
          rw [List.length_cons]
          omega
        rw [ite_eq_right hguard]
        have ih'' : t.erase a = t := by
          rw [ih, ite_eq_right hlt]
        rw [ih'']

/-! ## `byRec` -/

/-- The recursion written out, against `List.erase.eq_2`.  As with `find?`, the
library states the cons case as a `match a == x with` while the alternative
writes `if b == a then`, so the `Bool` has to be split on before `simp` can line
the two up. -/
private theorem rec_erase [BEq α] : ∀ (l : List α) (a : α), byRec l a = l.erase a := by
  intro l
  induction l with
  | nil => intro a; rfl
  | cons b t ih =>
    intro a
    cases hba : b == a with
    | true => simp [byRec, List.erase.eq_2, hba]
    | false => simp [byRec, hba, ih]

theorem byRec_eq_erase [BEq α] (l : List α) (a : α) : byRec l a = l.erase a := rec_erase l a

/-! ## `viaTakeDrop` -/

/-- Defeq: the alternative *is* `erase_take_drop` read backwards, `let` binding
and all. -/
theorem viaTakeDrop_eq_erase [BEq α] (l : List α) (a : α) : viaTakeDrop l a = l.erase a :=
  (erase_take_drop a l).symm

/-! ## `viaEraseIdx` -/

/- Attempted, not finished, and it fails in a way worth recording.

The route needs `List.eraseIdx l i = take i l ++ drop (i + 1) l` together with
the out-of-range case.  Both are *true* — `eraseIdx [1,2,3] 1 = [1,3]` and
`eraseIdx [1,2,3] 3 = [1,2,3]` — but `List.eraseIdx` is a `List.brecOn` through
`List.eraseIdx._f`, and `simp [List.eraseIdx]` does not reproduce the real cons
equation `eraseIdx (a :: t) (n + 1) = a :: eraseIdx t n`.  Worse, it appears to:
`simp [List.eraseIdx]` happily accepts

    eraseIdx (a :: t) (n + 1) = eraseIdx t n

which is **false** (`eraseIdx [1,2,3] 1 = [1,3]` but `eraseIdx [2,3] 0 = [3]`).
The proof goes through because both sides normalise to `eraseIdx._f` applications
whose `List.below` arguments are then identified by proof irrelevance.  So the
route cannot be closed with `simp`; the real cons equation has to be established
against `List.eraseIdx._f` directly, which is the same `brecOn` wall as
`List.span`.  Unfinished. -/

/-! ## `byFoldlLatch` -/

private def eraseLatchStep [BEq α] (a : α) (state : List α × Bool) (b : α) :=
  if b == a && !state.2 then (state.1, true) else (b :: state.1, state.2)

private theorem foldl_eraseLatchStep [BEq α] (a : α) : ∀ (l : List α)
    (state : List α × Bool),
    List.foldl (fun (acc, dropped) b =>
      if b == a && !dropped then (acc, true) else (b :: acc, dropped)) state l =
      List.foldl (eraseLatchStep a) state l := by
  intro l
  induction l with
  | nil => intro state; rfl
  | cons b t ih =>
    intro state
    rw [List.foldl_cons, List.foldl_cons]
    have hstep :
        (match state with
        | (acc, dropped) =>
          if b == a && !dropped then (acc, true) else (b :: acc, dropped)) =
          eraseLatchStep a state b := by
      cases state
      rfl
    rw [hstep, ih]

private theorem foldl_latch_erase [BEq α] (a : α) : ∀ (l acc : List α) (dropped : Bool),
    (List.foldl (eraseLatchStep a) (acc, dropped) l).1.reverse =
      acc.reverse ++ if dropped then l else l.erase a := by
  intro l
  induction l with
  | nil => intro acc dropped; cases dropped <;> simp
  | cons b t ih =>
    intro acc dropped
    simp only [List.foldl_cons]
    cases dropped with
    | true =>
      have hs : eraseLatchStep a (acc, true) b = (b :: acc, true) := by simp [eraseLatchStep]
      rw [hs]
      simpa [List.reverse_cons, List.append_assoc] using ih (b :: acc) true
    | false =>
      cases hb : (b == a) with
      | true =>
        have hs : eraseLatchStep a (acc, false) b = (acc, true) := by
          simp [eraseLatchStep, hb]
        rw [hs]
        simpa [List.erase_cons, hb] using ih acc true
      | false =>
        have hs : eraseLatchStep a (acc, false) b = (b :: acc, false) := by
          simp [eraseLatchStep, hb]
        rw [hs]
        simpa [List.erase_cons, hb, List.reverse_cons, List.append_assoc] using
          ih (b :: acc) false

/- Attempted, not finished.  This one avoids `findIdx` entirely — it is a pure
fold with a latch.  The invariant that closes it is: the accumulator, reversed,
is `acc.reverse ++` the list with *one* leading match deleted.  Expressing "one
leading match deleted" needs `takeWhile` / `dropWhile`, and both of those are
themselves `brecOn` with no exposed cons equation, so the statement drags in the
very obstruction this file was written to avoid.  The way around it would be to
state the invariant in `l.erase a`-shaped content, and then be circular.
Unfinished. -/

/-! ## Against the original -/

theorem byRec_eq_orig [BEq α] (l : List α) (a : α) : byRec l a = orig l a := rec_erase l a

theorem viaTakeDrop_eq_orig [BEq α] (l : List α) (a : α) : viaTakeDrop l a = orig l a :=
  viaTakeDrop_eq_erase l a

/-! ## Outstanding (stated, not proved) -/

/-!
The theorems below are the remaining routes.  Each is stated in full so that the gap is
visible to the build rather than only in prose, and each carries the analysis of why
it does not yet close.  The `sorry` is deliberate and temporary: this section is the
work list.  Every theorem outside it is fully proved.
-/

/-! ### `viaEraseIdx` -/

/-- Outstanding: not proved.  `simp [List.eraseIdx]` accepts the FALSE statement
`eraseIdx (a :: t) (n + 1) = eraseIdx t n` -- both sides normalise to
`eraseIdx._f` applications whose `List.below` arguments are then identified by
proof irrelevance.  (`eraseIdx [1,2,3] 1 = [1,3]` but `eraseIdx [2,3] 0 = [3]`.)
The real cons equation has to go against `eraseIdx._f` directly. -/
theorem viaEraseIdx_eq_orig [BEq α] (l : List α) (a : α) : viaEraseIdx l a = orig l a := by
  induction l with
  | nil => simp [viaEraseIdx, orig]
  | cons b t ih =>
    cases h : (b == a) with
    | false =>
      simp [viaEraseIdx, orig, List.findIdx_cons, h, List.erase_cons]
      exact ih
    | true =>
      simp [viaEraseIdx, orig, List.findIdx_cons, h, List.erase_cons]

/-! ### `byFoldlLatch` -/

/-- Outstanding: not proved.  The invariant is "the accumulator, reversed, is `acc.reverse ++` the list with
*one* leading match deleted".  Expressing "one leading match deleted" needs
`takeWhile`/`dropWhile`, both of which are `brecOn` with no exposed cons
equation, so the statement drags in the obstruction this file avoids. -/
theorem byFoldlLatch_eq_orig [BEq α] (l : List α) (a : α) : byFoldlLatch l a = orig l a := by
  unfold byFoldlLatch
  rw [foldl_eraseLatchStep]
  simpa [orig, eraseLatchStep] using foldl_latch_erase a l [] false

end Alt.List.erase
