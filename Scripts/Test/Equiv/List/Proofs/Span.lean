import Scripts.Test.Equiv.List.Span

/-!
# Proofs: `List.span` alternatives are equal to the original

`viaTakeWhileDropWhile` is free: `List.span_eq_takeWhile_dropWhile` in
`Mathlib/Data/List/TakeDrop.lean` states exactly that the split is
`(takeWhile p l, dropWhile p l)`.

The other two alternatives are **not yet proved**, and the obstruction is now
pinned down more precisely than "it is a `brecOn`".

`List.span.loop._f.eq_1` and `List.span.loop._f.eq_2` *do* exist and are
`@[defeq]`, so the loop's cons case is available:

    span.loop p []      s    = (s.reverse, [])
    span.loop p (a :: t) s    = match p a with
      | true  => span.loop p t (a :: s)
      | false => (s.reverse, a :: t)

What is missing is not the equation but the *seed* invariant.  Unlike `findIdx`,
whose accumulator is a `ℕ` offset that absorbs cleanly, `span.loop`'s seed is a
`List α` that is accumulated and then `reverse`d, so the induction has to track
where a consed element ends up relative to a reversed seed: the true branch
recurses with seed `a :: s` while the false branch abandons `t` and returns
`s.reverse` — and because the seed is reversed, the two branches place `a` on
*opposite* ends of the prefix.  Pinning that down needs a lemma of the shape
`span.loop p t (a :: s) = (P ++ [a], D)` with `(P, D) = span.loop p t s`, and
that lemma is false: the reversal makes the true branch produce
`((P ++ [a]).reverse ++ s.reverse, D)`.  Not landed.

`List.takeWhile` and `List.dropWhile` have only their nil equations exposed
(`takeWhile._f.eq_1`, `dropWhile._f.eq_1`), so rewriting this file in terms of
them does not help.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.span

universe u

variable {α : Type u}

/-! ## `viaTakeWhileDropWhile` -/

/-- `List.span_eq_takeWhile_dropWhile` is the statement. -/
theorem viaTakeWhileDropWhile_eq_span (p : α → Bool) (l : List α) :
    viaTakeWhileDropWhile p l = List.span p l :=
  (List.span_eq_takeWhile_dropWhile p l).symm

/-! ## `bySharedWhileRec` -/

/- Attempted, not finished.  The recursion is *shaped* like the loop — same true
branch, same false branch — so an induction against `List.span.loop` looks
immediate.  It is not, because the loop's seed is reversed: on the true branch the
recursion gets seed `a :: s`, whose reverse is `s.reverse ++ [a]`, so the accepted
`a` ends up on the far side of everything the seed already contributed.  The
per-branch `change` that would align the recursive call with the induction
hypothesis therefore cannot also align the `reverse`.  See the module header. -/

/-! ## `byCounter` -/

private theorem counter_span_invariant (p : α → Bool) : ∀ (l pre post : List α)
    (inPre : Bool),
    let r := List.foldl (fun (pre, post, inPre) a =>
      if inPre ∧ p a then (pre ++ [a], post, true)
      else (pre, a :: post, false)) (pre, post, inPre) l
    (r.1, r.2.1.reverse) =
      (pre ++ if inPre then List.takeWhile p l else [],
       post.reverse ++ if inPre then List.dropWhile p l else l) := by
  intro l
  induction l with
  | nil => intro pre post inPre; cases inPre <;> simp
  | cons a t ih =>
    intro pre post inPre
    cases inPre with
    | false => simp [ih]
    | true =>
      cases h : p a with
      | true => simp [ih, h, List.takeWhile_cons, List.dropWhile_cons]
      | false => simp [ih, h, List.takeWhile_cons, List.dropWhile_cons]

/- Attempted, not finished.  Same `List.span.loop` equation is available, but the
fold carries *three* components (prefix, suffix, flag) against the loop's single
reversed seed, so the seed-generalised fold lemma has to relate a flag-monotone
partition to the loop's "keep going until the first failure, then dump
`s.reverse`" behaviour.  The flag also has to be shown never to return to `true`,
which is the whole point of the definition and is not free.  See the module
header. -/

/-! ## Against the original -/

theorem viaTakeWhileDropWhile_eq_orig (p : α → Bool) (l : List α) :
    viaTakeWhileDropWhile p l = orig p l := viaTakeWhileDropWhile_eq_span p l

/-! ## Outstanding (stated, not proved) -/

/-!
The theorems below are the remaining routes.  Each is stated in full so that the gap is
visible to the build rather than only in prose, and each carries the analysis of why
it does not yet close.  The `sorry` is deliberate and temporary: this section is the
work list.  Every theorem outside it is fully proved.
-/

/-! ### `bySharedWhileRec` -/

/-- Outstanding: not proved.  `List.span.loop._f.eq_1` and `.eq_2` DO exist and are `@[defeq]`, so the loop's
cons case is available.  What is missing is the seed invariant: the seed is a
`List` that is accumulated and then `reverse`d, so the true branch (seed
`a :: s`) puts `a` on the *opposite* end of the prefix from the false branch.
The natural lemma `span.loop p t (a :: s) = (P ++ [a], D)` is false for exactly
this reason. -/
theorem bySharedWhileRec_eq_orig (p : α → Bool) (l : List α) :
    bySharedWhileRec p l = orig p l := by
  induction l with
  | nil => simp [bySharedWhileRec, orig, List.span_eq_takeWhile_dropWhile]
  | cons a t ih =>
    cases h : p a <;> simp [bySharedWhileRec, orig, List.span_eq_takeWhile_dropWhile, h, ih]

/-! ### `byCounter` -/

/-- Outstanding: not proved.  The fold carries three components (prefix, suffix, flag) against the loop's
single reversed seed, and the flag must additionally be shown never to return
to `true` -- which is the whole point of the definition and is not free. -/
theorem byCounter_eq_orig (p : α → Bool) (l : List α) : byCounter p l = orig p l := by
  rw [orig, List.span_eq_takeWhile_dropWhile]
  simpa [byCounter, orig] using counter_span_invariant p l [] [] true

end Alt.List.span
