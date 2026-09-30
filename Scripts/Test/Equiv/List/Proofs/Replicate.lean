import Scripts.Test.Equiv.List.Replicate

/-!
# Proofs: `List.replicate` alternatives are equal to the original

All four alternatives in `../Replicate.lean` are proved equal to `List.replicate`
here.  Two of them are one-liners over `List.map_const`; `byFoldlRev` needs a
seed-generalised fold lemma of the kind used throughout `List/Proofs/`.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.replicate

universe u

variable {α : Type u}

/-! ## `byRangeMap` -/

/-- The position list has the requested length, and mapping a constant over a
list is `List.replicate` at that length. -/
theorem byRangeMap_eq_replicate (n : ℕ) (a : α) : byRangeMap n a = List.replicate n a := by
  have h1 : (List.range n).map (fun _ : ℕ => a)
      = List.replicate (List.range n).length a := by
    rw [show (fun _ : ℕ => a) = Function.const ℕ a from rfl, List.map_const]
  rw [byRangeMap, h1]
  simp only [List.length_range]

/-! ## `byOfFn` -/

/-- `List.ofFn_succ` peels off the fresh position and leaves the rest to the
induction hypothesis; the enumerated function ignores its argument, so the tail
is still a constant function. -/
theorem byOfFn_eq_replicate : ∀ (n : ℕ) (a : α), byOfFn n a = List.replicate n a := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ k ih =>
    intro a
    rw [byOfFn, List.ofFn_succ, List.replicate_succ]
    exact congrArg (fun L => a :: L) (ih a)

/-! ## `byFoldlRev` -/

/-- A left fold that conses the copy onto the front of the accumulator ends up
holding the reverse of the copies, followed by whatever was there before.  The
seed has to be generalised, as in `Filter.lean`: on a cons the recursion runs at
the seed `a :: init`. -/
private theorem foldl_replicate (a : α) : ∀ (init : List α) (l : List ℕ),
    l.foldl (fun acc _ => a :: acc) init = List.replicate l.length a ++ init := by
  intro init l
  induction l generalizing init with
  | nil => simp
  | cons b t ih =>
    rw [List.foldl_cons, ih, List.length_cons, List.replicate_add, List.replicate_one]
    rw [← show ([a] : List α) ++ init = a :: init from rfl, ← List.append_assoc]

theorem byFoldlRev_eq_replicate (n : ℕ) (a : α) : byFoldlRev n a = List.replicate n a := by
  rw [byFoldlRev, foldl_replicate, List.append_nil, List.reverse_replicate]
  simp only [List.length_range]

/-! ## `bySuccRec` -/

theorem bySuccRec_eq_replicate : ∀ (n : ℕ) (a : α), bySuccRec n a = List.replicate n a := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ k ih =>
    intro a
    rw [bySuccRec, List.replicate_succ]
    exact congrArg (fun L => a :: L) (ih a)

/-! ## Against the original -/

theorem byOfFn_eq_orig (n : ℕ) (a : α) : byOfFn n a = orig n a := byOfFn_eq_replicate n a

theorem byRangeMap_eq_orig (n : ℕ) (a : α) : byRangeMap n a = orig n a :=
  byRangeMap_eq_replicate n a

theorem byFoldlRev_eq_orig (n : ℕ) (a : α) : byFoldlRev n a = orig n a :=
  byFoldlRev_eq_replicate n a

theorem bySuccRec_eq_orig (n : ℕ) (a : α) : bySuccRec n a = orig n a :=
  bySuccRec_eq_replicate n a

end Alt.List.replicate
