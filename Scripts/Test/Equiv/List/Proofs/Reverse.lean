import Scripts.Test.Equiv.List.Reverse

/-!
# Proofs: `List.reverse` alternatives are equal to the original

All eight alternatives in `../Reverse.lean` are proved equal to `List.reverse`
here — `orig` is imported, not redefined.  No `sorry`, no `axiom`.
-/

namespace Alt.List.reverse

variable {α : Type u}

/-! ## `withAcc` and `direct` -/

/-- The textbook accumulator recursion, stated with the accumulator as a second
parameter so the induction can be done on the list alone.  This single lemma
also discharges `direct`, which is `withAcc` at the empty accumulator. -/
theorem withAcc_eq (l : List α) (acc : List α) : withAcc l acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => simp [withAcc]
  | cons a t ih => simp [withAcc, ih]

theorem direct_eq (l : List α) : direct l = List.reverse l := by
  simp only [direct, withAcc_eq, List.append_nil]

/-! ## `viaFoldl` -/

/-- The same accumulator idea driven by the library, consing onto the *front*,
so the seed has to be generalised: on a cons the recursion runs at seed
`a :: init`.  Compare the `foldl_rev` in `../Proofs/Map.lean`, which is the same
lemma for `map`. -/
private theorem foldl_rev (acc : List α) (l : List α) :
    l.foldl (fun acc x => x :: acc) acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, ih, List.reverse_cons, List.cons_append,
      List.append_assoc, List.nil_append]

theorem viaFoldl_eq (l : List α) : viaFoldl l = List.reverse l := by
  simp only [viaFoldl, foldl_rev, List.append_nil]

/-! ## `viaAppend` -/

/-- The naive quadratic recursion: reverse the tail, then append the head at the
*end*.  Correct, and much slower than the linear versions. -/
theorem viaAppend_eq (l : List α) : viaAppend l = List.reverse l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [viaAppend, ih, List.reverse_cons]

/-! ## `viaFoldrAppend` -/

/-- `foldr` appends instead of consing, so the accumulator of the tail reaches
the head last.  The `simp only [viaFoldrAppend] at ih` is needed because the
inductive hypothesis is stated in terms of the definition while the goal has
already been unfolded. -/
theorem viaFoldrAppend_eq (l : List α) : viaFoldrAppend l = List.reverse l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [viaFoldrAppend] at ih
    simp only [viaFoldrAppend, List.foldr_cons, ih, List.reverse_cons]

/-! ## `viaIndexScan` and `viaIndex` -/

/-- The step is `cons`, so the `foldr` is just `map` with the seed parked on the
right.  Stated over an arbitrary index list, which is what makes the induction
on `l` below go through with a fixed seed. -/
private theorem foldr_cons_map (f : ℕ → γ) : ∀ (s : List ℕ) (acc : List γ),
    List.foldr (fun i acc => f i :: acc) acc s = List.map f s ++ acc
  | [], _ => rfl
  | i :: t, acc => by
      simp only [List.foldr_cons, List.map_cons, List.cons_append]
      rw [foldr_cons_map f t]

/-- The mirror index `l.length - 1 - i`, read at every `i` of the range, is the
reverse — as a `map`, so `List.range_succ` plus `List.map_append` is enough.  The
cons case needs `List.map_congr_left`, because `f` for `a :: t` and `f` for `t`
are different lambdas that happen to agree on `i < t.length`; there
`List.getElem?_cons_succ` and `omega` carry the index across. -/
private theorem scan_map (l : List α) :
    (List.range l.length).map (fun i => l[l.length - 1 - i]?) =
      List.map Option.some l.reverse := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.length_cons]
    rw [List.range_succ, List.map_append]
    rw [List.reverse_cons, List.map_append]
    have hpt : ∀ i ∈ List.range t.length,
        (a :: t)[t.length + 1 - 1 - i]? = t[t.length - 1 - i]? := by
      intro i hi
      have hlt : i < t.length := List.mem_range.mp hi
      have h1 : t.length + 1 - 1 - i = t.length - i := by omega
      rw [h1]
      have h2 : t.length - i = (t.length - i - 1) + 1 := by omega
      rw [h2, List.getElem?_cons_succ]
      exact congrArg (fun k => t[k]?) (by omega)
    rw [List.map_congr_left hpt, ih]
    simp

/-- Every probe is in range, so the `none`s never appear. -/
theorem viaIndexScan_eq (l : List α) : viaIndexScan l = List.map Option.some l.reverse := by
  simp only [viaIndexScan]
  rw [foldr_cons_map, scan_map, List.append_nil]

/-- Dropping the `none`s of a list of `some`s. -/
theorem viaIndex_eq (l : List α) : viaIndex l = List.reverse l := by
  simp only [viaIndex, viaIndexScan_eq]
  rw [List.filterMap_map]
  simp [Function.comp, List.filterMap_some]

/-! ## `viaPeel` and `viaDrop` -/

/-- The decomposition the peel loop needs.  `l.getLast? = some x` says `x` is the
last element, and the reverse is then `x` consed onto the reverse of everything
before it — which is exactly `l.dropLast`.  Case analysis twice: `l = []` is
impossible, `l = [a]` is `rfl`, and the two-element case peels one cons off both
sides and invokes itself on the remainder.

Note `List.tail_reverse` (`l.reverse.tail = l.dropLast.reverse`) says the same
thing, but going through it would still need the head, so the two-level case
analysis is the shorter route. -/
private theorem reverse_eq_cons_dropLast (l : List α) (x : α) (h : l.getLast? = some x) :
    l.reverse = x :: l.dropLast.reverse := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil =>
      have hax : a = x := by simpa [List.getLast?] using h
      rw [hax]
      rfl
    | cons b u =>
      have IH := reverse_eq_cons_dropLast (b :: u) x h
      calc
        (a :: b :: u).reverse = (b :: u).reverse ++ [a] := List.reverse_cons
        _ = (x :: (b :: u).dropLast.reverse) ++ [a] := by rw [IH]
        _ = x :: ((b :: u).dropLast.reverse ++ [a]) := List.cons_append
        _ = x :: (a :: (b :: u).dropLast).reverse := by rw [List.reverse_cons]
        _ = x :: (a :: b :: u).dropLast.reverse := by rw [← List.dropLast_cons_cons]

/-- Induction on the **fuel**, which is what `viaPeel` actually recurses on, with
the list and accumulator generalised and `l.length = n` tying them together —
so the fuel is always exactly enough, and `l.dropLast.length = n - 1` hands the
induction hypothesis the right call.

The accumulator goes on the **left**: each step appends the freshly peeled
element, so the peels accumulate to `acc ++ l.reverse`, not `l.reverse ++ acc`.
Getting that backwards is the trap here — `viaPeel 1 [a] [c]` returns `[c, a]`,
which is `acc ++ [a]` and not `[a] ++ acc`. -/
theorem viaPeel_eq (n : ℕ) (l : List α) (acc : List α) (h : l.length = n) :
    viaPeel n l acc = acc ++ l.reverse := by
  induction n generalizing l acc with
  | zero =>
    cases l with
    | nil => simp [viaPeel]
    | cons a t => simp at h
  | succ k ih =>
    cases l with
    | nil => simp only [List.length_nil] at h; omega
    | cons a t =>
      cases hg : (a :: t).getLast? with
      | none => simp [List.getLast?_eq_none_iff] at hg
      | some x =>
        simp only [viaPeel, hg]
        rw [ih (a :: t).dropLast (acc ++ [x]) (by simpa [List.length_dropLast_cons] using h)]
        rw [List.append_assoc]
        rw [List.singleton_append]
        rw [reverse_eq_cons_dropLast (a :: t) x hg]

/-- Fuel `l.length` is exactly right, so the loop peels the whole list. -/
theorem viaDrop_eq (l : List α) : viaDrop l = List.reverse l := by
  simp only [viaDrop, viaPeel_eq l.length l [] rfl, List.nil_append]

/-! ## Against the original -/

theorem direct_eq_orig (l : List α) : direct l = orig l := direct_eq l

theorem viaFoldl_eq_orig (l : List α) : viaFoldl l = orig l := viaFoldl_eq l

theorem viaAppend_eq_orig (l : List α) : viaAppend l = orig l := viaAppend_eq l

theorem viaFoldrAppend_eq_orig (l : List α) : viaFoldrAppend l = orig l := viaFoldrAppend_eq l

theorem viaPeel_eq_orig (l : List α) : viaPeel l.length l [] = orig l := by
  simp only [viaPeel_eq l.length l [] rfl, List.nil_append, orig]

theorem viaDrop_eq_orig (l : List α) : viaDrop l = orig l := viaDrop_eq l

theorem viaIndexScan_eq_orig (l : List α) : viaIndexScan l = List.map Option.some (orig l) :=
  viaIndexScan_eq l

theorem viaIndex_eq_orig (l : List α) : viaIndex l = orig l := viaIndex_eq l

end Alt.List.reverse
