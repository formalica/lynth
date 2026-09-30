import Scripts.Test.Equiv.List.Elem

/-!
# Proofs: `List.elem` alternatives are equal to the original

All seven alternatives in `../Elem.lean` are proved equal to `List.elem` here.

`viaCountPos` and `viaEraseLoop` need `[LawfulBEq α]`, because `List.count` and
`List.erase` test `x == a` while `List.elem` tests `a == x`; the two orders can
differ for an arbitrary `BEq`.  The other five need only `[BEq α]`.

`orig` is imported, not redefined.  No `sorry`, no `axiom`.
-/

namespace Alt.List.elem

universe u

variable {α : Type u}

/-! ## `direct` -/

theorem direct_eq [BEq α] (a : α) : ∀ (l : List α), direct a l = List.elem a l
  | [] => rfl
  | x :: t => by
    rw [direct, List.elem_cons, direct_eq a t]
    cases h : a == x <;> rfl

/-! ## `viaFoldl` -/

/-- Once the accumulator is `true` the step is the identity, so the fold returns
`true` whatever the rest of the list is. -/
private theorem latchT [BEq α] (a : α) (t : List α) :
    t.foldl (fun acc x => acc || (a == x)) true = true := by
  induction t with
  | nil => rfl
  | cons b u ihu => simp [List.foldl_cons, ihu]  -- latch absorbs

/-- Unlike `direct` this does not short-circuit: every element is tested.  The
`simp only [viaFoldl] at ih` is what lets the induction hypothesis be used —
without it the hypothesis is stated in terms of `viaFoldl` while the goal has
already been unfolded. -/
theorem viaFoldl_eq [BEq α] (a : α) (l : List α) : viaFoldl a l = List.elem a l := by
  induction l with
  | nil => rw [viaFoldl, List.foldl_nil, List.elem_nil]
  | cons x t ih =>
    simp only [viaFoldl] at ih ⊢
    rw [List.foldl_cons, List.elem_cons]
    cases h : a == x
    · rw [Bool.false_or]; exact ih
    · simp [latchT a t]

/-! ## `viaFoldr` -/

/-- The same latch, right to left.  `foldr` hands the head the accumulator built
for the tail, so the head's own test is the *outer* one. -/
private theorem latchT' [BEq α] (a : α) (t : List α) :
    t.foldr (fun x acc => (a == x) || acc) true = true := by
  induction t with
  | nil => rfl
  | cons b u ihu => simp [List.foldr_cons, ihu]

theorem viaFoldr_eq [BEq α] (a : α) (l : List α) : viaFoldr a l = List.elem a l := by
  induction l with
  | nil => rw [viaFoldr, List.foldr_nil, List.elem_nil]
  | cons x t ih =>
    simp only [viaFoldr] at ih ⊢
    rw [List.foldr_cons, List.elem_cons]
    cases h : a == x
    · rw [Bool.false_or]; exact ih
    · simp

/-! ## The `BEq` direction

Everything below that goes through `List.count` or `List.erase` needs the two
orders of `==` to agree. -/

/-- `LawfulBEq` pins both directions to `a = b`, and `Bool` has only two values,
so the two orders cannot differ. -/
private theorem beq_comm [BEq α] [LawfulBEq α] (a b : α) : (a == b) = (b == a) := by
  cases h : a == b <;> cases hb : b == a
  · rfl
  · exact absurd (beq_iff_eq.mpr ((beq_iff_eq.mp hb).symm)) (by simp [h])
  · exact absurd (beq_iff_eq.mpr ((beq_iff_eq.mp h).symm)) (by simp [hb])
  · rfl

/-! ## `viaCountPos` -/

/-- `decide (List.count a l > 0)` is the `Bool` form of `a ∈ l`, and
`List.elem a l` is the same thing.  The `bool` cases of `simp` close the
arithmetic because a hit adds `1` and a miss adds `0`. -/
private theorem count_pos [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    decide (List.count a l > 0) = List.elem a l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [List.count_cons, List.elem_cons]
    rw [show (x == a) = (a == x) from beq_comm x a]
    cases a == x <;> simp

theorem viaCountPos_eq [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaCountPos a l = List.elem a l := by
  rw [viaCountPos, count_pos]

/-! ## `viaFilterEmpty` -/

/-- `filter` keeps exactly the elements equal to `a`, so the result is empty iff
`a` is not in the list; `isEmpty == false` is the double negation of that. -/
theorem viaFilterEmpty_eq [BEq α] (a : α) (l : List α) :
    viaFilterEmpty a l = List.elem a l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [viaFilterEmpty] at ih ⊢
    rw [List.filter_cons, List.elem_cons]
    cases a == x <;> simp [ih]

/-! ## `viaFindIdx` -/

/-- The guard `≠ l.length` is what makes this work: `findIdx` returns `l.length`
exactly when nothing matched, and `(n + 1) != (m + 1)` reduces to `n != m`, so
the cons case is the induction hypothesis verbatim. -/
theorem viaFindIdx_eq [BEq α] (a : α) (l : List α) :
    viaFindIdx a l = List.elem a l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [viaFindIdx] at ih ⊢
    rw [List.findIdx_cons, List.elem_cons]
    cases a == x <;> simp [ih]

/-! ## `viaErase` and `viaEraseLoop` -/

/-- `viaErase` is compiled through `Nat.brecOn`, so neither boundary case is
reducible by `rfl` alone; `simp` cannot see through the recursor either. -/
private theorem viaErase_zero [BEq α] (a : α) (l : List α) :
    viaErase 0 a l = false := rfl

private theorem viaErase_nil [BEq α] (n : ℕ) (a : α) : viaErase n a [] = false := by
  cases n <;> rfl

/-- Erasing shortens the list exactly when an occurrence was removed, which by
symmetry of `==` is exactly `a ∈ t`.  This is the bridge the loop needs: the
`if` in `viaErase` asks about lengths, not about `elem`. -/
private theorem erase_len [BEq α] [LawfulBEq α] (a : α) : ∀ (t : List α),
    ((t.erase a).length < t.length) ↔ a ∈ t
  | [] => by simp
  | x :: t => by
    rw [List.erase_cons, List.mem_cons]
    rw [show (x == a) = (a == x) from beq_comm x a]
    by_cases h : (a == x) = true
    · rw [ite_eq_left h]
      simp only [List.length_cons]
      have hax : a = x := beq_iff_eq.mp h
      constructor
      · intro _; exact Or.inl hax
      · intro _; omega
    · rw [ite_eq_right h]
      simp only [List.length_cons]
      rw [Nat.succ_lt_succ_iff, erase_len a t]
      constructor
      · intro hab; exact Or.inr hab
      · intro hh; exact hh.resolve_left (fun hh' => h (beq_iff_eq.mpr hh'))

/-- Induction on the **fuel**, with the list generalised and `l.length ≤ n`
tying the two together — a list induction would have nothing to decrease on. -/
private theorem erase_mem [BEq α] [LawfulBEq α] (a : α) : ∀ (n : ℕ) (l : List α),
    l.length ≤ n → (viaErase n a l = true ↔ a ∈ l)
  | 0, l, h => by
    have hl : l = [] := by
      cases l with
      | nil => rfl
      | cons x t => simp at h
    subst hl
    rw [viaErase_zero]
    simp
  | n + 1, [], _ => by rw [viaErase_nil]; simp
  | n + 1, x :: t, h => by
    have ht : t.length ≤ n := by simp only [List.length_cons] at h; omega
    simp only [viaErase]
    by_cases hx : (x == a) = true
    · have hE : (x :: t).erase a = t := by
        rw [List.erase_cons, ite_eq_left hx]
      have hx' : (a == x) = true := (beq_comm a x).trans hx
      have hax : a = x := beq_iff_eq.mp hx'
      rw [hE]
      simp only [List.length_cons]
      rw [List.mem_cons]
      rw [ite_eq_left (show t.length < t.length + 1 by omega)]
      constructor
      · intro _; exact Or.inl hax
      · intro _; rfl
    · have hxf : (x == a) = false := Bool.eq_false_of_not_eq_true hx
      have hE : (x :: t).erase a = x :: t.erase a := by
        rw [List.erase_cons, ite_eq_right hx]
      have hx' : (a == x) = false := (beq_comm a x).trans hxf
      have hT : (a == x) ≠ true := by simp [hx']
      have hax : ¬(a = x) := fun hh => hT (beq_iff_eq.mpr hh)
      rw [hE]
      simp only [List.length_cons]
      rw [List.mem_cons]
      by_cases hP : (t.erase a).length + 1 < t.length + 1
      · rw [ite_eq_left hP]
        have hlt : (t.erase a).length < t.length := by omega
        have hmem : a ∈ t := (erase_len a t).mp hlt
        constructor
        · intro _; exact Or.inr hmem
        · intro _; rfl
      · rw [ite_eq_right hP]
        rw [erase_mem a n t ht]
        constructor
        · intro hab; exact Or.inr hab
        · intro hh; exact hh.resolve_left hax

/-- The fuel loop in `Bool` form.  `Bool.eq_iff_iff` and `List.elem_iff` turn
the statement into the membership form `erase_mem` proves. -/
theorem viaErase_eq [BEq α] [LawfulBEq α] (a : α) (n : ℕ) (l : List α) (h : l.length ≤ n) :
    viaErase n a l = List.elem a l := by
  rw [Bool.eq_iff_iff, List.elem_iff]
  exact erase_mem a n l h

theorem viaEraseLoop_eq [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaEraseLoop a l = List.elem a l := by
  rw [viaEraseLoop, Bool.eq_iff_iff, List.elem_iff]
  exact erase_mem a l.length l (Nat.le_refl _)

/-! ## Against the original -/

theorem direct_eq_orig [BEq α] (a : α) (l : List α) : direct a l = orig a l :=
  direct_eq a l

theorem viaFoldl_eq_orig [BEq α] (a : α) (l : List α) : viaFoldl a l = orig a l :=
  viaFoldl_eq a l

theorem viaFoldr_eq_orig [BEq α] (a : α) (l : List α) : viaFoldr a l = orig a l :=
  viaFoldr_eq a l

theorem viaCountPos_eq_orig [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaCountPos a l = orig a l :=
  viaCountPos_eq a l

theorem viaFilterEmpty_eq_orig [BEq α] (a : α) (l : List α) :
    viaFilterEmpty a l = orig a l :=
  viaFilterEmpty_eq a l

theorem viaFindIdx_eq_orig [BEq α] (a : α) (l : List α) :
    viaFindIdx a l = orig a l :=
  viaFindIdx_eq a l

theorem viaErase_eq_orig [BEq α] [LawfulBEq α] (a : α) (n : ℕ) (l : List α) (h : l.length ≤ n) :
    viaErase n a l = List.elem a l :=
  viaErase_eq a n l h

theorem viaEraseLoop_eq_orig [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaEraseLoop a l = orig a l :=
  viaEraseLoop_eq a l

end Alt.List.elem
