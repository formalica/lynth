import Scripts.Test.Equiv.List.Count

/-!
# Proofs: `List.count` alternatives are equal to the original

`List.count a l` tests `x == a` (element first); every alternative in
`../Count.lean` except `viaErase` tests `a == x` (value first).  The two orders
agree exactly when `BEq` is symmetric, so six of the seven are proved under
`[LawfulBEq α]` — which is also the setting where counting anything is
meaningful.  Without the law they are genuinely false: a `BEq` with
`t == f = true` and `f == t = false` gives `List.count f [t] = 1` but
`direct f [t] = 0`.  `viaEraseLoop` is the exception — it already guards with
`x == a`, so it is proved for a bare `[BEq α]`.

`orig` is imported, not redefined.  No `sorry`, no `axiom`.
-/

namespace Alt.List.count

universe u

variable {α : Type u}

/-! ## The `BEq` direction -/

/-- `LawfulBEq` pins both directions to `a = b`, and `Bool` has only two values,
so the two orders cannot differ. -/
private theorem beq_comm [BEq α] [LawfulBEq α] (a b : α) : (a == b) = (b == a) := by
  cases h : a == b <;> cases hb : b == a
  · rfl
  · exact absurd (beq_iff_eq.mpr ((beq_iff_eq.mp hb).symm)) (by simp [h])
  · exact absurd (beq_iff_eq.mpr ((beq_iff_eq.mp h).symm)) (by simp [hb])
  · rfl

/-- `List.count_cons` guards on `x == a`; the definitions guard on `a == x`. -/
private theorem count_cons' [BEq α] [LawfulBEq α] (a x : α) (t : List α) :
    List.count a (x :: t) = List.count a t + if a == x then 1 else 0 := by
  rw [List.count_cons, beq_comm x a]

/-! ## `direct` -/

theorem direct_eq [BEq α] [LawfulBEq α] (a : α) : ∀ (l : List α), direct a l = List.count a l
  | [] => rfl
  | x :: t => by
    rw [direct, count_cons' a x t, direct_eq a t]
    cases a == x <;> simp

/-! ## `viaFoldl` -/

/-- Seed-generalised: on a cons the head is folded onto the accumulator before
the tail is visited, so an induction fixing the seed has nothing to rewrite
with. -/
private theorem foldl_count [BEq α] [LawfulBEq α] (a : α) :
    ∀ (acc : ℕ) (l : List α),
      l.foldl (fun acc x => if a == x then acc + 1 else acc) acc = acc + List.count a l
  | acc, [] => by simp
  | acc, x :: t => by
    rw [List.foldl_cons, foldl_count a, count_cons' a x t]
    cases a == x <;> simp [Nat.add_comm, Nat.add_left_comm]

theorem viaFoldl_eq [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaFoldl a l = List.count a l := by
  rw [viaFoldl, foldl_count a]
  simp

/-! ## `viaFoldr` -/

private theorem foldr_count [BEq α] [LawfulBEq α] (a : α) :
    ∀ (l : List α) (acc : ℕ),
      l.foldr (fun x acc => if a == x then acc + 1 else acc) acc = List.count a l + acc
  | [], acc => by simp
  | x :: t, acc => by
    rw [List.foldr_cons, foldr_count a, count_cons' a x t]
    cases a == x <;> simp [Nat.add_assoc, Nat.add_comm]

theorem viaFoldr_eq [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaFoldr a l = List.count a l := by
  rw [viaFoldr, foldr_count a]
  simp

/-! ## `viaCountP` -/

/-- The two predicates are the same up to the order of the comparison. -/
theorem viaCountP_eq [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaCountP a l = List.count a l := by
  simp only [viaCountP, List.count]
  exact List.countP_congr (fun x _ => by rw [beq_comm])

/-! ## `viaFilterLength` -/

theorem viaFilterLength_eq [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaFilterLength a l = List.count a l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [viaFilterLength] at ih ⊢
    rw [List.filter_cons, count_cons' a x t]
    cases a == x <;> simp [ih]

/-! ## `viaElemSum` -/

theorem viaElemSum_eq [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaElemSum a l = List.count a l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [viaElemSum] at ih ⊢
    rw [List.map_cons, List.sum_cons, count_cons' a x t,
      List.elem_cons, List.elem_nil]
    cases a == x <;> simp [ih, Nat.add_comm]

/-! ## `viaErase` and `viaEraseLoop` -/

/-- Induction on the **fuel**, with the list generalised and `l.length ≤ n`
tying them together.  This one needs no `LawfulBEq`: its guard is `x == a`, the
same order `List.count` and `List.erase_cons` use, and `erase` really does drop
the head when that guard holds, so the `match` on the result is a case split on
the tail. -/
private theorem erase_count [BEq α] (a : α) : ∀ (n : ℕ) (l : List α),
    l.length ≤ n → viaErase n a l = List.count a l
  | 0, l, h => by
    cases l with
    | nil => rfl
    | cons x t => simp at h
  | n + 1, [], _ => rfl
  | n + 1, x :: t, h => by
    have ht : t.length ≤ n := by simp only [List.length_cons] at h; omega
    cases hx : x == a
    · simp only [viaErase, List.count_cons]
      simp [hx, erase_count a n t ht]
    · simp only [viaErase]
      rw [ite_eq_left hx]
      rw [List.erase_cons]
      rw [ite_eq_left hx]
      cases t with
      | nil => rw [List.count_cons]; simp [hx]
      | cons b u =>
        have hb : (b :: u).length ≤ n := by simp only [List.length_cons] at ht; omega
        rw [List.count_cons]
        simp [hx, erase_count a n (b :: u) hb, Nat.add_comm]

theorem viaErase_eq [BEq α] (a : α) (l : List α) :
    viaEraseLoop a l = List.count a l :=
  erase_count a l.length l (Nat.le_refl _)

/-! ## Against the original -/

theorem direct_eq_orig [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    direct a l = orig a l := direct_eq a l

theorem viaFoldl_eq_orig [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaFoldl a l = orig a l := viaFoldl_eq a l

theorem viaFoldr_eq_orig [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaFoldr a l = orig a l := viaFoldr_eq a l

theorem viaCountP_eq_orig [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaCountP a l = orig a l := viaCountP_eq a l

theorem viaFilterLength_eq_orig [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaFilterLength a l = orig a l := viaFilterLength_eq a l

theorem viaElemSum_eq_orig [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    viaElemSum a l = orig a l := viaElemSum_eq a l

theorem viaEraseLoop_eq_orig [BEq α] (a : α) (l : List α) :
    viaEraseLoop a l = orig a l := viaErase_eq a l

end Alt.List.count
