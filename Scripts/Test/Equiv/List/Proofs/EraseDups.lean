import Scripts.Test.Equiv.List.EraseDups

/-!
# Proofs: `List.eraseDups` alternatives are equal to the original

`viaFilterDups` and `byFoldlRev` are proved here.  The latter needs
`[LawfulBEq α]`: its membership test compares the accumulator element with the
new element, while `eraseDups` compares the new tail element with the retained
head.  Those directions agree only for a lawful equality test.  A third route,
`byRevFoldlFirst`, was removed because it was *false*.

`filterDupsFuel` is public in the definition file precisely so that the fuel
lemma can be stated here; the definition files otherwise contain no helpers.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.eraseDups

universe u

variable {α : Type u}

/-! ## `viaFilterDups` -/

/-- With enough fuel the fuelled recursion is `List.eraseDups`.  `List.eraseDups_cons`
is exactly the recursion equation, so all that is left is the fuel arithmetic.
The nil case at fuel `0` is unreachable in practice — the caller always supplies
`l.length` — but it has to be handled, and it is the reason the fuel appears in
the statement at all. -/
private theorem fuel_eraseDups [BEq α] : ∀ (fuel : ℕ) (l : List α), l.length ≤ fuel →
    filterDupsFuel fuel l = List.eraseDups l := by
  intro fuel
  induction fuel with
  | zero =>
    intro l h
    have hl : l = [] := by
      cases l with
      | nil => rfl
      | cons a t => simp at h
    subst hl
    rfl
  | succ n ih =>
    intro l h
    cases l with
    | nil => rfl
    | cons a t =>
      rw [List.eraseDups_cons, filterDupsFuel]
      refine congrArg (fun z => a :: z) (ih _ ?_)
      exact le_trans (List.length_filter_le _ _) (by simp at h; omega)

theorem viaFilterDups_eq_eraseDups [BEq α] (l : List α) :
    viaFilterDups l = List.eraseDups l :=
  fuel_eraseDups l.length l le_rfl

/-! ## `byFoldlRev` -/

/- The generic theorem without `LawfulBEq` is false: the fold tests existing
elements against the new one, while `eraseDups` tests the new element against
each retained element. -/

private theorem beq_comm_of_lawful [BEq α] [LawfulBEq α] (a b : α) :
    (a == b) = (b == a) := by
  cases h : (a == b) <;> cases h' : (b == a)
  · rfl
  · have hba : b = a := LawfulBEq.eq_of_beq h'
    subst b
    simp at h
  · have hab : a = b := LawfulBEq.eq_of_beq h
    subst b
    simp at h'
  · rfl

private theorem any_beq_comm [BEq α] [LawfulBEq α] (acc : List α) (a : α) :
    List.any acc (fun b => b == a) = List.any acc (fun b => a == b) := by
  induction acc with
  | nil => rfl
  | cons b t ih =>
    simp only [List.any_cons]
    rw [beq_comm_of_lawful b a, ih]

private theorem foldl_rev_loop [BEq α] [LawfulBEq α] :
    ∀ (l acc : List α),
      (List.foldl (fun acc a =>
        if List.any acc (fun b => b == a) then acc else a :: acc) acc l).reverse =
        List.eraseDupsBy.loop (fun x y => x == y) l acc := by
  intro l
  induction l with
  | nil => intro acc; simp [List.eraseDupsBy.loop.eq_1]
  | cons a t ih =>
    intro acc
    simp only [List.foldl_cons, List.eraseDupsBy.loop.eq_2]
    rw [any_beq_comm]
    cases h : List.any acc (fun b => a == b) with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih (a :: acc)
    | true =>
      simp only [↓reduceIte]
      exact ih acc

/-! ## Against the original -/

theorem viaFilterDups_eq_orig [BEq α] (l : List α) : viaFilterDups l = orig l :=
  viaFilterDups_eq_eraseDups l

/-! ## Against the original -/

/-- The statement requires `LawfulBEq`: for an arbitrary `BEq`, the fold checks
`b == a` while `eraseDups` checks `a == b`, and these tests need not agree. -/
theorem byFoldlRev_eq_orig [BEq α] [LawfulBEq α] (l : List α) :
    byFoldlRev l = orig l := by
  simp only [byFoldlRev, orig, List.eraseDups]
  exact foldl_rev_loop l []

end Alt.List.eraseDups
