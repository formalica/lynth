import Scripts.Test.Equiv.Nat.Add

/-!
# Proofs: `Nat.add` alternatives are equal to the original

All six alternatives in `../Add.lean` are proved equal to `a + b` here.

`recOnFirst`, `recOnSecond` and `viaSucc` carry a `termination_by`, so they are
compiled by well-founded recursion: `rfl` and `simp [def]` cannot reduce them and
only the equation lemmas (used with `rw`) work.  `recBoth` carries one too.

The two fold schemes are proved through a shared counting lemma — the step adds
`1` to the accumulator and ignores the element, so only `xs.length` matters.

`orig` is imported, not redefined.  No `sorry`, no `axiom`.
-/

namespace Alt.Nat.add

/-- Every element of the list contributes exactly `1` to the accumulator, so the
fold counts the list.  Both fold-based definitions reuse this. -/
private theorem foldl_len (xs : List ℕ) : ∀ (acc : ℕ),
    List.foldl (fun c _ => c + 1) acc xs = acc + xs.length := by
  induction xs with
  | nil => intro acc; rfl
  | cons x t ih => intro acc; rw [List.foldl_cons, ih, List.length_cons]; omega

theorem recOnFirst_eq (a b : ℕ) : recOnFirst a b = a + b := by
  induction a with
  | zero => rw [recOnFirst, Nat.zero_add]
  | succ n ih => rw [recOnFirst, ih, Nat.succ_add]

theorem recOnSecond_eq (a b : ℕ) : recOnSecond a b = a + b := by
  induction b with
  | zero => rw [recOnSecond, Nat.add_zero]
  | succ n ih => rw [recOnSecond, ih]; omega

theorem viaSucc_eq (a b : ℕ) : viaSucc a b = a + b := by
  induction a with
  | zero => rw [viaSucc, Nat.zero_add]
  | succ n ih => rw [viaSucc, ih, Nat.succ_add]

theorem recBoth_eq : ∀ (a b : ℕ), recBoth a b = a + b
  | 0, 0 => by rw [recBoth]
  | 0, b + 1 => by rw [recBoth, recBoth_eq]; omega
  | a + 1, 0 => by rw [recBoth, recBoth_eq]
  | a + 1, b + 1 => by rw [recBoth, recBoth_eq]; omega

theorem viaFoldr_eq (a b : ℕ) : viaFoldr a b = a + b := by
  rw [viaFoldr, foldl_len, List.length_replicate, Nat.add_comm]

/-- `addRange` is the same "add one per element" sweep written as its own
recursion, so `foldl_len` applies verbatim. -/
private theorem addRange_len (xs : List ℕ) (acc : ℕ) :
    viaRange.addRange xs acc = acc + xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x t ih => rw [viaRange.addRange, ih, List.length_cons]; omega

theorem viaRange_eq (a b : ℕ) : viaRange a b = a + b := by
  rw [viaRange, addRange_len, List.length_range, Nat.add_comm]

/-! ## Against the original -/

theorem recOnFirst_eq_orig (a b : ℕ) : recOnFirst a b = orig a b := recOnFirst_eq a b

theorem recOnSecond_eq_orig (a b : ℕ) : recOnSecond a b = orig a b := recOnSecond_eq a b

theorem viaSucc_eq_orig (a b : ℕ) : viaSucc a b = orig a b := viaSucc_eq a b

theorem recBoth_eq_orig (a b : ℕ) : recBoth a b = orig a b := recBoth_eq a b

theorem viaFoldr_eq_orig (a b : ℕ) : viaFoldr a b = orig a b := viaFoldr_eq a b

theorem viaRange_eq_orig (a b : ℕ) : viaRange a b = orig a b := viaRange_eq a b

end Alt.Nat.add
