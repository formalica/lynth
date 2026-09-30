import Scripts.Test.Equiv.Nat.Mul

/-!
# Proofs: `Nat.mul` alternatives are equal to the original

All six alternatives in `../Mul.lean` are proved equal to `a * b` here.

`recOnFirst` and `recOnSecond` carry a `termination_by` and so are well-founded
recursions: only the equation lemmas work on them.  The four list-based schemes
all reduce to one counting lemma — the step adds a fixed `a` once per element, so
only the list's `length` survives.

`orig` is imported, not redefined.  No `sorry`, no `axiom`.
-/

namespace Alt.Nat.mul

theorem recOnSecond_eq (a b : ℕ) : recOnSecond a b = a * b := by
  induction b with
  | zero => rw [recOnSecond, Nat.mul_zero]
  | succ n ih => rw [recOnSecond, ih, Nat.mul_succ, Nat.add_comm]

theorem recOnFirst_eq (a b : ℕ) : recOnFirst a b = a * b := by
  induction a with
  | zero => rw [recOnFirst, Nat.zero_mul]
  | succ n ih => rw [recOnFirst, ih, Nat.succ_mul, Nat.add_comm]

/-- `acc + a` once per element, so `acc + xs.length * a`.  The seed is
generalised because `foldl_cons` folds the head onto the seed *before* visiting
the tail. -/
private theorem foldl_add (a : ℕ) (xs : List ℕ) : ∀ (acc : ℕ),
    List.foldl (fun c _ => c + a) acc xs = acc + xs.length * a := by
  induction xs with
  | nil => intro acc; rw [List.length_nil, Nat.zero_mul, Nat.add_zero]; rfl
  | cons x t ih =>
    intro acc
    rw [List.foldl_cons, ih, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem viaRangeOnB_eq (a b : ℕ) : viaRangeOnB a b = a * b := by
  rw [viaRangeOnB, foldl_add, List.length_range, Nat.zero_add, Nat.mul_comm]

theorem viaRangeOnA_eq (a b : ℕ) : viaRangeOnA a b = a * b := by
  rw [viaRangeOnA, foldl_add, List.length_range, Nat.zero_add]

/-- `List.replicate n a` has `n` copies of `a`, so its sum is `n * a`. -/
private theorem sum_replicate (n : ℕ) (a : ℕ) : (List.replicate n a).sum = n * a := by
  induction n with
  | zero => rw [List.replicate_zero, List.sum_nil, Nat.zero_mul]
  | succ m ih =>
    rw [List.replicate_succ, List.sum_cons, ih, Nat.add_mul, Nat.one_mul]
    omega

theorem viaReplicateSum_eq (a b : ℕ) : viaReplicateSum a b = a * b := by
  rw [viaReplicateSum, sum_replicate, Nat.mul_comm]

theorem viaReplicateSum'_eq (a b : ℕ) : viaReplicateSum' a b = a * b := by
  rw [viaReplicateSum', sum_replicate]

/-! ## Against the original -/

theorem recOnSecond_eq_orig (a b : ℕ) : recOnSecond a b = orig a b := recOnSecond_eq a b

theorem recOnFirst_eq_orig (a b : ℕ) : recOnFirst a b = orig a b := recOnFirst_eq a b

theorem viaRangeOnB_eq_orig (a b : ℕ) : viaRangeOnB a b = orig a b := viaRangeOnB_eq a b

theorem viaRangeOnA_eq_orig (a b : ℕ) : viaRangeOnA a b = orig a b := viaRangeOnA_eq a b

theorem viaReplicateSum_eq_orig (a b : ℕ) : viaReplicateSum a b = orig a b :=
  viaReplicateSum_eq a b

theorem viaReplicateSum'_eq_orig (a b : ℕ) : viaReplicateSum' a b = orig a b :=
  viaReplicateSum'_eq a b

end Alt.Nat.mul
