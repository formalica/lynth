import Scripts.Test.Equiv.Nat.EquivNat

/-!
# Proofs: every route in `../EquivNat.lean` is the identity

All twenty-two routes in `../EquivNat.lean` are proved here.  Each is an
alternative route from `n : ℕ` back to `n`, so each theorem has the shape

```lean
theorem viaFoo_eq_id (n : ℕ) : viaFoo n = n
```

`../EquivNat.lean`'s header says these are "`#eval`-checked rather than proved".
They are proved now.  The `#eval` checks were not redundant: the file's three
degenerate-operand entries encode cases that differ in exactly the way this
corpus exists to record, and a `#eval` sweep is what confirms the *definitions*
compute as intended before any theorem is attempted.

## The three cases the header singles out

* `n % (n + 1) = n` but `n % n = 0` for every `n`, so `viaModSucc`'s divisor has
  to be *strictly* greater than `n`.  This is `Nat.mod_eq_of_lt`, and the proof is
  one line — the point is in the definition, not the theorem.
* `Nat.gcd n 0 = n` but `Nat.lcm n 0 = 0`, so the neutral element for `lcm` is `1`
  and for `gcd` it is `0`.  Hence `viaGcdZero` and `viaLcmOne` are asymmetric and
  neither follows from the other.
* `Nat.div n 0 = 0` while `Nat.mod n 0 = n`, the same asymmetry in the other pair.

## What the proofs actually needed

Most are a single library lemma (`Nat.and_self`, `Nat.or_zero`, `Nat.shl_zero`,
`Nat.shr_zero`, `Nat.log2_pow`, `Nat.sqrt_sq`, `Nat.min_eq_left`, `Nat.max_eq_left`).
Only three needed structure:

* `viaParity` is a real case split, so `Nat.div_add_mod` is supplied as a
  hypothesis and each branch is closed by `omega`.  `omega` cannot do the division
  itself, which is the whole reason the identity has to be handed to it.
* `viaRecSucc` needed `rec_succ_id`, because `Nat.rec` for the successor motive is
  not a `simp` lemma — `simp` unfolds the `rec` and then has nothing left.
* `viaFindEq` and `viaFindLe` needed `Nat.find_spec` and `Nat.find_min'`.  Note
  `Nat.find_min'` takes the proof `p m` as its *fourth positional* argument with
  `m` implicit, which is the opposite of the order the name suggests.

No `sorry`, no `axiom`, no `native_decide`, no `Classical`.
-/

namespace Equiv
namespace Nat

universe u

variable {n : ℕ}

/-- `n % (n + 1) = n`: the divisor is strictly greater than `n`.  Contrast `n % n`,
which is `0` for every `n` — so the divisor has to be strictly greater, which is
exactly the distinction the file's header singles out. -/
theorem viaModSucc_eq_id (n : ℕ) : viaModSucc n = n := by
  simp [viaModSucc]

/-- `0` is the neutral element for `gcd`. -/
theorem viaGcdZero_eq_id (n : ℕ) : viaGcdZero n = n := by
  simp [viaGcdZero]

/-- `Nat.gcd n n = n`. -/
theorem viaGcdSelf_eq_id (n : ℕ) : viaGcdSelf n = n := by
  simp [viaGcdSelf]

/-- `1` is the neutral element for `lcm`.  Contrast `Nat.lcm n 0 = 0`, which is
why `viaGcdZero` uses `0` and this uses `1`. -/
theorem viaLcmOne_eq_id (n : ℕ) : viaLcmOne n = n := by
  simp [viaLcmOne]

/-- `(n + 1).pred = n`: build the successor, then undo it. -/
theorem viaPredSucc_eq_id (n : ℕ) : viaPredSucc n = n := by
  simp [viaPredSucc]

/-- `(n + 1) - 1 = n`: the other route back from the successor.  Distinct from
`viaPredSucc` because `Nat.pred` is defined by cases and this is not. -/
theorem viaSuccSub_eq_id (n : ℕ) : viaSuccSub n = n := by
  simp [viaSuccSub]

/-- A case split that returns its argument. -/
theorem viaMatchSucc_eq_id (n : ℕ) : viaMatchSucc n = n := by
  cases n <;> rfl

-- `Nat.rec` for the successor motive, iterated from `0`, is the identity.  Stated
-- separately so that `viaRecSucc` needs only a definitional match.
private theorem rec_succ_id :
    ∀ n : ℕ, Nat.rec (motive := fun _ => ℕ) 0 (fun _ ih => ih + 1) n = n := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih => exact congrArg (fun k => k + 1) ih

theorem viaRecSucc_eq_id (n : ℕ) : viaRecSucc n = n := rec_succ_id n

/-- `n &&& n = n`. -/
theorem viaAndSelf_eq_id (n : ℕ) : viaAndSelf n = n := by
  simp [viaAndSelf]

/-- `n ||| 0 = n`. -/
theorem viaOrZero_eq_id (n : ℕ) : viaOrZero n = n := by
  simp [viaOrZero]

/-- `n <<< 0 = n`. -/
theorem viaShiftLeftZero_eq_id (n : ℕ) : viaShiftLeftZero n = n := by
  simp [viaShiftLeftZero]

/-- `n >>> 0 = n`. -/
theorem viaShiftRightZero_eq_id (n : ℕ) : viaShiftRightZero n = n := by
  simp [viaShiftRightZero]

/-- `log2 (2 ^ n) = n`. -/
theorem viaLog2Pow_eq_id (n : ℕ) : viaLog2Pow n = n := by
  simp [viaLog2Pow]

/-- `sqrt (n * n) = n`. -/
theorem viaSqrtSquare_eq_id (n : ℕ) : viaSqrtSquare n = n := by
  simp [viaSqrtSquare]

/-- Halve and double.  The guard is a genuine case split, so this is not a `simp`
one-liner: the two branches have to be discharged separately. -/
theorem viaParity_eq_id (n : ℕ) : viaParity n = n := by
  have hd := Nat.div_add_mod n 2
  cases h : (n % 2 == 0) with
  | true =>
    rw [viaParity, ite_eq_left h]
    have h0 : n % 2 = 0 := by simpa using h
    omega
  | false =>
    rw [viaParity, ite_eq_right (by simpa using h)]
    have hlt : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hne : n % 2 ≠ 0 := by simpa using h
    omega

/-- `Nat.find` over `m = n` reaches `n`. -/
theorem viaFindEq_eq_id (n : ℕ) : viaFindEq n = n :=
  Nat.find_spec (p := fun m => m = n) ⟨n, rfl⟩

/-- `Nat.find` over `n ≤ m` reaches `n`. -/
theorem viaFindLe_eq_id (n : ℕ) : viaFindLe n = n := by
  have hmin : Nat.find (p := fun m => n ≤ m) ⟨n, Nat.le_refl n⟩ ≤ n :=
    Nat.find_min' (p := fun m => n ≤ m) ⟨n, Nat.le_refl n⟩ (Nat.le_refl n)
  exact Nat.le_antisymm hmin (Nat.find_spec _)

/-- `Nat.findGreatest` over `m ≤ n` bounded by `n` is `n`. -/
theorem viaFindGreatest_eq_id (n : ℕ) : viaFindGreatest n = n := by
  simp [viaFindGreatest]

/-- `min n (n + 1) = n`. -/
theorem viaMinSucc_eq_id (n : ℕ) : viaMinSucc n = n := by
  simp [viaMinSucc]

/-- `max n (n - 1) = n`. -/
theorem viaMaxPred_eq_id (n : ℕ) : viaMaxPred n = n := by
  simp [viaMaxPred]

/-- `max n 0 = n`. -/
theorem viaMaxZero_eq_id (n : ℕ) : viaMaxZero n = n := by
  simp [viaMaxZero]

/-- A guard instead of arithmetic. -/
theorem viaIfZero_eq_id (n : ℕ) : viaIfZero n = n := by
  cases n <;> rfl

end Nat
end Equiv
