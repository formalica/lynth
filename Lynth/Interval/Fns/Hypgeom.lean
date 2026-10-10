import Lynth.Interval.Fns.Zeta
import Lynth.Hypergeometric
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Generalized hypergeometric `pFq` on the real line (FLINT's `pfq_direct`
general path).

For top args `a₁..aₚ`, bottom args `b₁..b_q` and `z`, with rising
products (`T_0 = 1`):

```
T_{k+1} = T_k · (Πᵢ(aᵢ+k))/(Πⱼ(bⱼ+k)) · z/(k+1),   pFq = Σ_k T_k.
```

* Terminating tops (a point nonpositive integer): exact finite prefix.
* `p ≤ q`: converges everywhere; `p = q+1`: needs `R < 1` (checked;
  fails past the disc); `p > q+1`: diverges → `⊤`.
* Fixed term count `n = 64 + 2·prec` (any `n` is sound with a valid tail
  bound; no float simulation needed); the loop sums `n+1` terms and widens
  by `|T_n|·R/(1-R)` with `R` the uniform later-ratio bound
  (`pfq_bound_factor.c`, real-line form) — the corrected
  `pfqTail_corrected_succ` (the `n`-term `R/(1-R)` form is false).
* Per term: `p+q+3` muls + 1 div (no Bernoulli, no special functions).

Analysis (recurrence, corrected tail bounds, termination) proved below,
ported back from the Mathlib-only handoff `/tmp/pfq_thm_proof.lean`.
One `HGFunL` registry entry serves all shapes: goals write multiset
`Complex.HGFun`, normalized to lists by the reifier.
-/

namespace Lynth.Interval.Fns

open BigOperators

/-! ### Real mirrors (evaluator vocabulary; byte-identical to `/tmp`) -/

/-- one series term (rising products; `T_0 = 1` definitionally). -/
noncomputable def pfqTerm (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ Finset.range p, ∏ j ∈ Finset.range k, (a i + (j : ℝ)))
    / (∏ i ∈ Finset.range q, ∏ j ∈ Finset.range k, (b i + (j : ℝ)))
    * z ^ k / (Nat.factorial k : ℝ)

/-- the real `pFq` value as a series. -/
noncomputable def pfqReal (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' k, pfqTerm p q a b z k

/-- uniform later-term-ratio bound (`R` in `|T_n|·R/(1-R)`).
For `p ≤ q` this is `Z·paired/((extra bottoms)·(n+1))`; for the
`p = q+1` case the extra top arg contributes `( |a_q|+n+1)` in place of
one `/(n+1)` (from `|a_q+k|/(k+1) ≤ (|a_q|+n+1)/(n+1)` for `k ≥ n`). -/
noncomputable def pfqRatio (p q : Nat) (a b : ℕ → ℝ) (Z : ℝ) (n : ℕ) : ℝ :=
  Z * (∏ i ∈ Finset.range (min p q), (|a i - b i| / (b i + (n : ℝ)) + 1))
    / ((∏ j ∈ Finset.Ico p q, (b j + (n : ℝ))) * ((n : ℝ) + 1))
    * (if p = q + 1 then (|a q| + (n : ℝ) + 1) else 1)

/-- term recurrence (field simp; needs bottom factors nonzero). -/
theorem pfqTerm_succ (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (k : ℕ)
    (hB : ∀ j : Nat, j < q → b j + (k : ℝ) ≠ 0) :
    pfqTerm p q a b z (k + 1) = pfqTerm p q a b z k
      * ((∏ i ∈ Finset.range p, (a i + (k : ℝ)))
        / (∏ j ∈ Finset.range q, (b j + (k : ℝ))) * z / ((k : ℝ) + 1)) := by
  simp only [pfqTerm, Finset.prod_range_succ, Finset.prod_mul_distrib, Nat.factorial_succ,
    Nat.cast_mul, pow_succ]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-! ### Tail bound (proved in `/tmp/pfq_thm_proof.lean`, ported back).

The originally stated `pfqTail` is **false**: the partial sum `∑_{k<n} T_k`
omits `T_n` itself, so the remainder is `T_n + T_{n+1} + ⋯`, bounded by
`|T_n|/(1-R)`, not `|T_n|·R/(1-R)` (counterexample `p = q = 0`, `z = 0`,
`n = 0`; see `pfqTail_false`).  The evaluator sums `n+1` terms
(`S + T_n`) and widens by `|T_n|·R/(1-R)`, which is exactly the corrected
`pfqTail_corrected_succ`. -/

lemma pfq_factor_le (x y : ℝ) (n k : ℕ) (hnk : n ≤ k) (hy : 0 < y + n) :
    |x + k| / (y + k) ≤ |x - y| / (y + n) + 1 := by
  have hk : (n:ℝ) ≤ k := by exact_mod_cast hnk
  have hyk : 0 < y + k := by linarith
  rw [div_le_iff₀ hyk]
  have h1 : |x + k| ≤ |x - y| + (y + k) := by
    calc |x + k| = |(x - y) + (y + k)| := by ring_nf
      _ ≤ |x - y| + |y + k| := abs_add_le _ _
      _ = _ := by rw [abs_of_pos hyk]
  have h2 : |x - y| ≤ |x - y| / (y + n) * (y + k) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hy]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  nlinarith

lemma pfq_ratio_le (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (n k : Nat) (hnk : n ≤ k)
    (hpq : p ≤ q + 1)
    (hBpos : ∀ j : Nat, j < q → 0 < b j + (n : ℝ)) :
    |(∏ i ∈ Finset.range p, (a i + (k : ℝ)))
        / (∏ j ∈ Finset.range q, (b j + (k : ℝ))) * z / ((k : ℝ) + 1)|
      ≤ pfqRatio p q a b |z| n := by
  have hk : (n:ℝ) ≤ k := by exact_mod_cast hnk
  have hBk : ∀ j, j < q → 0 < b j + (k:ℝ) := fun j hj => by linarith [hBpos j hj]
  have hP : ∀ m, m ≤ q →
      |∏ i ∈ Finset.range m, (a i + (k:ℝ))| / (∏ i ∈ Finset.range m, (b i + (k:ℝ)))
        ≤ ∏ i ∈ Finset.range m, (|a i - b i| / (b i + (n : ℝ)) + 1) := by
    intro m hmq
    rw [Finset.abs_prod, ← Finset.prod_div_distrib]
    apply Finset.prod_le_prod₀
    · intro i hi; exact div_nonneg (abs_nonneg _) (hBk i (by simp at hi; omega)).le
    · intro i hi; exact pfq_factor_le _ _ n k hnk (hBpos i (by simp at hi; omega))
  have hPpos : ∀ m, m ≤ q → 0 < ∏ i ∈ Finset.range m, (b i + (k:ℝ)) := fun m hm =>
    Finset.prod_pos (fun i hi => hBk i (by simp at hi; omega))
  have hPbnn : ∀ m, m ≤ q →
      0 ≤ ∏ i ∈ Finset.range m, (|a i - b i| / (b i + (n : ℝ)) + 1) := fun m hm =>
    Finset.prod_nonneg fun i hi =>
      add_nonneg (div_nonneg (abs_nonneg _) (hBpos i (by simp at hi; omega)).le) zero_le_one
  have hk1 : (0:ℝ) < k + 1 := by positivity
  have hn1 : (0:ℝ) < n + 1 := by positivity
  rcases Nat.lt_or_ge q p with hlt | hle
  · have hp : p = q + 1 := by omega
    subst hp
    have hmin : min (q+1) q = q := by omega
    simp only [pfqRatio, hmin, ite_true, Finset.Ico_eq_empty_of_le (Nat.le_succ q),
      Finset.prod_empty, one_mul, Finset.prod_range_succ]
    have hA : |a q + k| / (k + 1) ≤ (|a q| + n + 1) / (n + 1) := by
      rw [div_le_div_iff₀ hk1 hn1]
      have := abs_add_le (a q) (k:ℝ)
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ k)] at this
      nlinarith [abs_nonneg (a q)]
    have e : |(∏ i ∈ Finset.range q, (a i + (k:ℝ))) * (a q + k)
        / (∏ j ∈ Finset.range q, (b j + (k : ℝ))) * z / ((k : ℝ) + 1)|
        = |z| * (|∏ i ∈ Finset.range q, (a i + (k:ℝ))| / (∏ i ∈ Finset.range q, (b i + (k:ℝ))))
          * (|a q + k| / (k + 1)) := by
      rw [abs_div, abs_mul, abs_div, abs_mul, abs_of_pos (hPpos q le_rfl), abs_of_pos hk1]
      ring
    rw [e]
    have := hP q le_rfl
    calc _ ≤ |z| * (∏ i ∈ Finset.range q, (|a i - b i| / (b i + (n : ℝ)) + 1))
          * ((|a q| + n + 1) / (n + 1)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left this (abs_nonneg _)) hA
            (div_nonneg (abs_nonneg _) hk1.le) (mul_nonneg (abs_nonneg _) (hPbnn q le_rfl))
      _ = _ := by ring
  · have hmin : min p q = p := by omega
    simp only [pfqRatio, hmin, show p ≠ q + 1 by omega, ite_false, mul_one]
    rw [← Finset.prod_range_mul_prod_Ico _ hle]
    have hD : ∀ m : ℕ, m ≥ n → 0 < ∏ j ∈ Finset.Ico p q, (b j + (m:ℝ)) := fun m hm =>
      Finset.prod_pos (fun j hj => by
        simp at hj
        have : (n:ℝ) ≤ m := by exact_mod_cast hm
        linarith [hBpos j hj.2])
    have hDle : ∏ j ∈ Finset.Ico p q, (b j + (n:ℝ)) ≤ ∏ j ∈ Finset.Ico p q, (b j + (k:ℝ)) :=
      Finset.prod_le_prod₀ (fun j hj => by simp at hj; exact (hBpos j hj.2).le)
        (fun j hj => by linarith)
    have e : |(∏ i ∈ Finset.range p, (a i + (k:ℝ)))
        / ((∏ j ∈ Finset.range p, (b j + (k : ℝ))) * ∏ j ∈ Finset.Ico p q, (b j + (k : ℝ)))
          * z / ((k : ℝ) + 1)|
        = |z| * (|∏ i ∈ Finset.range p, (a i + (k:ℝ))| / (∏ i ∈ Finset.range p, (b i + (k:ℝ))))
          / ((∏ j ∈ Finset.Ico p q, (b j + (k : ℝ))) * (k + 1)) := by
      rw [abs_div, abs_mul, abs_div, abs_mul, abs_of_pos (hPpos p hle), abs_of_pos hk1,
        abs_of_pos (hD k hnk)]
      field_simp
    rw [e]
    apply div_le_div₀ (mul_nonneg (abs_nonneg _) (hPbnn p hle))
      (mul_le_mul_of_nonneg_left (hP p hle) (abs_nonneg _))
      (mul_pos (hD n le_rfl) hn1)
    exact mul_le_mul hDle (by linarith) hn1.le (hD k hnk).le

lemma pfq_geom_tail (T : ℕ → ℝ) (R : ℝ) (n : ℕ) (hR0 : 0 ≤ R) (hR : R < 1)
    (h : ∀ k, n ≤ k → |T (k + 1)| ≤ R * |T k|) :
    Summable T ∧ |∑' k, T k - ∑ k ∈ Finset.range n, T k| ≤ |T n| / (1 - R) := by
  have hb : ∀ j, |T (j + n)| ≤ |T n| * R ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc |T (j + 1 + n)| = |T ((j + n) + 1)| := by rw [Nat.add_right_comm]
        _ ≤ R * |T (j + n)| := h _ (by omega)
        _ ≤ R * (|T n| * R ^ j) := mul_le_mul_of_nonneg_left ih hR0
        _ = |T n| * R ^ (j + 1) := by ring
  have hg : Summable (fun j => |T n| * R ^ j) :=
    (summable_geometric_of_lt_one hR0 hR).mul_left _
  have hsn : Summable (fun j => |T (j + n)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) hb hg
  have hs' : Summable (fun j => T (j + n)) := hsn.of_abs
  have hs : Summable T := (summable_nat_add_iff n).mp hs'
  refine ⟨hs, ?_⟩
  rw [← hs.sum_add_tsum_nat_add n, add_sub_cancel_left]
  calc |∑' j, T (j + n)| ≤ ∑' j, |T (j + n)| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun j => T (j + n)) hsn
    _ ≤ ∑' j, |T n| * R ^ j := hsn.tsum_le_tsum hb hg
    _ = |T n| / (1 - R) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hR0 hR, div_eq_mul_inv]

/-- One-step ratio bound for the actual terms, for all `k ≥ n`. -/
lemma pfqTerm_ratio_step (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (n : Nat)
    (hpq : p ≤ q + 1)
    (hBpos : ∀ j : Nat, j < q → 0 < b j + (n : ℝ)) :
    ∀ k, n ≤ k → |pfqTerm p q a b z (k + 1)| ≤ pfqRatio p q a b |z| n * |pfqTerm p q a b z k| := by
  intro k hk
  have hkr : (n:ℝ) ≤ k := by exact_mod_cast hk
  rw [pfqTerm_succ p q a b z k (fun j hj => by linarith [hBpos j hj]), abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (pfq_ratio_le p q a b z n k hk hpq hBpos) (abs_nonneg _)

lemma pfqRatio_nonneg (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (n : Nat)
    (hpq : p ≤ q + 1)
    (hBpos : ∀ j : Nat, j < q → 0 < b j + (n : ℝ)) :
    0 ≤ pfqRatio p q a b |z| n :=
  (abs_nonneg _).trans (pfq_ratio_le p q a b z n n le_rfl hpq hBpos)

/-- Under the dispatcher's conditions the series defining `pfqReal` converges. -/
theorem pfqTail_summable (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (n : Nat)
    (hpq : p ≤ q + 1)
    (hBpos : ∀ j : Nat, j < q → 0 < b j + (n : ℝ))
    (hR : pfqRatio p q a b |z| n < 1) :
    Summable (fun k => pfqTerm p q a b z k) :=
  (pfq_geom_tail _ _ n (pfqRatio_nonneg p q a b z n hpq hBpos) hR
    (pfqTerm_ratio_step p q a b z n hpq hBpos)).1

/-- The original `pfqTail` statement is false (counterexample `p = q = 0`, `z = 0`, `n = 0`). -/
theorem pfqTail_false : ¬ (∀ (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (n : Nat)
    (_hpq : p ≤ q + 1)
    (_hBpos : ∀ j : Nat, j < q → 0 < b j + (n : ℝ))
    (_hBne : ∀ j : Nat, j < q → ∀ k : Nat, k < n → b j + (k : ℝ) ≠ 0)
    (_hR : pfqRatio p q a b |z| n < 1),
    |pfqReal p q a b z - (Finset.range n).sum (fun k => pfqTerm p q a b z k)|
      ≤ |pfqTerm p q a b z n|
        * (pfqRatio p q a b |z| n / (1 - pfqRatio p q a b |z| n))) := by
  intro h
  have hr : pfqRatio 0 0 0 0 |(0:ℝ)| 0 = 0 := by simp [pfqRatio]
  have e : pfqReal 0 0 0 0 0 = 1 := by
    unfold pfqReal
    rw [tsum_eq_single 0]
    · simp [pfqTerm]
    · intro k hk; simp [pfqTerm, zero_pow hk]
  have := h 0 0 0 0 0 0 (by norm_num) (by simp) (by simp) (by rw [hr]; norm_num)
  rw [hr, e] at this
  norm_num at this

/-- CORRECTED tail bound: `|pFq − Σ_{k<n} T_k| ≤ |T_n| · (1/(1-R))`. -/
theorem pfqTail_corrected (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (n : Nat)
    (hpq : p ≤ q + 1)
    (hBpos : ∀ j : Nat, j < q → 0 < b j + (n : ℝ))
    (hR : pfqRatio p q a b |z| n < 1) :
    |pfqReal p q a b z - (Finset.range n).sum (fun k => pfqTerm p q a b z k)|
      ≤ |pfqTerm p q a b z n| * (1 / (1 - pfqRatio p q a b |z| n)) := by
  rw [mul_one_div]
  exact (pfq_geom_tail _ _ n (pfqRatio_nonneg p q a b z n hpq hBpos) hR
    (pfqTerm_ratio_step p q a b z n hpq hBpos)).2

/-- CORRECTED tail bound, original right-hand side: once `T_n` is included in the partial
sum, `|pFq − Σ_{k<n+1} T_k| ≤ |T_n| · (R/(1-R))`. This is what the evaluator
uses (`S + T_n` plus `|T_n|`-widening). -/
theorem pfqTail_corrected_succ (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (n : Nat)
    (hpq : p ≤ q + 1)
    (hBpos : ∀ j : Nat, j < q → 0 < b j + (n : ℝ))
    (hR : pfqRatio p q a b |z| n < 1) :
    |pfqReal p q a b z - (Finset.range (n + 1)).sum (fun k => pfqTerm p q a b z k)|
      ≤ |pfqTerm p q a b z n|
        * (pfqRatio p q a b |z| n / (1 - pfqRatio p q a b |z| n)) := by
  set R := pfqRatio p q a b |z| n with hRdef
  have hR0 : 0 ≤ R := pfqRatio_nonneg p q a b z n hpq hBpos
  have hstep := pfqTerm_ratio_step p q a b z n hpq hBpos
  have h := (pfq_geom_tail (fun k => pfqTerm p q a b z k) R (n + 1) hR0 hR
    (fun k hk => hstep k (by omega))).2
  have h1 : 0 < 1 - R := by linarith
  calc _ ≤ |pfqTerm p q a b z (n + 1)| / (1 - R) := h
    _ ≤ (R * |pfqTerm p q a b z n|) / (1 - R) :=
        div_le_div_of_nonneg_right (hstep n le_rfl) h1.le
    _ = _ := by ring

/-- terminating tops (`a i₀ = -m`) kill all terms past `m`,
so the series is the exact prefix (no bottom hypotheses needed:
`0/0 = 0` in Lean fields keeps vanishing unconditional). -/
theorem pfqTerm_exact (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (m : Nat)
    (i₀ : Nat) (hi₀ : i₀ < p) (hterm : a i₀ = -(m : ℝ)) :
    pfqReal p q a b z = (Finset.range (m + 1)).sum (fun k => pfqTerm p q a b z k) := by
  unfold pfqReal
  apply tsum_eq_sum
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  have h0 : ∏ i ∈ Finset.range p, ∏ j ∈ Finset.range k, (a i + (j : ℝ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.2 hi₀)
    apply Finset.prod_eq_zero (i := m) (Finset.mem_range.2 (by omega))
    rw [hterm]; ring
  simp [pfqTerm, h0]

/-! ### Local bridges -/

/-- list product over a mapped range is the finset product. -/
theorem list_prod_map_range (f : Nat → ℝ) : ∀ N : Nat,
    ((List.range N).map f).prod = (Finset.range N).prod fun k => f k
  | 0 => by simp
  | N + 1 => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one,
      Finset.prod_range_succ]
    rw [list_prod_map_range f N]

/-- `T_0 = 1` (empty products, `z^0`, `0!`). -/
theorem pfqTerm_zero (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) :
    pfqTerm p q a b z 0 = 1 := by
  simp [pfqTerm]

/-- one recurrence step as interval arithmetic. -/
def pfqStepIval (c : Ctx) (A B : List Ival) (p q : Nat) (Z : Ival) (k : Nat)
    (T : Ival) : Ival :=
  let num := iprod c ((List.range p).map fun i =>
    Ival.add c.prec (A.getD i Ival.top) (Ival.ofRat c.prec ((k : Nat) : ℚ)))
  let den := iprod c ((List.range q).map fun j =>
    Ival.add c.prec (B.getD j Ival.top) (Ival.ofRat c.prec ((k : Nat) : ℚ)))
  Ival.div c.prec (Ival.mul c.prec (Ival.mul c.prec T num) Z)
    (Ival.mul c.prec den (Ival.ofRat c.prec ((k + 1 : Nat) : ℚ)))

/-- paired rising factor `|aᵢ-bᵢ|/Dᵢ + 1` as interval arithmetic. -/
def pfqPairIval (c : Ctx) (Ai Bi Di : Ival) : Ival :=
  Ival.add c.prec
    (Ival.div c.prec (Ival.abs (Ival.sub c.prec Ai Bi)) Di)
    (Ival.ofRat c.prec 1)

/-- fuel loop: `(sum of terms k..k+f-1, T_{k+f})`, structural on fuel. -/
def pfqLoop (c : Ctx) (A B : List Ival) (p q : Nat) (Z : Ival) :
    Nat → Nat → Ival → Ival → Ival × Ival
  | 0, _, S, T => (S, T)
  | f + 1, k, S, T =>
    pfqLoop c A B p q Z f (k + 1) (Ival.add c.prec S T)
      (pfqStepIval c A B p q Z k T)

/-- bottom guards: shifted bottoms positive + no pole integer in range. -/
def pfqGuard (B : List Ival) (n : Nat) : Bool :=
  B.all fun J => match J.lo, J.hi with
    | some lo, some hi =>
      decide ((n : ℚ) + lo.toRat > 0
        ∧ ¬ (⌈lo.toRat⌉ ≤ ⌊hi.toRat⌋ ∧ ⌈lo.toRat⌉ ≤ 0 ∧ -((n - 1 : Nat) : ℤ) ≤ ⌊hi.toRat⌋))
    | _, _ => false

/-- range-mapped shift-factor memberships (induction on fuel). -/
theorem pfqAddForall₂ (c : Ctx) (L : List Ival) (v : ℕ → ℝ) (k : Nat)
    (hm : ∀ i : Nat, i < L.length → v i ∈ L.getD i Ival.top) :
    ∀ m : Nat, m ≤ L.length → List.Forall₂ (fun x I => x ∈ I)
      ((List.range m).map fun (i : Nat) => v i + (k : ℝ))
      ((List.range m).map fun (i : Nat) =>
        Ival.add c.prec (L.getD i Ival.top) (Ival.ofRat c.prec ((k : Nat) : ℚ))) := by
  intro m
  induction m with
  | zero => intro _; exact List.Forall₂.nil
  | succ m ih =>
    intro hmle
    rw [List.range_succ, List.map_append, List.map_append]
    refine List.rel_append (ih (by omega)) ?_
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    have hvm := hm m (by omega)
    have hkR : ((k : Nat) : ℝ) ∈ Ival.ofRat c.prec ((k : Nat) : ℚ) := by
      exact_mod_cast Ival.mem_ofRat c.prec ((k : Nat) : ℚ)
    exact Ival.mem_add hvm hkR

/-- one recurrence step as interval arithmetic (sound). -/
theorem mem_pfqStep (c : Ctx) (hc : c.Valid)
    (a b : ℕ → ℝ) (A B : List Ival) (Z : Ival) (z : ℝ) (k : Nat)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i Ival.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i Ival.top)
    (hmZ : z ∈ Z) (T : Ival) (Tk : ℝ) (hT : Tk ∈ T) :
    Tk * ((∏ i ∈ Finset.range A.length, (a i + (k : ℝ)))
      / (∏ j ∈ Finset.range B.length, (b j + (k : ℝ))) * z / ((k : ℝ) + 1))
      ∈ pfqStepIval c A B A.length B.length Z k T := by
  have hnum := mem_iprod c hc _ _ (pfqAddForall₂ c A a k hmA A.length le_rfl)
  rw [list_prod_map_range] at hnum
  have hden := mem_iprod c hc _ _ (pfqAddForall₂ c B b k hmB B.length le_rfl)
  rw [list_prod_map_range] at hden
  have hk1R : ((k + 1 : Nat) : ℝ) ∈ Ival.ofRat c.prec ((k + 1 : Nat) : ℚ) := by
    exact_mod_cast Ival.mem_ofRat c.prec ((k + 1 : Nat) : ℚ)
  have hval : Tk * ((∏ i ∈ Finset.range A.length, (a i + (k : ℝ)))
      / (∏ j ∈ Finset.range B.length, (b j + (k : ℝ))) * z / ((k : ℝ) + 1))
      = ((Tk * (Finset.range A.length).prod (fun i => a i + (k : ℝ))) * z)
        / ((Finset.range B.length).prod (fun j => b j + (k : ℝ))
          * ((k + 1 : Nat) : ℝ)) := by
    have e : (((k + 1 : Nat)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [e]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hval]
  simp only [pfqStepIval]
  exact Ival.mem_div (Ival.mem_mul (Ival.mem_mul hT hnum) hmZ)
    (Ival.mem_mul hden hk1R)

/-- joint loop invariant: prefix sum + current term memberships. -/
theorem mem_pfqLoop (c : Ctx) (hc : c.Valid)
    (a b : ℕ → ℝ) (A B : List Ival) (Z : Ival) (z : ℝ) (n : Nat)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i Ival.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i Ival.top)
    (hmZ : z ∈ Z)
    (hBne : ∀ j : Nat, j < B.length → ∀ k : Nat, k < n → b j + (k : ℝ) ≠ 0) :
    ∀ (f k : Nat), k + f ≤ n → ∀ (S T : Ival) (Sr Tr : ℝ),
    Sr ∈ S → Tr ∈ T →
    Sr = (Finset.range k).sum (fun j => pfqTerm A.length B.length a b z j) →
    Tr = pfqTerm A.length B.length a b z k →
    ((Finset.range (k + f)).sum (fun j => pfqTerm A.length B.length a b z j)
      ∈ (pfqLoop c A B A.length B.length Z f k S T).1
    ∧ pfqTerm A.length B.length a b z (k + f)
      ∈ (pfqLoop c A B A.length B.length Z f k S T).2) := by
  intro f
  induction f with
  | zero =>
    intro k hkn S T Sr Tr hS hT hSeq hTeq
    simp only [pfqLoop, Nat.add_zero]
    constructor
    · rw [← hSeq]; exact hS
    · rw [← hTeq]; exact hT
  | succ f ih =>
    intro k hkn S T Sr Tr hS hT hSeq hTeq
    show ((Finset.range (k + (f + 1))).sum _
        ∈ (pfqLoop c A B A.length B.length Z f (k + 1)
          (Ival.add c.prec S T)
          (pfqStepIval c A B A.length B.length Z k T)).1
      ∧ pfqTerm A.length B.length a b z (k + (f + 1))
        ∈ (pfqLoop c A B A.length B.length Z f (k + 1)
          (Ival.add c.prec S T)
          (pfqStepIval c A B A.length B.length Z k T)).2)
    have hST : Sr + Tr ∈ Ival.add c.prec S T := Ival.mem_add hS hT
    have hTk1 : Tr
        * ((∏ i ∈ Finset.range A.length, (a i + (k : ℝ)))
          / (∏ j ∈ Finset.range B.length, (b j + (k : ℝ))) * z / ((k : ℝ) + 1))
        ∈ pfqStepIval c A B A.length B.length Z k T :=
      mem_pfqStep c hc a b A B Z z k hmA hmB hmZ T Tr hT
    have hTeq1 : Tr
        * ((∏ i ∈ Finset.range A.length, (a i + (k : ℝ)))
          / (∏ j ∈ Finset.range B.length, (b j + (k : ℝ))) * z / ((k : ℝ) + 1))
        = pfqTerm A.length B.length a b z (k + 1) := by
      rw [hTeq]
      exact (pfqTerm_succ A.length B.length a b z k
        (fun j hj => hBne j hj k (by omega))).symm
    rw [hTeq1] at hTk1
    have hSeq1 : Sr + Tr
        = (Finset.range (k + 1)).sum (fun j => pfqTerm A.length B.length a b z j) := by
      rw [Finset.sum_range_succ, hSeq, hTeq]
    have e1 : k + (f + 1) = k + 1 + f := by omega
    rw [e1]
    exact ih (k + 1) (by omega) _ _ _ _ hST hTk1 hSeq1 rfl

/-- terminating-top search: first `(index, m)` with point value `-m`
(any terminating top makes the series exact; first match keeps it fast). -/
def pfqFindTerm : List Ival → Nat → Option (Nat × Nat)
  | [], _ => none
  | I :: Is, i =>
    match I.lo, I.hi with
    | some lo, some hi =>
      if lo = hi then
        let q := lo.toRat
        if q.den = 1 ∧ q.num ≤ 0 then some (i, (-q.num).toNat)
        else pfqFindTerm Is (i + 1)
      else pfqFindTerm Is (i + 1)
    | _, _ => pfqFindTerm Is (i + 1)

/-- a point enclosure pins the real value (dyadic cast). -/
theorem dyPointMem {D : Dy} {X : Ival} {x : ℝ} (hx : x ∈ X)
    (hlo : X.lo = some D) (hhi : X.hi = some D) :
    x = ((D.toRat : ℚ) : ℝ) := by
  rw [Ival.mem_def] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have e1 := hx1 D hlo
  have e2 := hx2 D hhi
  rw [Dy.toReal_def] at e1 e2
  exact le_antisymm e2 e1

/-- search result is a genuine terminating top. -/
theorem pfqFindTerm_ok (a : ℕ → ℝ) :
    ∀ (As : List Ival) (o : Nat),
    (∀ i : Nat, i < As.length → a (o + i) ∈ As.getD i Ival.top) →
    ∀ (r : Option (Nat × Nat)), pfqFindTerm As o = r →
    ∀ (i₀ m : Nat), r = some (i₀, m) → i₀ < o + As.length ∧ a i₀ = -(m : ℝ) := by
  intro As
  induction As with
  | nil =>
    intro o _ r hr i₀ m hrm
    simp only [pfqFindTerm] at hr
    rw [hrm] at hr
    exact absurd hr (by simp)
  | cons I Is ih =>
    intro o hm r hr i₀ m hrm
    cases hlo : I.lo with
    | none =>
      have hstep : pfqFindTerm (I :: Is) o = pfqFindTerm Is (o + 1) := by
        simp [pfqFindTerm, hlo]
      rw [hstep] at hr
      have hm' : ∀ i : Nat, i < Is.length → a ((o + 1) + i) ∈ Is.getD i Ival.top := by
        intro i hi
        have h2 : i + 1 < (I :: Is).length := by
          simp only [List.length_cons] at hi ⊢
          omega
        have h3 := hm (i + 1) h2
        have e : o + (i + 1) = (o + 1) + i := by omega
        rw [e] at h3
        simpa using h3
      have hih := ih (o + 1) hm' r hr i₀ m hrm
      have hlen : (I :: Is).length = Is.length + 1 := rfl
      obtain ⟨hlt, hval⟩ := hih
      exact ⟨by omega, hval⟩
    | some lo =>
      cases hhi : I.hi with
      | none =>
        have hstep : pfqFindTerm (I :: Is) o = pfqFindTerm Is (o + 1) := by
          simp [pfqFindTerm, hlo, hhi]
        rw [hstep] at hr
        have hm' : ∀ i : Nat, i < Is.length → a ((o + 1) + i) ∈ Is.getD i Ival.top := by
          intro i hi
          have h2 : i + 1 < (I :: Is).length := by
            simp only [List.length_cons] at hi ⊢
            omega
          have h3 := hm (i + 1) h2
          have e : o + (i + 1) = (o + 1) + i := by omega
          rw [e] at h3
          simpa using h3
        have hih := ih (o + 1) hm' r hr i₀ m hrm
        have hlen : (I :: Is).length = Is.length + 1 := rfl
        obtain ⟨hlt, hval⟩ := hih
        exact ⟨by omega, hval⟩
      | some hi =>
        by_cases hpt : lo = hi
        · have hstep : pfqFindTerm (I :: Is) o =
              (let q := lo.toRat
              if q.den = 1 ∧ q.num ≤ 0 then some (o, (-q.num).toNat)
              else pfqFindTerm Is (o + 1)) := by
            simp [pfqFindTerm, hlo, hhi, hpt]
          rw [hstep] at hr
          by_cases hnat : lo.toRat.den = 1 ∧ lo.toRat.num ≤ 0
          · simp only [hnat, and_self, ite_true] at hr
            have hr' : some (o, (-lo.toRat.num).toNat) = r := hr
            rw [hrm] at hr'
            have hpair : o = i₀ ∧ (-lo.toRat.num).toNat = m := by
              simpa using hr'
            obtain ⟨e1, e2⟩ := hpair
            rw [← e1, ← e2]
            have hmem : a (o + 0) ∈ (I :: Is).getD 0 Ival.top := hm 0 (by simp)
            simp only [Nat.add_zero] at hmem
            have hptI : (I :: Is).getD 0 Ival.top = I := rfl
            rw [hptI] at hmem
            have hhi' : I.hi = some lo := by rw [← hpt] at hhi; exact hhi
            refine ⟨?_, ?_⟩
            · have hlen : (I :: Is).length = Is.length + 1 := rfl
              omega
            · have hmem2 := dyPointMem (X := I) hmem hlo hhi'
              have hq : lo.toRat = ((lo.toRat.num : ℤ) : ℚ) := by
                have h := lo.toRat.num_div_den
                rw [hnat.1] at h
                rw [← h]
                simp
              rw [hmem2, hq]
              have hzz : (lo.toRat.num : ℤ)
                  = -(((-lo.toRat.num).toNat : Nat) : ℤ) := by
                have htn : (((-lo.toRat.num).toNat : Nat) : ℤ) = -lo.toRat.num :=
                  Int.toNat_of_nonneg (by omega : 0 ≤ -lo.toRat.num)
                omega
              exact_mod_cast hzz
          · simp only [hnat, ite_false] at hr
            have hm' : ∀ i : Nat, i < Is.length → a ((o + 1) + i) ∈ Is.getD i Ival.top := by
              intro i hi
              have h2 : i + 1 < (I :: Is).length := by
                simp only [List.length_cons] at hi ⊢
                omega
              have h3 := hm (i + 1) h2
              have e : o + (i + 1) = (o + 1) + i := by omega
              rw [e] at h3
              simpa using h3
            have hih := ih (o + 1) hm' r hr i₀ m hrm
            have hlen : (I :: Is).length = Is.length + 1 := rfl
            obtain ⟨hlt, hval⟩ := hih
            exact ⟨by omega, hval⟩
        · have hstep : pfqFindTerm (I :: Is) o = pfqFindTerm Is (o + 1) := by
            simp [pfqFindTerm, hlo, hhi, hpt]
          rw [hstep] at hr
          have hm' : ∀ i : Nat, i < Is.length → a ((o + 1) + i) ∈ Is.getD i Ival.top := by
            intro i hi
            have h2 : i + 1 < (I :: Is).length := by
              simp only [List.length_cons] at hi ⊢
              omega
            have h3 := hm (i + 1) h2
            have e : o + (i + 1) = (o + 1) + i := by omega
            rw [e] at h3
            simpa using h3
          have hih := ih (o + 1) hm' r hr i₀ m hrm
          have hlen : (I :: Is).length = Is.length + 1 := rfl
          obtain ⟨hlt, hval⟩ := hih
          exact ⟨by omega, hval⟩

/-- `R` numerator: paired factors over `i < min p q`. -/
def pfqRNumIval (c : Ctx) (A B : List Ival) (p q n : Nat) : Ival :=
  iprod c ((List.range (min p q)).map fun i =>
    pfqPairIval c (A.getD i Ival.top) (B.getD i Ival.top)
      (Ival.add c.prec (B.getD i Ival.top) (Ival.ofRat c.prec ((n : Nat) : ℚ))))

/-- `R` denominator extras over `j ∈ [p, q)`, fuel-indexed. -/
def pfqRDenAux (c : Ctx) (B : List Ival) (n : Nat) : Nat → Nat → List Ival
  | _, 0 => []
  | p, f + 1 => pfqRDenAux c B n p f
    ++ [Ival.add c.prec (B.getD (p + f) Ival.top)
      (Ival.ofRat c.prec ((n : Nat) : ℚ))]

/-- full `R` interval (mirrors `pfqRatio`, same `if`). -/
def pfqRIval (c : Ctx) (A B : List Ival) (p q : Nat) (Zabs : Ival)
    (aq : Ival) (n : Nat) : Ival :=
  let base := Ival.div c.prec
    (Ival.mul c.prec Zabs (pfqRNumIval c A B p q n))
    (Ival.mul c.prec
      (iprod c (pfqRDenAux c B n p (q - p)))
      (Ival.ofRat c.prec (((n : Nat) : ℚ) + 1)))
  if p = q + 1 then
    Ival.mul c.prec base
      (Ival.add c.prec aq (Ival.ofRat c.prec (((n : Nat) : ℚ) + 1)))
  else base

/-- tail scale `C = R/(1-R)` interval, `⊤` unless `R < 1`. -/
def pfqTailC (c : Ctx) (R : Ival) : Ival :=
  match R.hi with
  | some h => if h.toRat < 1 then
      Ival.div c.prec R (Ival.sub c.prec (Ival.ofRat c.prec 1) R)
    else Ival.top
  | none => Ival.top

/-- closed-form term `T_k` as interval arithmetic. -/
def pfqTermIval (c : Ctx) (A B : List Ival) (p q : Nat) (Z : Ival) (k : Nat) : Ival :=
  Ival.div c.prec
    (Ival.div c.prec
      (Ival.mul c.prec
        (iprod c ((List.range p).map fun i => risingZ c (A.getD i Ival.top) k))
        (Ival.npow c.prec Z k))
      (iprod c ((List.range q).map fun j => risingZ c (B.getD j Ival.top) k)))
    (Ival.ofRat c.prec (Nat.factorial k : ℚ))

/-- closed-form term membership. -/
theorem mem_pfqTermIval (c : Ctx) (hc : c.Valid)
    (a b : ℕ → ℝ) (A B : List Ival) (p q : Nat) (Z : Ival) (z : ℝ) (k : Nat)
    (hlenA : A.length = p) (hlenB : B.length = q)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i Ival.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i Ival.top)
    (hmZ : z ∈ Z) :
    pfqTerm p q a b z k ∈ pfqTermIval c A B p q Z k := by
  have hfaN : ∀ m : Nat, m ≤ p → List.Forall₂ (fun x I => x ∈ I)
      ((List.range m).map fun i => emRising (a i) k)
      ((List.range m).map fun i => risingZ c (A.getD i Ival.top) k) := by
    intro m
    induction m with
    | zero => intro _; exact List.Forall₂.nil
    | succ m ih =>
      intro hmle
      rw [List.range_succ, List.map_append, List.map_append]
      refine List.rel_append (ih (by omega)) ?_
      refine List.Forall₂.cons ?_ List.Forall₂.nil
      have hmem : a m ∈ A.getD m Ival.top := hmA m (by omega)
      exact mem_risingZ c hc _ _ hmem k
  have hfaD : ∀ m : Nat, m ≤ q → List.Forall₂ (fun x I => x ∈ I)
      ((List.range m).map fun j => emRising (b j) k)
      ((List.range m).map fun j => risingZ c (B.getD j Ival.top) k) := by
    intro m
    induction m with
    | zero => intro _; exact List.Forall₂.nil
    | succ m ih =>
      intro hmle
      rw [List.range_succ, List.map_append, List.map_append]
      refine List.rel_append (ih (by omega)) ?_
      refine List.Forall₂.cons ?_ List.Forall₂.nil
      have hmem : b m ∈ B.getD m Ival.top := hmB m (by omega)
      exact mem_risingZ c hc _ _ hmem k
  have hnum := mem_iprod c hc _ _ (hfaN p le_rfl)
  rw [list_prod_map_range] at hnum
  have hden := mem_iprod c hc _ _ (hfaD q le_rfl)
  rw [list_prod_map_range] at hden
  have hpow : z ^ k ∈ Ival.npow c.prec Z k := Ival.mem_npow hmZ k
  have hfact : (((Nat.factorial k : Nat) : ℚ) : ℝ)
      ∈ Ival.ofRat c.prec (Nat.factorial k : ℚ) := Ival.mem_ofRat _ _
  have hval : pfqTerm p q a b z k
      = (((Finset.range p).prod (fun i => emRising (a i) k) * z ^ k
        / (Finset.range q).prod (fun j => emRising (b j) k))
        / (((Nat.factorial k : Nat) : ℚ) : ℝ)) := by
    simp only [pfqTerm, emRising, list_prod_map_range]
    push_cast
    ring
  rw [hval]
  simp only [pfqTermIval]
  exact Ival.mem_div
    (Ival.mem_div (Ival.mem_mul hnum hpow) hden) hfact

/-- finite-prefix enclosure (terminating path). -/
def pfqFiniteIval (c : Ctx) (A B : List Ival) (p q : Nat) (Z : Ival)
    (m : Nat) : Ival :=
  isum c ((List.range (m + 1)).map fun k => pfqTermIval c A B p q Z k)

/-- finite-prefix soundness (exact identity, no tail). -/
theorem pfqFinite_sound (c : Ctx) (hc : c.Valid)
    (p q : Nat) (a b : ℕ → ℝ) (A B : List Ival) (Z : Ival) (z : ℝ)
    (m : Nat) (i₀ : Nat)
    (hlenA : A.length = p) (hlenB : B.length = q)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i Ival.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i Ival.top)
    (hmZ : z ∈ Z)
    (hi₀ : i₀ < p) (hterm : a i₀ = -(m : ℝ)) :
    pfqReal p q a b z ∈ pfqFiniteIval c A B p q Z m := by
  have hfa : ∀ t : Nat, t ≤ m + 1 → List.Forall₂ (fun x I => x ∈ I)
      ((List.range t).map fun k => pfqTerm p q a b z k)
      ((List.range t).map fun k => pfqTermIval c A B p q Z k) := by
    intro t
    induction t with
    | zero => intro _; exact List.Forall₂.nil
    | succ t ih =>
      intro htle
      rw [List.range_succ, List.map_append, List.map_append]
      refine List.rel_append (ih (by omega)) ?_
      refine List.Forall₂.cons ?_ List.Forall₂.nil
      exact mem_pfqTermIval c hc a b A B p q Z z t hlenA hlenB hmA hmB hmZ
  have hmem := mem_isum c hc _ _ (hfa (m + 1) le_rfl)
  rw [list_sum_map_range] at hmem
  rw [pfqTerm_exact p q a b z m i₀ hi₀ hterm]
  exact hmem

/-- guard element correctness (real bounds + pole avoidance). -/
theorem pfqGuardElem_ok (J : Ival) (n : Nat) (lo hi : Dy)
    (hlo : J.lo = some lo) (hhi : J.hi = some hi)
    (hg : (n : ℚ) + lo.toRat > 0
      ∧ ¬ (⌈lo.toRat⌉ ≤ ⌊hi.toRat⌋ ∧ ⌈lo.toRat⌉ ≤ 0 ∧ -((n - 1 : Nat) : ℤ) ≤ ⌊hi.toRat⌋))
    (bj : ℝ) (hloR : ((lo.toRat : ℚ) : ℝ) ≤ bj) (hhiR : bj ≤ ((hi.toRat : ℚ) : ℝ)) :
    (0 < (n : ℝ) + bj) ∧ (∀ k : Nat, k < n → bj + (k : ℝ) ≠ 0) := by
  obtain ⟨hpos, hnp⟩ := hg
  have hposR : (0 : ℝ) < (n : ℝ) + ((lo.toRat : ℚ) : ℝ) := by exact_mod_cast hpos
  constructor
  · linarith
  · intro k hk hzero
    have hbk : bj = -((k : Nat) : ℝ) := by linarith
    have e : ((-(k : ℤ) : ℚ) : ℝ) = (-((k : Nat)) : ℝ) := by push_cast; ring
    have e1 : lo.toRat ≤ (-(k : ℤ) : ℚ) := by
      have h' : ((lo.toRat : ℚ) : ℝ) ≤ ((-(k : ℤ) : ℚ) : ℝ) := by
        rw [e, ← hbk]
        exact hloR
      exact_mod_cast h'
    have e2 : (-(k : ℤ) : ℚ) ≤ hi.toRat := by
      have h' : ((-(k : ℤ) : ℚ) : ℝ) ≤ ((hi.toRat : ℚ) : ℝ) := by
        rw [e, ← hbk]
        exact hhiR
      exact_mod_cast h'
    have c1 : ⌈lo.toRat⌉ ≤ -(k : ℤ) := Int.ceil_le.mpr e1
    have c2 : -(k : ℤ) ≤ ⌊hi.toRat⌋ := Int.le_floor.mpr e2
    have hle : -((n - 1 : Nat) : ℤ) ≤ -(k : ℤ) := by omega
    exact hnp ⟨le_trans c1 c2, le_trans c1 (by omega), le_trans hle c2⟩

/-- guard correctness over a list (offset induction). -/
theorem pfqGuard_ok (b : ℕ → ℝ) :
    ∀ (Bs : List Ival) (o n : Nat),
    (∀ i : Nat, i < Bs.length → b (o + i) ∈ Bs.getD i Ival.top) →
    pfqGuard Bs n = true →
    (∀ j : Nat, j < Bs.length → 0 < (n : ℝ) + b (o + j))
    ∧ (∀ j : Nat, j < Bs.length → ∀ k : Nat, k < n → b (o + j) + (k : ℝ) ≠ 0) := by
  intro Bs
  induction Bs with
  | nil =>
    intro o n _ _
    constructor <;> (intro j hj; simp at hj)
  | cons J Js ih =>
    intro o n hm hg
    simp only [pfqGuard, List.all_cons] at hg
    rw [Bool.and_eq_true] at hg
    obtain ⟨hJ, hJs⟩ := hg
    -- head element bounds
    cases hlo : J.lo with
    | none => simp [hlo] at hJ
    | some lo =>
      cases hhi : J.hi with
      | none => simp [hlo, hhi] at hJ
      | some hi =>
        simp only [hlo, hhi, decide_eq_true_eq] at hJ
        have hmem : b (o + 0) ∈ (J :: Js).getD 0 Ival.top := hm 0 (by simp)
        simp only [Nat.add_zero] at hmem
        have hhead : b o ∈ J := by simpa using hmem
        rw [Ival.mem_def] at hhead
        obtain ⟨hlo', hhi'⟩ := hhead
        have hloR : ((lo.toRat : ℚ) : ℝ) ≤ b o := hlo' lo hlo
        have hhiR : b o ≤ ((hi.toRat : ℚ) : ℝ) := hhi' hi hhi
        have hElem := pfqGuardElem_ok J n lo hi hlo hhi hJ (b o) hloR hhiR
        have hm' : ∀ i : Nat, i < Js.length → b ((o + 1) + i) ∈ Js.getD i Ival.top := by
          intro i hi
          have h2 : i + 1 < (J :: Js).length := by
            simp only [List.length_cons] at hi ⊢
            omega
          have h3 := hm (i + 1) h2
          have e : o + (i + 1) = (o + 1) + i := by omega
          rw [e] at h3
          simpa using h3
        have hrec := ih (o + 1) n hm' hJs
        obtain ⟨hr1, hr2⟩ := hrec
        have hlen : (J :: Js).length = Js.length + 1 := rfl
        constructor
        · intro j hj
          cases j with
          | zero => simpa using hElem.1
          | succ j =>
            have e : o + (j + 1) = (o + 1) + j := by omega
            rw [e]
            exact hr1 j (by omega)
        · intro j hj k hk
          cases j with
          | zero => simpa using hElem.2 k hk
          | succ j =>
            have e : o + (j + 1) = (o + 1) + j := by omega
            rw [e]
            exact hr2 j (by omega) k hk

/-- extras real equation (fuel induction to `Ico`). -/
theorem pfqRDenAux_eq (b : ℕ → ℝ) (p f n : Nat) :
    ((List.range f).map fun t => b (p + t) + (n : ℝ)).prod
      = ∏ j ∈ Finset.Ico p (p + f), (b j + (n : ℝ)) := by
  induction f with
  | zero => simp
  | succ f ih =>
    sorry

/-- extras interval membership (fuel induction). -/
theorem pfqRDenForall₂ (c : Ctx) (B : List Ival) (b : ℕ → ℝ) (n p : Nat)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i Ival.top) :
    ∀ f : Nat, p + f ≤ B.length → List.Forall₂ (fun x I => x ∈ I)
      ((List.range f).map fun t => b (p + t) + (n : ℝ))
      (pfqRDenAux c B n p f) := by
  intro f
  induction f with
  | zero => intro _; exact List.Forall₂.nil
  | succ f ih =>
    intro hle
    rw [List.range_succ, List.map_append]
    show List.Forall₂ (fun x I => x ∈ I) _
      (pfqRDenAux c B n p f
        ++ [Ival.add c.prec (B.getD (p + f) Ival.top)
          (Ival.ofRat c.prec ((n : Nat) : ℚ))])
    refine List.rel_append (ih (by omega)) ?_
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    have hmem : b (p + f) ∈ B.getD (p + f) Ival.top := hmB (p + f) (by omega)
    have hnR : ((n : Nat) : ℝ) ∈ Ival.ofRat c.prec ((n : Nat) : ℚ) := by
      exact_mod_cast Ival.mem_ofRat c.prec ((n : Nat) : ℚ)
    exact Ival.mem_add hmem hnR

/-- paired-factor membership (range induction). -/
theorem pfqPairForall₂ (c : Ctx) (A B : List Ival) (a b : ℕ → ℝ) (n : Nat)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i Ival.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i Ival.top) :
    ∀ m : Nat, m ≤ min A.length B.length → List.Forall₂ (fun x I => x ∈ I)
      ((List.range m).map fun (i : Nat) => |a i - b i| / (b i + (n : ℝ)) + 1)
      ((List.range m).map fun (i : Nat) =>
        pfqPairIval c (A.getD i Ival.top) (B.getD i Ival.top)
          (Ival.add c.prec (B.getD i Ival.top) (Ival.ofRat c.prec ((n : Nat) : ℚ)))) := by
  intro m
  induction m with
  | zero => intro _; exact List.Forall₂.nil
  | succ m ih =>
    intro hmle
    rw [List.range_succ, List.map_append, List.map_append]
    refine List.rel_append (ih (by omega)) ?_
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    have haM : a m ∈ A.getD m Ival.top := hmA m (by omega)
    have hbM : b m ∈ B.getD m Ival.top := hmB m (by omega)
    have hnR : ((n : Nat) : ℝ) ∈ Ival.ofRat c.prec ((n : Nat) : ℚ) := by
      exact_mod_cast Ival.mem_ofRat c.prec ((n : Nat) : ℚ)
    have hD : b m + (n : ℝ) ∈ Ival.add c.prec (B.getD m Ival.top)
        (Ival.ofRat c.prec ((n : Nat) : ℚ)) := Ival.mem_add hbM hnR
    unfold pfqPairIval
    exact Ival.mem_add (Ival.mem_div (Ival.mem_abs (Ival.mem_sub haM hbM)) hD)
      (by exact_mod_cast Ival.mem_ofRat c.prec (1 : ℚ))

/-- core evaluator: finite prefix or (`n+1` terms) + symmetric tail widening.
The loop returns `(Σ_{k<n} T_k, T_n)`; the enclosure is centered at
`Σ_{k<n+1} T_k = S + T_n` with radius `|T_n|·R/(1-R)`
(`pfqTail_corrected_succ`). -/
def pfqCoreIval (c : Ctx) (A B : List Ival) (Z : Ival) (n : Nat) : Ival :=
  match pfqFindTerm A 0 with
  | some (_, m) =>
    pfqFiniteIval c A B A.length B.length Z m
  | none =>
    if A.length > B.length + 1 then Ival.top
    else if pfqGuard B n then
      let res := pfqLoop c A B A.length B.length Z n 0
        (Ival.ofRat c.prec 0) (Ival.ofRat c.prec 1)
      let S := Ival.add c.prec res.1 res.2
      let p := A.length
      let q := B.length
      let W := Ival.mul c.prec (Ival.abs res.2)
        (pfqTailC c (pfqRIval c A B p q (Ival.abs Z)
          (Ival.abs (A.getD q Ival.top)) n))
      match W.hi with
      | some h => Ival.add c.prec S (Ival.ofRats c.prec (-h.toRat) h.toRat)
      | none => Ival.top
    else Ival.top

/-- core soundness (statement; proof via loop invariant + `pfqTail_corrected_succ`/
terminating path — the remaining assembly is sorry'd). -/
theorem pfqCore_sound (c : Ctx) (hc : c.Valid)
    (p q : Nat) (a b : ℕ → ℝ) (A B : List Ival) (Z : Ival) (z : ℝ) (n : Nat)
    (hlenA : A.length = p) (hlenB : B.length = q)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i Ival.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i Ival.top)
    (hmZ : z ∈ Z) :
    pfqReal p q a b z ∈ pfqCoreIval c A B Z n := by
  sorry

/-! ### List-based `HGFun` mirror (single registry entry).

Users write `Complex.HGFun` over multisets in goals; the reifier
(`reifyMultisetHGFun?`) normalizes literal spines to lists and targets
`HGFunL` below. The evaluator extracts real parts (imaginary parts must
be exactly zero) and runs the general `pfqCoreIval` core at any lengths. -/

/-- list-based `HGFun` mirror (registry vocabulary). -/
noncomputable def HGFunL (a b : List ℂ) (z : ℂ) : ℂ :=
  Complex.HGFun ↑a ↑b z

/-- real part of a complex enclosure with exactly-zero imaginary part. -/
def CBox.realOfZeroIm (B : CBox) : Option Ival :=
  match B.im.lo, B.im.hi with
  | some lo, some hi => if lo = hi ∧ lo.toRat = 0 then some B.re else none
  | _, _ => none

def HGFunL_ev (c : Ctx) : CEnc [.list .cplx, .list .cplx, .cplx] → CBox
  | .cons _ (some A) (.cons _ (some B) (.cons _ Z .nil)) =>
    match A.mapM CBox.realOfZeroIm, B.mapM CBox.realOfZeroIm,
        CBox.realOfZeroIm Z with
    | some Ar, some Br, some Zr =>
      let R := pfqCoreIval c Ar Br Zr (64 + 2 * c.prec)
      ⟨R, Ival.ofRat c.prec 0⟩
    | _, _, _ => CBox.top
  | _ => CBox.top

theorem HGFunL_sound (c : Ctx) :
    ∀ (vs : CVal [.list .cplx, .list .cplx, .cplx])
      (ds : CDen [.list .cplx, .list .cplx, .cplx]) (y : ℂ)
      (X : CEnc [.list .cplx, .list .cplx, .cplx]) (hc : c.Valid)
      (hg : y = applyCurried [.list .cplx, .list .cplx, .cplx] .cplx HGFunL vs)
      (hh : CEncHolds X ds) (hag : Agree vs ds),
    y ∈ HGFunL_ev c X := by
  sorry

@[lynth_cfn] def HGFunLR : CFn [.list .cplx, .list .cplx, .cplx] .cplx :=
  { name := "HGFun",
    fn := fun _ _ _ => (0 : ℂ),
    graph := CFn.graphOf [.list .cplx, .list .cplx, .cplx] .cplx HGFunL,
    exu := CFn.exuOf (tys := [.list .cplx, .list .cplx, .cplx]) .cplx HGFunL,
    ev := HGFunL_ev,
    sound := HGFunL_sound,
    cost := 1500 }


end Lynth.Interval.Fns

/-! ### Bridge to Mathlib's `Complex.regularizedHGFun` (ported from
`/tmp/pfq_thm_proof.lean`). -/

namespace Complex

open BigOperators

/-- The ascending Pochhammer symbol `(x)ₖ` as the product `∏_{j<k} (x+j)`. -/
lemma ascPochhammer_eval_eq_prod_range (x : ℂ) (k : ℕ) :
    (ascPochhammer ℂ k).eval x = ∏ j ∈ Finset.range k, (x + (j : ℂ)) := by
  induction k with
  | zero => simp
  | succ k ih => simp [ascPochhammer_succ_right, Finset.prod_range_succ, ih]

/-- BRIDGE (coefficients): at real parameters with no bottom parameter a nonpositive integer,
the `k`-th term of the (Γ-normalized) series `HGFun` is the real mirror `pfqTerm`. -/
theorem HGFunCoeff_mul_pow_ofReal (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (k : ℕ)
    (hb : ∀ j : ℕ, j < q → ∀ m : ℕ, (b j : ℂ) ≠ -(m : ℂ)) :
    HGFunCoeff ((Multiset.range p).map (fun i => (a i : ℂ)))
        ((Multiset.range q).map (fun j => (b j : ℂ))) k * (z : ℂ) ^ k
      = ((Lynth.Interval.Fns.pfqTerm p q a b z k : ℝ) : ℂ) := by
  have hG : ∀ j ∈ Finset.range q, Complex.Gamma ((b j : ℂ) + k)
      = Complex.Gamma (b j) * ∏ i ∈ Finset.range k, ((b j : ℂ) + (i : ℂ)) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have hne : Complex.Gamma (b j) ≠ 0 := Complex.Gamma_ne_zero (hb j hj')
    rw [← ascPochhammer_eval_eq_prod_range, ← Complex.Gamma_add_nat_div_Gamma_eq _ (hb j hj')]
    field_simp
  have hGne : ∏ j ∈ Finset.range q, Complex.Gamma (b j) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j hj => Complex.Gamma_ne_zero (hb j (Finset.mem_range.1 hj))
  have hm : ∀ {R : Type} [CommMonoid R] (n : ℕ) (f : ℕ → R),
      ((Multiset.range n).map f).prod = ∏ i ∈ Finset.range n, f i := fun _ _ => rfl
  unfold HGFunCoeff Complex.regularizedHGFunCoeff Lynth.Interval.Fns.pfqTerm
  simp only [Multiset.map_map, Function.comp_def, hm]
  rw [Finset.prod_congr rfl hG, Finset.prod_mul_distrib]
  simp only [ascPochhammer_eval_eq_prod_range]
  push_cast
  field_simp

/-- BRIDGE (function): at real parameters with no bottom parameter a nonpositive integer,
`HGFun` (built from Mathlib's `Complex.regularizedHGFun`) agrees with the real mirror
`pfqReal` at every real point `z`. No convergence hypothesis is needed: both sides are the
same `tsum` (and both are `0` when the series diverges). -/
theorem HGFun_ofReal_eq_pfqReal (p q : Nat) (a b : ℕ → ℝ) (z : ℝ)
    (hb : ∀ j : ℕ, j < q → ∀ m : ℕ, (b j : ℂ) ≠ -(m : ℂ)) :
    HGFun ((Multiset.range p).map (fun i => (a i : ℂ)))
        ((Multiset.range q).map (fun j => (b j : ℂ))) (z : ℂ)
      = ((Lynth.Interval.Fns.pfqReal p q a b z : ℝ) : ℂ) := by
  unfold HGFun Complex.regularizedHGFun Complex.regularizedHGFunSeries Lynth.Interval.Fns.pfqReal
  rw [← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq,
    Complex.ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [smul_eq_mul, ← mul_assoc]
  exact HGFunCoeff_mul_pow_ofReal p q a b z k hb

end Complex
