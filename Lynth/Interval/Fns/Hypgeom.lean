import Lynth.Interval.Fns.Zeta
import Lynth.Interval.Fns.Exp
import Lynth.Interval.Fns.ComplexElem
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

/-- PACKAGED CORE ENCLOSURE (ported from `/tmp/pfq_thm_proof.lean`).
Terminating tops give the exact prefix; the convergent case gives the
`(n+1)`-term partial sum plus `|T_n|·R/(1-R)`.  Consumed by `pfqCore_sound`. -/
theorem pfqCore_enclosure (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (n : Nat)
    (h : (∃ i₀ : Nat, ∃ m : Nat, i₀ < p ∧ a i₀ = -(m : ℝ))
       ∨ ((p ≤ q + 1) ∧ (∀ j : Nat, j < q → 0 < b j + (n : ℝ))
           ∧ pfqRatio p q a b |z| n < 1)) :
    (∃ m : Nat, pfqReal p q a b z
       = (Finset.range (m + 1)).sum (fun k => pfqTerm p q a b z k))
    ∨ (|pfqReal p q a b z - (Finset.range (n + 1)).sum (fun k => pfqTerm p q a b z k)|
       ≤ |pfqTerm p q a b z n|
         * (pfqRatio p q a b |z| n / (1 - pfqRatio p q a b |z| n))) := by
  rcases h with ⟨i₀, m, hi₀, hterm⟩ | ⟨hpq, hBpos, hR⟩
  · exact Or.inl ⟨m, pfqTerm_exact p q a b z m i₀ hi₀ hterm⟩
  · exact Or.inr (pfqTail_corrected_succ p q a b z n hpq hBpos hR)

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
    have h1 : p + (f + 1) = (p + f) + 1 := by omega
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, h1]
    rw [Finset.prod_Ico_succ_top (by omega : p ≤ p + f), ih]

/-- extras interval membership (fuel induction). -/
theorem pfqRDenForall₂ (c : Ctx) (B : List Ival) (b : ℕ → ℝ) (n p : Nat)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i Ival.top) :
    ∀ f : Nat, (∀ t : Nat, t < f → p + t < B.length) → List.Forall₂ (fun x I => x ∈ I)
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
    refine List.rel_append (ih (fun t ht => hle t (by omega))) ?_
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    have hmem : b (p + f) ∈ B.getD (p + f) Ival.top := hmB (p + f) (hle f (Nat.lt_succ_self f))
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

/-- denominator extras over `[p, p + (q-p))` agree with `[p, q)` (`p ≤ q+1`). -/
theorem pfqExtras_eq (p q : Nat) (hpq : p ≤ q + 1) (b : ℕ → ℝ) (n : Nat) :
    ∏ j ∈ Finset.Ico p (p + (q - p)), (b j + (n : ℝ))
      = ∏ j ∈ Finset.Ico p q, (b j + (n : ℝ)) := by
  by_cases h : p = q + 1
  · subst h
    have e0 : q - (q + 1) = 0 := by omega
    rw [e0, add_zero, Finset.Ico_eq_empty_of_le (le_refl (q + 1)),
      Finset.Ico_eq_empty_of_le (show q ≤ q + 1 by omega)]
  · have hle : p ≤ q := by omega
    rw [Nat.add_sub_cancel' hle]

/-- `R`-enclosure: the exact ratio bound lies in `pfqRIval`
(no positivity needed: `Ival.mem_div` is unconditional). -/
theorem mem_pfqRIval (c : Ctx) (hc : c.Valid)
    (a b : ℕ → ℝ) (A B : List Ival) (p q : Nat) (Z : Ival) (z : ℝ) (n : Nat)
    (hlenA : A.length = p) (hlenB : B.length = q)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i Ival.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i Ival.top)
    (hmZ : z ∈ Z)
    (hpq : p ≤ q + 1) :
    pfqRatio p q a b |z| n ∈ pfqRIval c A B p q (Ival.abs Z)
      (Ival.abs (A.getD q Ival.top)) n := by
  have hZabs : |z| ∈ Ival.abs Z := Ival.mem_abs hmZ
  have hN := mem_iprod c hc _ _
    (pfqPairForall₂ c A B a b n hmA hmB (min p q) (by omega))
  rw [list_prod_map_range] at hN
  have hD := mem_iprod c hc _ _
    (pfqRDenForall₂ c B b n p hmB (q - p) (fun t ht => by omega))
  rw [pfqRDenAux_eq, pfqExtras_eq p q hpq b n] at hD
  have hN1 : ((n : ℝ) + 1) ∈ Ival.ofRat c.prec (((n : Nat) : ℚ) + 1) := by
    exact_mod_cast Ival.mem_ofRat c.prec (((n : Nat) : ℚ) + 1)
  have hDen : (∏ j ∈ Finset.Ico p q, (b j + (n : ℝ))) * ((n : ℝ) + 1)
      ∈ Ival.mul c.prec (iprod c (pfqRDenAux c B n p (q - p)))
        (Ival.ofRat c.prec (((n : Nat) : ℚ) + 1)) :=
    Ival.mem_mul hD hN1
  by_cases hpq1 : p = q + 1
  · have hAq : |a q| ∈ Ival.abs (A.getD q Ival.top) :=
      Ival.mem_abs (hmA q (by omega))
    have hTop : |a q| + ((n : ℝ) + 1)
        ∈ Ival.add c.prec (Ival.abs (A.getD q Ival.top))
          (Ival.ofRat c.prec (((n : Nat) : ℚ) + 1)) :=
      Ival.mem_add hAq hN1
    have hval : pfqRatio p q a b |z| n
        = (|z| * (∏ i ∈ Finset.range (min p q), (|a i - b i| / (b i + (n : ℝ)) + 1))
          / ((∏ j ∈ Finset.Ico p q, (b j + (n : ℝ))) * ((n : ℝ) + 1)))
          * (|a q| + ((n : ℝ) + 1)) := by
      unfold pfqRatio
      rw [ite_eq_left hpq1]
      ring
    rw [hval]
    simp only [pfqRIval, ite_eq_left hpq1]
    exact Ival.mem_mul
      (Ival.mem_div (Ival.mem_mul hZabs hN) hDen) hTop
  · have hbase : pfqRatio p q a b |z| n
        = |z| * (∏ i ∈ Finset.range (min p q), (|a i - b i| / (b i + (n : ℝ)) + 1))
          / ((∏ j ∈ Finset.Ico p q, (b j + (n : ℝ))) * ((n : ℝ) + 1)) := by
      unfold pfqRatio
      rw [ite_eq_right hpq1]
      ring
    rw [hbase]
    simp only [pfqRIval, ite_eq_right hpq1]
    exact Ival.mem_div (Ival.mem_mul hZabs hN) hDen

/-- real part of a complex enclosure with exactly-zero imaginary part. -/
def CBox.realOfZeroIm (B : CBox) : Option Ival :=
  match B.im.lo, B.im.hi with
  | some lo, some hi => if lo = hi ∧ lo.toRat = 0 then some B.re else none
  | _, _ => none

/-- guard facts give the bridge hypothesis: bottoms avoid nonpositive integers. -/
theorem hb_of_guard (b : ℕ → ℝ) (q n : Nat)
    (hpos : ∀ j : Nat, j < q → 0 < b j + (n : ℝ))
    (hne : ∀ j : Nat, j < q → ∀ k : Nat, k < n → b j + (k : ℝ) ≠ 0) :
    ∀ j : Nat, j < q → ∀ m : ℕ, (b j : ℂ) ≠ -(m : ℂ) := by
  intro j hj m heq
  have hr : b j = -((m : Nat) : ℝ) := by
    apply Complex.ofReal_injective
    rw [heq]
    simp
  by_cases hm : m < n
  · exact hne j hj m hm (by linarith)
  · exfalso
    have hle : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : n ≤ m)
    have h0 : b j + (n : ℝ) ≤ 0 := by linarith
    linarith [hpos j hj]

/-- a complex number with zero imaginary part is the coercion of its real part. -/
theorem ofReal_of_re {z : ℂ} (h : z.im = 0) : ((z.re : ℝ) : ℂ) = z := by
  apply Complex.ext
  · exact Complex.ofReal_re _
  · rw [Complex.ofReal_im]; exact h.symm

/-- zero-imaginary projection is correct on members. -/
theorem realOfZeroIm_ok (B : CBox) (R : Ival) (z : ℂ)
    (hR : CBox.realOfZeroIm B = some R) (hm : z ∈ B) :
    z.re ∈ R ∧ z.im = 0 := by
  cases hlo : B.im.lo with
  | none => simp [CBox.realOfZeroIm, hlo] at hR
  | some lo =>
    cases hhi : B.im.hi with
    | none => simp [CBox.realOfZeroIm, hlo, hhi] at hR
    | some hi =>
      simp only [CBox.realOfZeroIm, hlo, hhi] at hR
      by_cases hc : lo = hi ∧ lo.toRat = 0
      · rw [ite_eq_left hc] at hR
        have hReq : B.re = R := Option.some_inj.mp hR
        have him0 : z.im = 0 := by
          have hhi' : B.im.hi = some lo := by rw [← hc.1] at hhi; exact hhi
          have hpt := dyPointMem (X := B.im) hm.2 hlo hhi'
          rw [hc.2] at hpt
          exact_mod_cast hpt
        refine ⟨?_, him0⟩
        rw [← hReq]; exact hm.1
      · rw [ite_eq_right hc] at hR
        exact absurd hR (by simp)

/-- `getD` agrees with `getElem` in bounds. -/
theorem getD_of_lt {α : Type} (l : List α) (d : α) (i : Nat) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- extract real parameters from successful zero-imaginary projections. -/
theorem extract_real_params (A : List CBox) :
    ∀ (Ar : List Ival) (a d : List ℂ),
    a = d →
    List.Forall₂ (Ty.Mem .cplx) A d →
    List.Forall₂ (fun B R => CBox.realOfZeroIm B = some R) A Ar →
    Ar.length = A.length ∧ a.length = A.length ∧
    ∀ i : Nat, i < A.length →
      (a.getD i 0).re ∈ Ar.getD i Ival.top ∧ (a.getD i 0).im = 0 := by
  induction A with
  | nil =>
    intro Ar a d had hHd hEx
    cases hHd with
    | nil =>
      cases hEx with
      | nil =>
        cases had
        refine ⟨rfl, rfl, fun i hi => by simp at hi⟩
  | cons B Bs ih =>
    intro Ar a d had hHd hEx
    cases hHd with
    | cons hHd1 hHd2 =>
      cases hEx with
      | cons hEx1 hEx2 =>
        cases had
        have hmemB : _ ∈ B := hHd1
        obtain ⟨hAr, ha, hmem⟩ := ih _ _ _ rfl hHd2 hEx2
        refine ⟨by exact congrArg (· + 1) hAr, by exact congrArg (· + 1) ha, fun i hi => ?_⟩
        cases i with
        | zero => exact realOfZeroIm_ok B _ _ hEx1 hmemB
        | succ i =>
          have hi' : i < Bs.length := by simp only [List.length_cons] at hi; omega
          exact hmem i hi'

/-- core evaluator: finite prefix or (`n+1` terms) + symmetric tail widening.
The loop returns `(Σ_{k<n} T_k, T_n)`; the enclosure is centered at
`Σ_{k<n+1} T_k = S + T_n` with radius `|T_n|·R/(1-R)`
(`pfqTail_corrected_succ`). -/
def pfqCoreIval (c : Ctx) (A B : List Ival) (Z : Ival) (n : Nat) : Ival :=
  match pfqFindTerm A 0 with
  | some (_, m) =>
    -- finite path needs bottom cleanliness too: the `HGFun` bridge only holds
    -- away from bottom poles (e.g. ₂F₁(-1;0;z) is `0` in Mathlib, `1` as a sum).
    if pfqGuard B n then pfqFiniteIval c A B A.length B.length Z m else Ival.top
  | none =>
    if A.length > B.length + 1 then Ival.top
    else if pfqGuard B n then
      let R := pfqRIval c A B A.length B.length (Ival.abs Z)
        (Ival.abs (A.getD (B.length) Ival.top)) n
      match R.hi with
      | none => Ival.top
      | some hR =>
        if hR.toRat < 1 then
          let res := pfqLoop c A B A.length B.length Z n 0
            (Ival.ofRat c.prec 0) (Ival.ofRat c.prec 1)
          let S := Ival.add c.prec res.1 res.2
          let W := Ival.mul c.prec (Ival.abs res.2)
            (Ival.div c.prec R
              (Ival.sub c.prec (Ival.ofRat c.prec 1) R))
          match W.hi with
          | some h => Ival.add c.prec S (Ival.ofRats c.prec (-h.toRat) h.toRat)
          | none => Ival.top
        else Ival.top
    else Ival.top

/-- core soundness (via loop invariant + `pfqTail_corrected_succ` / terminating path). -/
theorem pfqCore_sound (c : Ctx) (hc : c.Valid)
    (p q : Nat) (a b : ℕ → ℝ) (A B : List Ival) (Z : Ival) (z : ℝ) (n : Nat)
    (hlenA : A.length = p) (hlenB : B.length = q)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i Ival.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i Ival.top)
    (hmZ : z ∈ Z) :
    pfqReal p q a b z ∈ pfqCoreIval c A B Z n := by
  unfold pfqCoreIval
  cases hft : pfqFindTerm A 0 with
  | none =>
    show pfqReal p q a b z ∈
      (if A.length > B.length + 1 then Ival.top
        else if pfqGuard B n then
          let R := pfqRIval c A B A.length B.length (Ival.abs Z)
            (Ival.abs (A.getD (B.length) Ival.top)) n
          match R.hi with
          | none => Ival.top
          | some hR =>
            if hR.toRat < 1 then
              let res := pfqLoop c A B A.length B.length Z n 0
                (Ival.ofRat c.prec 0) (Ival.ofRat c.prec 1)
              let S := Ival.add c.prec res.1 res.2
              let W := Ival.mul c.prec (Ival.abs res.2)
                (Ival.div c.prec R
                  (Ival.sub c.prec (Ival.ofRat c.prec 1) R))
              match W.hi with
              | some h => Ival.add c.prec S (Ival.ofRats c.prec (-h.toRat) h.toRat)
              | none => Ival.top
            else Ival.top
        else Ival.top)
    by_cases hlen : A.length > B.length + 1
    · rw [ite_eq_left hlen]
      exact Ival.mem_top _
    · rw [ite_eq_right hlen]
      cases hguard : pfqGuard B n with
      | false =>
        show pfqReal p q a b z ∈ Ival.top
        exact Ival.mem_top _
      | true =>
        set resI := pfqLoop c A B A.length B.length Z n 0
          (Ival.ofRat c.prec 0) (Ival.ofRat c.prec 1) with hresI
        set SI := Ival.add c.prec resI.1 resI.2 with hSI
        set RIV := pfqRIval c A B A.length B.length (Ival.abs Z)
          (Ival.abs (A.getD (B.length) Ival.top)) n with hRIV
        set W := Ival.mul c.prec (Ival.abs resI.2)
          (Ival.div c.prec RIV (Ival.sub c.prec (Ival.ofRat c.prec 1) RIV)) with hWdef
        show pfqReal p q a b z ∈
          (match RIV.hi with
          | none => Ival.top
          | some hR =>
            if hR.toRat < 1 then
              match W.hi with
              | some h => Ival.add c.prec SI (Ival.ofRats c.prec (-h.toRat) h.toRat)
              | none => Ival.top
            else Ival.top)
        rw [← hlenA, ← hlenB]
        -- guard facts (offset form)
        have hmB' : ∀ i : Nat, i < B.length → b (0 + i) ∈ B.getD i Ival.top := by
          intro i hi
          rw [Nat.zero_add]
          exact hmB i hi
        have hG := pfqGuard_ok b B 0 n hmB' hguard
        obtain ⟨hpos, hne⟩ := hG
        have hpq' : A.length ≤ B.length + 1 := by omega
        have hBpos' : ∀ j : Nat, j < B.length → 0 < b j + (n : ℝ) := by
          intro j hj
          have h1 := hpos j hj
          rw [Nat.zero_add] at h1
          linarith
        have hBne : ∀ j : Nat, j < B.length → ∀ k : Nat, k < n → b j + (k : ℝ) ≠ 0 := by
          intro j hj k hk
          have h1 := hne j hj k hk
          rw [Nat.zero_add] at h1
          exact h1
        -- loop: prefix sum + last term
        have hS0 : (0 : ℝ) ∈ Ival.ofRat c.prec 0 := by
          exact_mod_cast Ival.mem_ofRat c.prec (0 : ℚ)
        have hT0 : (1 : ℝ) ∈ Ival.ofRat c.prec 1 := by
          exact_mod_cast Ival.mem_ofRat c.prec (1 : ℚ)
        have hSr : (0 : ℝ)
            = (Finset.range 0).sum (fun j => pfqTerm A.length B.length a b z j) := by
          simp
        have hTr : (1 : ℝ) = pfqTerm A.length B.length a b z 0 :=
          (pfqTerm_zero A.length B.length a b z).symm
        have hLoop : (Finset.range (0 + n)).sum (fun j => pfqTerm A.length B.length a b z j)
              ∈ resI.1
            ∧ pfqTerm A.length B.length a b z (0 + n) ∈ resI.2 :=
          mem_pfqLoop c hc a b A B Z z n hmA hmB hmZ hBne
            n 0 (by omega) _ _ _ _ hS0 hT0 hSr hTr
        simp only [Nat.zero_add] at hLoop
        obtain ⟨hS, hT⟩ := hLoop
        -- center = (n+1)-term partial sum
        have hSexact : (Finset.range (n + 1)).sum (fun j => pfqTerm A.length B.length a b z j)
            = (Finset.range n).sum (fun j => pfqTerm A.length B.length a b z j)
              + pfqTerm A.length B.length a b z n :=
          Finset.sum_range_succ _ n
        have hSmem : (Finset.range (n + 1)).sum (fun j => pfqTerm A.length B.length a b z j)
            ∈ SI := by
          rw [hSexact]
          exact Ival.mem_add hS hT
        -- ratio bound + R < 1 from the tail-scale enclosure
        have hRmem : pfqRatio A.length B.length a b |z| n ∈ RIV :=
          mem_pfqRIval c hc a b A B A.length B.length Z z n rfl rfl
            hmA hmB hmZ hpq'
        cases hRhi : RIV.hi with
        | none =>
          show pfqReal A.length B.length a b z ∈ Ival.top
          exact Ival.mem_top _
        | some hRD =>
          show pfqReal A.length B.length a b z ∈
            (if hRD.toRat < 1 then
              match W.hi with
              | some h => Ival.add c.prec SI (Ival.ofRats c.prec (-h.toRat) h.toRat)
              | none => Ival.top
            else Ival.top)
          by_cases hRlt : hRD.toRat < 1
          · rw [ite_eq_left hRlt]
            cases hW : W.hi with
            | none =>
              show pfqReal A.length B.length a b z ∈ Ival.top
              exact Ival.mem_top _
            | some h =>
              show pfqReal A.length B.length a b z ∈
                Ival.add c.prec SI (Ival.ofRats c.prec (-h.toRat) h.toRat)
              -- R < 1: tail bound applies
              have hR : pfqRatio A.length B.length a b |z| n < 1 := by
                have hle : pfqRatio A.length B.length a b |z| n ≤ ((hRD.toRat : ℚ) : ℝ) := by
                  have hmem2 := (Ival.mem_def.mp hRmem).2
                  rw [hRhi] at hmem2
                  rw [Ival.leHi_some] at hmem2
                  rwa [Dy.toReal_def] at hmem2
                have hlt1 : ((hRD.toRat : ℚ) : ℝ) < 1 := by exact_mod_cast hRlt
                linarith
              have h1 : (1 : ℝ) ∈ Ival.ofRat c.prec 1 := by
                exact_mod_cast Ival.mem_ofRat c.prec (1 : ℚ)
              have hCmem : pfqRatio A.length B.length a b |z| n
                  / (1 - pfqRatio A.length B.length a b |z| n)
                  ∈ Ival.div c.prec RIV
                    (Ival.sub c.prec (Ival.ofRat c.prec 1) RIV) :=
                Ival.mem_div hRmem (Ival.mem_sub h1 hRmem)
              have hTabs : |pfqTerm A.length B.length a b z n| ∈ Ival.abs resI.2 :=
                Ival.mem_abs hT
              have hWmem : |pfqTerm A.length B.length a b z n|
                  * (pfqRatio A.length B.length a b |z| n
                    / (1 - pfqRatio A.length B.length a b |z| n)) ∈ W :=
                Ival.mem_mul hTabs hCmem
              have hWle : |pfqTerm A.length B.length a b z n|
                  * (pfqRatio A.length B.length a b |z| n
                    / (1 - pfqRatio A.length B.length a b |z| n))
                  ≤ ((h.toRat : ℚ) : ℝ) := by
                have hle := (Ival.mem_def.mp hWmem).2
                rw [hW] at hle
                rw [Ival.leHi_some] at hle
                rwa [Dy.toReal_def] at hle
              have htail := pfqTail_corrected_succ A.length B.length a b z n
                hpq' hBpos' hR
              have hrad : |pfqReal A.length B.length a b z
                  - (Finset.range (n + 1)).sum
                    (fun j => pfqTerm A.length B.length a b z j)|
                  ≤ ((h.toRat : ℚ) : ℝ) :=
                le_trans htail hWle
              have hdiff : pfqReal A.length B.length a b z
                  - (Finset.range (n + 1)).sum
                    (fun j => pfqTerm A.length B.length a b z j)
                  ∈ Ival.ofRats c.prec (-h.toRat) h.toRat := by
                obtain ⟨hlo, hhi⟩ := abs_le.mp hrad
                refine Ival.mem_ofRats ?_ hhi
                simpa using hlo
              have hpeq : pfqReal A.length B.length a b z
                  = (Finset.range (n + 1)).sum
                      (fun j => pfqTerm A.length B.length a b z j)
                    + (pfqReal A.length B.length a b z
                      - (Finset.range (n + 1)).sum
                        (fun j => pfqTerm A.length B.length a b z j)) := by
                ring
              rw [hpeq]
              exact Ival.mem_add hSmem hdiff
          · rw [ite_eq_right hRlt]
            show pfqReal A.length B.length a b z ∈ Ival.top
            exact Ival.mem_top _
  | some r =>
    obtain ⟨i₀, m⟩ := r
    show pfqReal p q a b z ∈
      (if pfqGuard B n then pfqFiniteIval c A B A.length B.length Z m else Ival.top)
    cases hguard : pfqGuard B n with
    | false =>
      show pfqReal p q a b z ∈ Ival.top
      exact Ival.mem_top _
    | true =>
      rw [← hlenA, ← hlenB]
      have hmA' : ∀ i : Nat, i < A.length → a (0 + i) ∈ A.getD i Ival.top := by
        intro i hi
        rw [Nat.zero_add]
        exact hmA i hi
      have hok := pfqFindTerm_ok a A 0 hmA' _ hft i₀ m rfl
      obtain ⟨hlt, hval⟩ := hok
      have hi₀ : i₀ < A.length := by omega
      exact pfqFinite_sound c hc _ _ a b A B Z z m i₀ rfl rfl hmA hmB hmZ hi₀ hval

/-! ### Complex core (FLINT `pfq_direct`, complex-line form).

Mirrors the real core with `CBox` arithmetic: forward term recurrence,
norm-based ratio bound (`acb_hypgeom/pfq_bound_factor.c`, complex form:
`‖a+k‖/‖b+k‖ ≤ ‖a-b‖/‖b+n‖ + 1` for `k ≥ n` once `Re b + n > 0`, since
`‖b+k‖ ≥ ‖b+n‖` there), 0-exclusion bottom guard, terminating-prefix
shortcut. `HGFunL_ev` uses it when any parameter (or `z`) is genuinely
complex; all-real inputs keep the real core above (same enclosures, same
heartbeats). Every soundness lemma below is `sorry`'d; proofs are handed
off in `/tmp/hyperc` (each docstring names the real mirror to follow).
-/

/-- one complex series term (rising products; `T_0 = 1` definitionally). -/
noncomputable def cpfqTerm (p q : Nat) (a b : ℕ → ℂ) (z : ℂ) (k : ℕ) : ℂ :=
  (∏ i ∈ Finset.range p, ∏ j ∈ Finset.range k, (a i + (j : ℂ)))
    / (∏ i ∈ Finset.range q, ∏ j ∈ Finset.range k, (b i + (j : ℂ)))
    * z ^ k / (Nat.factorial k : ℂ)

/-- the complex `pFq` value as a series. -/
noncomputable def cpfqComplex (p q : Nat) (a b : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' k, cpfqTerm p q a b z k

/-- product of boxes (`1` on `[]`). -/
def cprod (c : Ctx) : List CBox → CBox
  | [] => ⟨Ival.one, Ival.zero⟩
  | B :: Bs => CBox.mul c.prec B (cprod c Bs)

/-- sum of boxes (`0` on `[]`). -/
def csum (c : Ctx) : List CBox → CBox
  | [] => ⟨Ival.zero, Ival.zero⟩
  | B :: Bs => CBox.add c.prec B (csum c Bs)

/-- `((k : ℕ) : ℂ)` as a box. -/
def cNatBox (c : Ctx) (k : Nat) : CBox :=
  ⟨Ival.ofRat c.prec (k : ℚ), Ival.zero⟩

/-- one step of the forward recurrence. -/
def cpfqStepBox (c : Ctx) (A B : List CBox) (p q : Nat) (Z T : CBox) (k : Nat) : CBox :=
  let num := cprod c ((List.range p).map fun i =>
    CBox.add c.prec (A.getD i CBox.top) (cNatBox c k))
  let den := cprod c ((List.range q).map fun j =>
    CBox.add c.prec (B.getD j CBox.top) (cNatBox c k))
  CBox.div c.prec (CBox.mul c.prec (CBox.mul c.prec T num) Z)
    (CBox.mul c.prec den (cNatBox c (k + 1)))

/-- fuel loop: `(sum of terms k..k+f-1, T_{k+f})`, structural on fuel. -/
def cpfqLoop (c : Ctx) (A B : List CBox) (p q : Nat) (Z : CBox) :
    Nat → Nat → CBox → CBox → CBox × CBox
  | 0, _, S, T => (S, T)
  | f + 1, k, S, T =>
    cpfqLoop c A B p q Z f (k + 1) (CBox.add c.prec S T)
      (cpfqStepBox c A B p q Z T k)

/-- paired norm factor `‖aᵢ-bᵢ‖/Dᵢ + 1`. -/
def cpfqPairBox (c : Ctx) (Ai Bi Di : Ival) : Ival :=
  Ival.add c.prec
    (Ival.div c.prec (Ival.abs (Ival.sub c.prec Ai Bi)) Di)
    (Ival.ofRat c.prec 1)

/-- `R` denominator extras over `j ∈ [p, q)`, fuel-indexed. -/
def cpfqRDenAux (c : Ctx) (nB : List Ival) (n : Nat) : Nat → Nat → List Ival
  | _, 0 => []
  | p, f + 1 => cpfqRDenAux c nB n p f
    ++ [Ival.add c.prec (nB.getD (p + f) Ival.top)
      (Ival.ofRat c.prec ((n : Nat) : ℚ))]

/-- full `R` norm-ratio bound (mirrors `pfqRatio`, same `if`). -/
def cpfqRBox (c : Ctx) (nA nB : List Ival) (p q : Nat) (Zabs : Ival)
    (aq : Ival) (n : Nat) : Ival :=
  let base := Ival.div c.prec
    (Ival.mul c.prec Zabs (iprod c ((List.range (min p q)).map fun i =>
      cpfqPairBox c (nA.getD i Ival.top) (nB.getD i Ival.top)
        (Ival.add c.prec (nB.getD i Ival.top) (Ival.ofRat c.prec ((n : Nat) : ℚ))))))
    (Ival.mul c.prec
      (iprod c (cpfqRDenAux c nB n p (q - p)))
      (Ival.ofRat c.prec (((n : Nat) : ℚ) + 1)))
  if p = q + 1 then
    Ival.mul c.prec base
      (Ival.add c.prec aq (Ival.ofRat c.prec (((n : Nat) : ℚ) + 1)))
  else base

/-- one bottom-box × shift avoids `0` (endpoint check). -/
def cpfqGuardElem (J : CBox) (k : Nat) : Bool :=
  match J.re.lo, J.re.hi, J.im.lo, J.im.hi with
  | some rlo, some rhi, some ilo, some ihi =>
    decide ((rhi.toRat + (k : ℚ) < 0 ∨ 0 < rlo.toRat + (k : ℚ))
      ∨ (ihi.toRat < 0 ∨ 0 < ilo.toRat))
  | _, _, _, _ => false

/-- real part of a bottom box stays positive past the shift (for the
ratio monotonicity `‖b+k‖ ≥ ‖b+n‖`, `k ≥ n`). -/
def cpfqGuardRe (J : CBox) (n : Nat) : Bool :=
  match J.re.lo with
  | some rlo => decide (0 < rlo.toRat + (n : ℚ))
  | none => false

/-- bottom guard: shifted bottoms keep positive real part, and no pole
in range. -/
def cpfqGuard (B : List CBox) (n : Nat) : Bool :=
  B.all (fun J => cpfqGuardRe J n) &&
  (List.range n).all (fun k => B.all (fun J => cpfqGuardElem J k))

/-- rising product box `∏_{j<k} (S + j)`. -/
def risingCBox (c : Ctx) (S : CBox) : Nat → CBox
  | 0 => ⟨Ival.one, Ival.zero⟩
  | k + 1 => CBox.mul c.prec (risingCBox c S k)
    (CBox.add c.prec S (cNatBox c k))

/-- closed-form term box. -/
def cpfqTermBox (c : Ctx) (A B : List CBox) (p q : Nat) (Z : CBox) (k : Nat) : CBox :=
  CBox.div c.prec
    (CBox.div c.prec
      (CBox.mul c.prec
        (cprod c ((List.range p).map fun i => risingCBox c (A.getD i CBox.top) k))
        (CBox.npow c.prec Z k))
      (cprod c ((List.range q).map fun j => risingCBox c (B.getD j CBox.top) k)))
    (cNatBox c (Nat.factorial k))

/-- terminating-top search: first `(index, m)` with point value `-m`
(imaginary part exactly zero). -/
def cpfqFindTerm : List CBox → Nat → Option (Nat × Nat)
  | [], _ => none
  | B :: Bs, i =>
    match B.re.lo, B.re.hi, B.im.lo, B.im.hi with
    | some rlo, some rhi, some ilo, some ihi =>
      if rlo = rhi && ilo = ihi && ilo.toRat = 0 then
        let q := rlo.toRat
        if q.den = 1 ∧ q.num ≤ 0 then some (i, (-q.num).toNat)
        else cpfqFindTerm Bs (i + 1)
      else cpfqFindTerm Bs (i + 1)
    | _, _, _, _ => cpfqFindTerm Bs (i + 1)

/-- finite prefix enclosure (exact identity, no tail). -/
def cpfqFiniteBox (c : Ctx) (A B : List CBox) (p q : Nat) (Z : CBox)
    (m : Nat) : CBox :=
  csum c ((List.range (m + 1)).map fun k => cpfqTermBox c A B p q Z k)

/-- core evaluator: finite prefix or (`n+1` terms) + symmetric tail disc.
The loop returns `(Σ_{k<n} T_k, T_n)`; the enclosure is centered at
`Σ_{k<n+1} T_k = S + T_n` with disc radius `‖T_n‖·R/(1-R)`. -/
def cpfqCoreBox (c : Ctx) (A B : List CBox) (Z : CBox) (n : Nat) : CBox :=
  match cpfqFindTerm A 0 with
  | some (_, m) =>
    -- finite path needs bottom cleanliness too: the `HGFun` bridge only holds
    -- away from bottom poles.
    if cpfqGuard B n then cpfqFiniteBox c A B A.length B.length Z m else CBox.top
  | none =>
    if A.length > B.length + 1 then CBox.top
    else if cpfqGuard B n then
      let nA := (List.range A.length).map fun i => CBox.norm c.prec (A.getD i CBox.top)
      let nB := (List.range B.length).map fun j => CBox.norm c.prec (B.getD j CBox.top)
      let R := cpfqRBox c nA nB A.length B.length (CBox.norm c.prec Z)
        (CBox.norm c.prec (A.getD B.length CBox.top)) n
      match R.hi with
      | none => CBox.top
      | some hR =>
        if hR.toRat < 1 then
          let res := cpfqLoop c A B A.length B.length Z n 0
            ⟨Ival.zero, Ival.zero⟩ ⟨Ival.one, Ival.zero⟩
          let S := CBox.add c.prec res.1 res.2
          let W := Ival.mul c.prec (CBox.norm c.prec res.2)
            (Ival.div c.prec R
              (Ival.sub c.prec (Ival.ofRat c.prec 1) R))
          match W.hi with
          | some h => CBox.add c.prec S ⟨Ival.ofRats c.prec (-h.toRat) h.toRat,
              Ival.ofRats c.prec (-h.toRat) h.toRat⟩
          | none => CBox.top
        else CBox.top
    else CBox.top

/-- term recurrence (mirror `pfqTerm_succ`). -/
theorem cpfqTerm_succ (p q : Nat) (a b : ℕ → ℂ) (z : ℂ) (k : Nat)
    (hB : ∀ j : Nat, j < q → (b j + (k : ℂ)) ≠ 0) :
    cpfqTerm p q a b z (k + 1) = cpfqTerm p q a b z k
      * ((∏ i ∈ Finset.range p, (a i + (k : ℂ)))
        / (∏ j ∈ Finset.range q, (b j + (k : ℂ))) * z / ((k : ℂ) + 1)) := by
  sorry

/-- product-box membership (mirror `mem_iprod`). -/
theorem mem_cprod (c : Ctx) (hc : c.Valid) (L : List CBox) (v : List ℂ)
    (h : List.Forall₂ (fun z B => z ∈ B) v L) :
    v.prod ∈ cprod c L := by
  sorry

/-- sum-box membership (mirror `mem_isum`). -/
theorem mem_csum (c : Ctx) (hc : c.Valid) (L : List CBox) (v : List ℂ)
    (h : List.Forall₂ (fun z B => z ∈ B) v L) :
    v.sum ∈ csum c L := by
  sorry

/-- nat-cast box membership. -/
theorem mem_cNatBox (c : Ctx) (k : Nat) : ((k : ℕ) : ℂ) ∈ cNatBox c k := by
  sorry

/-- range-mapped shifted-factor memberships (mirror `pfqAddForall₂`). -/
theorem cpfqAddForall₂ (c : Ctx) (L : List CBox) (v : ℕ → ℂ) (k : Nat)
    (hm : ∀ i : Nat, i < L.length → v i ∈ L.getD i CBox.top) :
    List.Forall₂ (fun z B => z ∈ B)
      ((List.range L.length).map fun i => v i + (k : ℂ))
      ((List.range L.length).map fun i =>
        CBox.add c.prec (L.getD i CBox.top) (cNatBox c k)) := by
  sorry

/-- step membership (mirror `mem_pfqStep`). -/
theorem mem_cpfqStep (c : Ctx) (hc : c.Valid)
    (a b : ℕ → ℂ) (A B : List CBox) (Z : CBox) (z : ℂ) (k : Nat)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i CBox.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i CBox.top)
    (hmZ : z ∈ Z) (T : CBox) (Tk : ℂ) (hT : Tk ∈ T) :
    Tk * ((∏ i ∈ Finset.range A.length, (a i + (k : ℂ)))
      / (∏ j ∈ Finset.range B.length, (b j + (k : ℂ))) * z / ((k : ℂ) + 1))
      ∈ cpfqStepBox c A B A.length B.length Z T k := by
  sorry

/-- joint loop invariant (mirror `mem_pfqLoop`). -/
theorem mem_cpfqLoop (c : Ctx) (hc : c.Valid)
    (a b : ℕ → ℂ) (A B : List CBox) (Z : CBox) (z : ℂ) (n : Nat)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i CBox.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i CBox.top)
    (hmZ : z ∈ Z)
    (hBne : ∀ j : Nat, j < B.length → ∀ k : Nat, k < n → (b j + (k : ℂ)) ≠ 0) :
    ∀ (f k : Nat), k + f ≤ n → ∀ (S T : CBox) (Sr Tr : ℂ),
    Sr ∈ S → Tr ∈ T →
    Sr = (Finset.range k).sum (fun j => cpfqTerm A.length B.length a b z j) →
    Tr = cpfqTerm A.length B.length a b z k →
    ((Finset.range (k + f)).sum (fun j => cpfqTerm A.length B.length a b z j)
      ∈ (cpfqLoop c A B A.length B.length Z f k S T).1
    ∧ cpfqTerm A.length B.length a b z (k + f)
      ∈ (cpfqLoop c A B A.length B.length Z f k S T).2) := by
  sorry

/-- where `cpfqRatio` is the uniform later-term norm ratio
(`‖T_{k+1}‖/‖T_k‖ ≤ R` for `k ≥ n`), mirroring `pfqRatio`. -/
noncomputable def cpfqRatio (p q : Nat) (a b : ℕ → ℂ) (Z : ℝ) (n : Nat) : ℝ :=
  Z * (∏ i ∈ Finset.range (min p q), (‖a i - b i‖ / ‖b i + (n : ℂ)‖ + 1))
    / ((∏ j ∈ Finset.Ico p q, ‖b j + (n : ℂ)‖) * ((n : ℝ) + 1))
    * (if p = q + 1 then (‖a q‖ + (n : ℝ) + 1) else 1)

/-- ratio-bound membership (mirror `mem_pfqRIval`; per-factor steps use
`CBox.mem_norm`, `Ival.mem_div/abs/sub` and the paired estimate
`‖a+k‖/‖b+k‖ ≤ ‖a-b‖/‖b+n‖ + 1` for `k ≥ n`). -/
theorem mem_cpfqR (c : Ctx) (hc : c.Valid)
    (a b : ℕ → ℂ) (A B : List CBox) (p q : Nat)
    (nA nB : List Ival) (Z : CBox) (z : ℂ) (n : Nat)
    (hmA : ∀ i : Nat, i < A.length → ‖a i‖ ∈ nA.getD i Ival.top)
    (hmB : ∀ i : Nat, i < B.length → ‖b i‖ ∈ nB.getD i Ival.top)
    (hmZ : ‖z‖ ∈ CBox.norm c.prec Z)
    (hpq : p ≤ q + 1) :
    cpfqRatio p q a b ‖z‖ n ∈ cpfqRBox c nA nB p q
      (CBox.norm c.prec Z) (CBox.norm c.prec (A.getD q CBox.top)) n := by
  sorry

/-- guard element correctness: exclusion + real-part positivity
(mirror `pfqGuardElem_ok`). -/
theorem cpfqGuardElem_ok (J : CBox) (k n : Nat) (lo hi : Dy)
    (hlo : J.re.lo = some lo) (hhi : J.re.hi = some hi)
    (b : ℂ) (hb : b ∈ J) (h : cpfqGuardElem J k = true) :
    (b + (k : ℂ)) ≠ 0 ∧ 0 < (b + (n : ℂ)).re := by
  sorry

/-- guard correctness (mirror `pfqGuard_ok`). -/
theorem cpfqGuard_ok (b : ℕ → ℂ) (B : List CBox) (n : Nat)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i CBox.top)
    (hguard : cpfqGuard B n = true) :
    (∀ j : Nat, j < B.length → 0 < (b j + (n : ℂ)).re)
      ∧ (∀ j : Nat, j < B.length → ∀ k : Nat, k < n → (b j + (k : ℂ)) ≠ 0) := by
  sorry

/-- rising-product box membership (mirror `mem_risingZ`). -/
theorem mem_risingCBox (c : Ctx) (hc : c.Valid) (S : CBox) (s : ℂ)
    (hs : s ∈ S) (k : Nat) :
    (∏ j ∈ Finset.range k, (s + (j : ℂ))) ∈ risingCBox c S k := by
  sorry

/-- closed-form term membership (mirror `mem_pfqTermIval`). -/
theorem mem_cpfqTermBox (c : Ctx) (hc : c.Valid)
    (a b : ℕ → ℂ) (A B : List CBox) (p q : Nat) (Z : CBox) (z : ℂ) (k : Nat)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i CBox.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i CBox.top)
    (hmZ : z ∈ Z) :
    cpfqTerm p q a b z k ∈ cpfqTermBox c A B p q Z k := by
  sorry

/-- terminating-top exact identity (mirror `pfqTerm_exact`). -/
theorem cpfqTerm_exact (p q : Nat) (a b : ℕ → ℂ) (z : ℂ) (m : Nat) (i₀ : Nat)
    (hi₀ : i₀ < p) (hterm : a i₀ = -(m : ℂ)) :
    cpfqComplex p q a b z
      = (Finset.range (m + 1)).sum (fun k => cpfqTerm p q a b z k) := by
  sorry

/-- finite-prefix soundness (mirror `pfqFinite_sound`). -/
theorem cpfqFinite_sound (c : Ctx) (hc : c.Valid)
    (p q : Nat) (a b : ℕ → ℂ) (A B : List CBox) (Z : CBox) (z : ℂ)
    (m : Nat) (i₀ : Nat)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i CBox.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i CBox.top)
    (hmZ : z ∈ Z)
    (hi₀ : i₀ < p) (hterm : a i₀ = -(m : ℂ)) :
    cpfqComplex p q a b z ∈ cpfqFiniteBox c A B p q Z m := by
  sorry

/-- disc membership from a norm bound. -/
theorem mem_cpfqDisc (c : Ctx) {z : ℂ} {h : Dy} (hle : ‖z‖ ≤ ((h.toRat : ℚ) : ℝ)) :
    z ∈ (⟨Ival.ofRats c.prec (-h.toRat) h.toRat,
      Ival.ofRats c.prec (-h.toRat) h.toRat⟩ : CBox) := by
  sorry

/-- norm tail bound (mirror `pfqTail_corrected_succ`; the abstract
`summable + ‖·‖ ≤` step is `Complex_geometric_tail`). -/
theorem cpfqTail_bound (p q : Nat) (a b : ℕ → ℂ) (z : ℂ) (n : Nat)
    (hpq : p ≤ q + 1)
    (hBne : ∀ j : Nat, j < q → ∀ m : ℕ, (b j + (m : ℂ)) ≠ 0)
    (hR : cpfqRatio p q a b ‖z‖ n < 1) :
    ‖cpfqComplex p q a b z
      - (Finset.range (n + 1)).sum (fun j => cpfqTerm p q a b z j)‖
      ≤ ‖cpfqTerm p q a b z n‖
        * (cpfqRatio p q a b ‖z‖ n / (1 - cpfqRatio p q a b ‖z‖ n)) := by
  sorry

/-- core soundness (mirror `pfqCore_sound`). -/
theorem cpfqCore_sound (c : Ctx) (hc : c.Valid)
    (p q : Nat) (a b : ℕ → ℂ) (A B : List CBox) (Z : CBox) (z : ℂ) (n : Nat)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i CBox.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i CBox.top)
    (hmZ : z ∈ Z) :
    cpfqComplex p q a b z ∈ cpfqCoreBox c A B Z n := by
  sorry
/-! ### 2F1/1F1 transform drivers (FLINT `2f1_choose` + Kummer).

Pfaff and Kummer need no Gamma factors, so they compose the existing
cores (`pfqCoreIval` / `cpfqCoreBox`, `rpowIval`, `expIval`, cpow-style
boxes). Heavier connection formulas (2F1 terms 2–5) and the `z ≈ 1` corner
stay on the direct path (top on failure) — see `/tmp/hyperc`.
* Pfaff: `2F1(a;b;c;z) = (1-z)^{-a} · 2F1(a,c-b;c;z/(z-1))`, used when the
  direct series does not terminate and `|z/(z-1)| < |z|` at midpoints with
  the box strictly left of the cut (mirrors FLINT's `mag[1] < mag[0]` pick).
* Kummer: `1F1(a;b;z) = e^z · 1F1(b-a;b;-z)`, used when the direct series
  does not terminate but the transformed one does (`b - a = -m`, `m ≤ n`).
Both fire only when the direct engine would not close exactly, so existing
passing tests keep their paths unless the transform strictly applies.
Soundness is `sorry`'d (identities + assembly in `/tmp/hyperc`). -/

/-- midpoint squared modulus of a real interval (`none` if unbounded). -/
def ivalMidSq (X : Ival) : Option ℚ :=
  match X.lo, X.hi with
  | some lo, some hi =>
    let m := (lo.toRat + hi.toRat) / 2
    some (m * m)
  | _, _ => none

/-- Pfaff-transformed problem, when the direct 2F1 does not terminate and
`|z/(z-1)| < |z|` with the box left of the cut. -/
def pfqPfaffArgs (c : Ctx) (A B : List Ival) (Z : Ival) :
    Option (List Ival × List Ival × Ival × Ival) :=
  match A, B with
  | [A0, A1], [B0] =>
    match pfqFindTerm [A0, A1] 0, ivalMidSq Z, Z.hi with
    | none, some mz, some zhi =>
      let W := Ival.div c.prec Z (Ival.sub c.prec Z (Ival.ofRat c.prec 1))
      match ivalMidSq W with
      | some mw =>
        if mw < mz ∧ zhi.toRat < 1 then
          let P := rpowIval c (Ival.sub c.prec (Ival.ofRat c.prec 1) Z)
            (Ival.neg A0)
          some ([A0, Ival.sub c.prec B0 A1], [B0], W, P)
        else none
      | none => none
    | _, _, _ => none
  | _, _ => none

/-- Kummer-transformed problem, when the direct 1F1 does not terminate but
the transformed one does (`b - a = -m`, `m ≤ n`). -/
def pfqKummerArgs (c : Ctx) (A B : List Ival) (Z : Ival) (n : Nat) :
    Option (List Ival × List Ival × Ival × Ival) :=
  match A, B with
  | [A0], [B0] =>
    match pfqFindTerm [A0] 0 with
    | some _ => none
    | none =>
      let D := Ival.sub c.prec B0 A0
      match D.lo, D.hi with
      | some lo, some hi =>
        if lo = hi then
          let q := lo.toRat
          if q.den = 1 ∧ q.num ≤ 0 ∧ (-q.num).toNat ≤ n then
            some ([D], [B0], Ival.neg Z, expIval c Z)
          else none
        else none
      | _, _ => none
  | _, _ => none

/-- Pfaff assembly soundness (identity + inner core + prefactor). -/
theorem pfqPfaff_sound (c : Ctx) (hc : c.Valid)
    (A B : List CBox) (Z : CBox) (a b : List ℂ) (z y : ℂ) (n : Nat)
    (Ar Br : List Ival) (Zr : Ival) (A' B' : List Ival) (W P : Ival)
    (hhA : List.Forall₂ (Ty.Mem .cplx) A a)
    (hhB : List.Forall₂ (Ty.Mem .cplx) B b)
    (hhZ : z ∈ Z)
    (hExA : List.Forall₂ (fun B R => CBox.realOfZeroIm B = some R) A Ar)
    (hExB : List.Forall₂ (fun B R => CBox.realOfZeroIm B = some R) B Br)
    (hZr : CBox.realOfZeroIm Z = some Zr)
    (hy : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z)
    (hArgs : pfqPfaffArgs c Ar Br Zr = some (A', B', W, P)) :
    y ∈ (⟨Ival.mul c.prec P (pfqCoreIval c A' B' W n),
      Ival.ofRat c.prec 0⟩ : CBox) := by
  sorry

/-- Kummer assembly soundness (identity + inner core + prefactor). -/
theorem pfqKummer_sound (c : Ctx) (hc : c.Valid)
    (A B : List CBox) (Z : CBox) (a b : List ℂ) (z y : ℂ) (n : Nat)
    (Ar Br : List Ival) (Zr : Ival) (A' B' : List Ival) (W P : Ival)
    (hhA : List.Forall₂ (Ty.Mem .cplx) A a)
    (hhB : List.Forall₂ (Ty.Mem .cplx) B b)
    (hhZ : z ∈ Z)
    (hExA : List.Forall₂ (fun B R => CBox.realOfZeroIm B = some R) A Ar)
    (hExB : List.Forall₂ (fun B R => CBox.realOfZeroIm B = some R) B Br)
    (hZr : CBox.realOfZeroIm Z = some Zr)
    (hy : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z)
    (hArgs : pfqKummerArgs c Ar Br Zr n = some (A', B', W, P)) :
    y ∈ (⟨Ival.mul c.prec P (pfqCoreIval c A' B' W n),
      Ival.ofRat c.prec 0⟩ : CBox) := by
  sorry

/-- Pfaff for real series values (follows `Complex.HGFun_pfaff` via the
ofReal bridge `HGFun_ofReal_eq_pfqReal`). See `/tmp/hyperc`. -/
theorem pfqReal_pfaff (a₀ a₁ b₀ z : ℝ) (hz : z < 1)
    (hb : ∀ m : ℕ, b₀ + m ≠ 0) :
    pfqReal 2 1 (fun i => [a₀, a₁].getD i 0) (fun _ => b₀) z
      = (1 - z) ^ (-a₀) * pfqReal 2 1 (fun i => [a₀, b₀ - a₁].getD i 0)
        (fun _ => b₀) (z / (z - 1)) := by
  sorry

/-- Kummer for real series values (follows `Complex.HGFun_kummer` via the
ofReal bridge). See `/tmp/hyperc`. -/
theorem pfqReal_kummer (a₀ b₀ z : ℝ)
    (hb : ∀ m : ℕ, b₀ + m ≠ 0) :
    pfqReal 1 1 (fun _ => a₀) (fun _ => b₀) z
      = Real.exp z * pfqReal 1 1 (fun _ => b₀ - a₀) (fun _ => b₀) (-z) := by
  sorry

/-! ### Complex transform drivers (same FLINT picks, `CBox` arithmetic).

Mirror of the real drivers above: Pfaff when `|z/(z-1)| < |z|` at box
midpoints with the box left of the cut, Kummer when the direct series does
not terminate but the transformed one does.  Prefactors use the `cpow`
pattern (`exp (log · * ·)`, nonzero-modulus gate) mirroring `cpowC.ev`.
Soundness is `sorry`'d (identities + assembly in `/tmp/hyperc`). -/

/-- midpoint squared modulus of a complex box (`none` if unbounded). -/
def cboxMidSq (B : CBox) : Option ℚ :=
  match B.re.lo, B.re.hi, B.im.lo, B.im.hi with
  | some rlo, some rhi, some ilo, some ihi =>
    let rx := (rlo.toRat + rhi.toRat) / 2
    let ix := (ilo.toRat + ihi.toRat) / 2
    some (rx * rx + ix * ix)
  | _, _, _, _ => none

/-- Pfaff-transformed problem, complex version. -/
def cpfqPfaffArgs (c : Ctx) (A B : List CBox) (Z : CBox) :
    Option (List CBox × List CBox × CBox × CBox) :=
  let one : CBox := ⟨Ival.ofRat c.prec 1, Ival.zero⟩
  match A, B with
  | [A0, A1], [B0] =>
    match cpfqFindTerm [A0, A1] 0, cboxMidSq Z, Z.re.hi with
    | none, some mz, some zhi =>
      let W := CBox.div c.prec Z (CBox.sub c.prec Z one)
      match cboxMidSq W with
      | some mw =>
        if mw < mz ∧ zhi.toRat < 1 then
          let X1 := CBox.sub c.prec one Z
          let P := match (CBox.norm c.prec X1).lo with
            | some lo => if 0 < lo.toRat then
                expBox c (CBox.mul c.prec (logBox c X1) (CBox.neg A0))
              else CBox.top
            | none => CBox.top
          some ([A0, CBox.sub c.prec B0 A1], [B0], W, P)
        else none
      | none => none
    | _, _, _ => none
  | _, _ => none

/-- Kummer-transformed problem, complex version. -/
def cpfqKummerArgs (c : Ctx) (A B : List CBox) (Z : CBox) (n : Nat) :
    Option (List CBox × List CBox × CBox × CBox) :=
  match A, B with
  | [A0], [B0] =>
    match cpfqFindTerm [A0] 0 with
    | some _ => none
    | none =>
      let D := CBox.sub c.prec B0 A0
      match D.re.lo, D.re.hi, D.im.lo, D.im.hi with
      | some rlo, some rhi, some ilo, some ihi =>
        if rlo = rhi ∧ ilo = ihi ∧ ilo.toRat = 0 then
          let q := rlo.toRat
          if q.den = 1 ∧ q.num ≤ 0 ∧ (-q.num).toNat ≤ n then
            some ([D], [B0], CBox.neg Z, expBox c Z)
          else none
        else none
      | _, _, _, _ => none
  | _, _ => none

/-- complex Pfaff assembly soundness (identity + inner core + prefactor). -/
theorem cpfqPfaff_sound (c : Ctx) (hc : c.Valid)
    (A B : List CBox) (Z : CBox) (a b : List ℂ) (z y : ℂ) (n : Nat)
    (A' B' : List CBox) (W P : CBox)
    (hhA : List.Forall₂ (Ty.Mem .cplx) A a)
    (hhB : List.Forall₂ (Ty.Mem .cplx) B b)
    (hhZ : z ∈ Z)
    (hy : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z)
    (hArgs : cpfqPfaffArgs c A B Z = some (A', B', W, P)) :
    y ∈ CBox.mul c.prec P (cpfqCoreBox c A' B' W n) := by
  sorry

/-- complex Kummer assembly soundness (identity + inner core + prefactor). -/
theorem cpfqKummer_sound (c : Ctx) (hc : c.Valid)
    (A B : List CBox) (Z : CBox) (a b : List ℂ) (z y : ℂ) (n : Nat)
    (A' B' : List CBox) (W P : CBox)
    (hhA : List.Forall₂ (Ty.Mem .cplx) A a)
    (hhB : List.Forall₂ (Ty.Mem .cplx) B b)
    (hhZ : z ∈ Z)
    (hy : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z)
    (hArgs : cpfqKummerArgs c A B Z n = some (A', B', W, P)) :
    y ∈ CBox.mul c.prec P (cpfqCoreBox c A' B' W n) := by
  sorry

/-! ### Bridge to Mathlib's `Complex.regularizedHGFun` (ported from
`/tmp/pfq_thm_proof.lean`). -/

end Lynth.Interval.Fns
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

/-- LIST BRIDGE (ported from `/tmp/pfq_thm_proof.lean`): `HGFun` over coerced
lists agrees with `pfqReal` over the list elements.  Consumed by `HGFunL_sound`. -/
theorem HGFun_coe_list_eq_pfqReal (ar br : List ℝ) (zr : ℝ)
    (hb : ∀ j : Nat, j < br.length → ∀ m : ℕ, (br.getD j 0 : ℂ) ≠ -(m : ℂ)) :
    HGFun (↑(ar.map Complex.ofReal) : Multiset ℂ)
      (↑(br.map Complex.ofReal) : Multiset ℂ) (zr : ℂ)
      = ((Lynth.Interval.Fns.pfqReal ar.length br.length
        (fun i => ar.getD i 0) (fun j => br.getD j 0) zr : ℝ) : ℂ) := by
  have hl : ∀ l : List ℝ, (↑(l.map Complex.ofReal) : Multiset ℂ)
      = (Multiset.range l.length).map (fun i => ((l.getD i 0 : ℝ) : ℂ)) := by
    intro l
    rw [Multiset.range, Multiset.map_coe, Multiset.coe_eq_coe]
    apply List.Perm.of_eq
    apply List.ext_getElem (by simp)
    intro n h1 _
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]
  rw [hl ar, hl br]
  exact HGFun_ofReal_eq_pfqReal _ _ _ _ zr hb

/-- BRIDGE (coefficients, complex): at parameters with no bottom
parameter a nonpositive integer, the `k`-th term of the (Γ-normalized)
series `HGFun` is the complex mirror `cpfqTerm`. Mirror
`HGFunCoeff_mul_pow_ofReal` (same Gamma manipulation, over `ℂ`). -/
theorem HGFunCoeff_mul_pow_ofComplex (p q : Nat) (a b : ℕ → ℂ) (z : ℂ) (k : ℕ)
    (hb : ∀ j : Nat, j < q → ∀ m : ℕ, b j ≠ -(m : ℂ)) :
    HGFunCoeff ((Multiset.range p).map a) ((Multiset.range q).map b) k * z ^ k
      = Lynth.Interval.Fns.cpfqTerm p q a b z k := by
  sorry

/-- LIST BRIDGE (complex): `HGFun` over coerced lists agrees with
`cpfqComplex` over the list elements. Consumed by `HGFunL_sound_complex`. -/
theorem HGFun_coe_list_eq_cpfqComplex (ar br : List ℂ) (zr : ℂ)
    (hb : ∀ j : Nat, j < br.length → ∀ m : ℕ, (br.getD j 0) ≠ -(m : ℂ)) :
    Complex.HGFun (↑ar : Multiset ℂ) (↑br : Multiset ℂ) zr
      = Lynth.Interval.Fns.cpfqComplex ar.length br.length
        (fun i => ar.getD i 0) (fun j => br.getD j 0) zr := by
  sorry

/-- Pfaff transformation (DLMF 15.8.1): `2F1(a;b;c;z) = (1-z)^{-a} · 2F1(a,c-b;c;z/(z-1))`,
valid left of the cut. The series version follows by analytic continuation;
see `/tmp/hyperc`. -/
theorem HGFun_pfaff (a b c z : ℂ) (hz : z.re < 1)
    (hb : ∀ m : ℕ, c + m ≠ 0) :
    Complex.HGFun (↑[a, b] : Multiset ℂ) (↑[c] : Multiset ℂ) z
      = (1 - z) ^ (-a) * Complex.HGFun (↑[a, c - b] : Multiset ℂ) (↑[c] : Multiset ℂ)
        (z / (z - 1)) := by
  sorry

/-- Kummer transformation: `1F1(a;b;z) = e^z · 1F1(b-a;b;-z)` (entire).
See `/tmp/hyperc`. -/
theorem HGFun_kummer (a b z : ℂ) (hb : ∀ m : ℕ, b + m ≠ 0) :
    Complex.HGFun (↑[a] : Multiset ℂ) (↑[b] : Multiset ℂ) z
      = Complex.exp z * Complex.HGFun (↑[b - a] : Multiset ℂ) (↑[b] : Multiset ℂ) (-z) := by
  sorry

end Complex
namespace Lynth.Interval.Fns

/-! ### List-based `HGFun` mirror (single registry entry).

Users write `Complex.HGFun` over multisets in goals; the reifier
(`reifyMultisetHGFun?`) normalizes literal spines to lists and targets
`HGFunL` below. The evaluator extracts real parts (imaginary parts must
be exactly zero) and runs the general `pfqCoreIval` core at any lengths. -/

/-- `HGFunL` soundness, genuinely-complex case: all parameters live in
their boxes and the value is enclosed by the complex core. The proof is
`cpfqCore_sound` after the `HGFun_coe_list_eq_cpfqComplex` bridge. -/
theorem HGFunL_sound_complex (c : Ctx) (hc : c.Valid)
    (a b : List ℂ) (z : ℂ) (A B : List CBox) (XZ : CBox) (y : ℂ)
    (hhA : List.Forall₂ (Ty.Mem .cplx) A a)
    (hhB : List.Forall₂ (Ty.Mem .cplx) B b)
    (hhZ : z ∈ XZ)
    (hy : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z) :
    y ∈ cpfqCoreBox c A B XZ (64 + 2 * c.prec) := by
  sorry

/-- list-based `HGFun` mirror (registry vocabulary). -/
noncomputable def HGFunL (a b : List ℂ) (z : ℂ) : ℂ :=
  Complex.HGFun ↑a ↑b z

/-- project real intervals elementwise (`none` on any nonzero imaginary part). -/
def projectReal : List CBox → Option (List Ival)
  | [] => some []
  | B :: Bs =>
    match CBox.realOfZeroIm B with
    | none => none
    | some R =>
      match projectReal Bs with
      | none => none
      | some Rs => some (R :: Rs)

/-- `projectReal` success gives pointwise projection equations. -/
theorem projectReal_some (A : List CBox) (Ar : List Ival)
    (h : projectReal A = some Ar) :
    List.Forall₂ (fun B R => CBox.realOfZeroIm B = some R) A Ar := by
  induction A generalizing Ar with
  | nil =>
    have h2 : ([] : List Ival) = Ar := Option.some_inj.mp (by simpa [projectReal] using h)
    subst h2
    exact List.Forall₂.nil
  | cons B Bs ih =>
    cases hB : CBox.realOfZeroIm B with
    | none => simp [projectReal, hB] at h
    | some R =>
      cases hRs : projectReal Bs with
      | none => simp [projectReal, hB, hRs] at h
      | some Rs =>
        have h2 : R :: Rs = Ar := Option.some_inj.mp (by simpa [projectReal, hB, hRs] using h)
        subst h2
        exact List.Forall₂.cons hB (ih _ hRs)

def HGFunL_ev (c : Ctx) : CEnc [.list .cplx, .list .cplx, .cplx] → CBox
  | .cons _ (some A) (.cons _ (some B) (.cons _ Z .nil)) =>
    match projectReal A, projectReal B, CBox.realOfZeroIm Z with
    | some Ar, some Br, some Zr =>
      match pfqPfaffArgs c Ar Br Zr with
      | some (A', B', W, P) =>
        (⟨Ival.mul c.prec P (pfqCoreIval c A' B' W (64 + 2 * c.prec)),
          Ival.ofRat c.prec 0⟩ : CBox)
      | none =>
        match pfqKummerArgs c Ar Br Zr (64 + 2 * c.prec) with
        | some (A', B', W, P) =>
          (⟨Ival.mul c.prec P (pfqCoreIval c A' B' W (64 + 2 * c.prec)),
            Ival.ofRat c.prec 0⟩ : CBox)
        | none =>
          if pfqGuard Br (64 + 2 * c.prec) then
            (⟨pfqCoreIval c Ar Br Zr (64 + 2 * c.prec), Ival.ofRat c.prec 0⟩ : CBox)
          else CBox.top
    | _, _, _ =>
      match cpfqPfaffArgs c A B Z with
      | some (A', B', W, P) =>
        CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
      | none =>
        match cpfqKummerArgs c A B Z (64 + 2 * c.prec) with
        | some (A', B', W, P) =>
          CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
        | none => cpfqCoreBox c A B Z (64 + 2 * c.prec)
  | _ => CBox.top

theorem HGFunL_sound (c : Ctx) :
    ∀ (vs : CVal [.list .cplx, .list .cplx, .cplx])
      (ds : CDen [.list .cplx, .list .cplx, .cplx]) (y : ℂ)
      (X : CEnc [.list .cplx, .list .cplx, .cplx]) (hc : c.Valid)
      (hg : y = applyCurried [.list .cplx, .list .cplx, .cplx] .cplx HGFunL vs)
      (hh : CEncHolds X ds) (hag : Agree vs ds),
    y ∈ HGFunL_ev c X := by
  intro vs ds y X hc hg hh hag
  match vs, ds, X with
  | .cons _ a (.cons _ b (.cons _ z .nil)),
    .cons _ da (.cons _ db (.cons _ dz .nil)),
    .cons _ XA (.cons _ XB (.cons _ XZ .nil)) =>
    have had : a = da := hag.1
    have hbd : b = db := hag.2.1
    have hzd : z = dz := hag.2.2.1
    subst had
    subst hbd
    subst hzd
    cases hXA : XA with
    | none =>
      show y ∈ CBox.top
      exact CBox.mem_top _
    | some A =>
      subst hXA
      cases hXB : XB with
      | none =>
        show y ∈ CBox.top
        exact CBox.mem_top _
      | some B =>
        subst hXB
        show y ∈ match projectReal A, projectReal B, CBox.realOfZeroIm XZ with
          | some Ar, some Br, some Zr =>
            match pfqPfaffArgs c Ar Br Zr with
            | some (A', B', W, P) =>
              (⟨Ival.mul c.prec P (pfqCoreIval c A' B' W (64 + 2 * c.prec)),
                Ival.ofRat c.prec 0⟩ : CBox)
            | none =>
              match pfqKummerArgs c Ar Br Zr (64 + 2 * c.prec) with
              | some (A', B', W, P) =>
                (⟨Ival.mul c.prec P (pfqCoreIval c A' B' W (64 + 2 * c.prec)),
                  Ival.ofRat c.prec 0⟩ : CBox)
              | none =>
                if pfqGuard Br (64 + 2 * c.prec) then
                  (⟨pfqCoreIval c Ar Br Zr (64 + 2 * c.prec), Ival.ofRat c.prec 0⟩ : CBox)
                else CBox.top
          | _, _, _ =>
            match cpfqPfaffArgs c A B XZ with
            | some (A', B', W, P) =>
              CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
            | none =>
              match cpfqKummerArgs c A B XZ (64 + 2 * c.prec) with
              | some (A', B', W, P) =>
                CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
              | none => cpfqCoreBox c A B XZ (64 + 2 * c.prec)
        cases hAr : projectReal A with
        | none =>
          show y ∈ match cpfqPfaffArgs c A B XZ with
          | some (A', B', W, P) =>
            CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
          | none =>
            match cpfqKummerArgs c A B XZ (64 + 2 * c.prec) with
            | some (A', B', W, P) =>
              CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
            | none => cpfqCoreBox c A B XZ (64 + 2 * c.prec)
          cases hP : cpfqPfaffArgs c A B XZ with
          | some v =>
            obtain ⟨A', B', W, P⟩ := v
            have hhA : List.Forall₂ (Ty.Mem .cplx) A a := hh.1
            have hhB : List.Forall₂ (Ty.Mem .cplx) B b := hh.2.1
            have hhZ : z ∈ XZ := hh.2.2.1
            have hy2 : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := hg
            exact cpfqPfaff_sound c hc A B XZ a b z y (64 + 2 * c.prec) A' B' W P hhA hhB hhZ hy2 hP
          | none =>
            cases hK : cpfqKummerArgs c A B XZ (64 + 2 * c.prec) with
            | some v =>
              obtain ⟨A', B', W, P⟩ := v
              have hhA : List.Forall₂ (Ty.Mem .cplx) A a := hh.1
              have hhB : List.Forall₂ (Ty.Mem .cplx) B b := hh.2.1
              have hhZ : z ∈ XZ := hh.2.2.1
              have hy2 : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := hg
              exact cpfqKummer_sound c hc A B XZ a b z y (64 + 2 * c.prec) A' B' W P hhA hhB hhZ hy2 hK
            | none =>
              have hhA : List.Forall₂ (Ty.Mem .cplx) A a := hh.1
              have hhB : List.Forall₂ (Ty.Mem .cplx) B b := hh.2.1
              have hhZ : z ∈ XZ := hh.2.2.1
              have hy2 : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := hg
              exact HGFunL_sound_complex c hc a b z A B XZ y hhA hhB hhZ hy2
        | some Ar =>
          cases hBr : projectReal B with
          | none =>
            show y ∈ match cpfqPfaffArgs c A B XZ with
            | some (A', B', W, P) =>
              CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
            | none =>
              match cpfqKummerArgs c A B XZ (64 + 2 * c.prec) with
              | some (A', B', W, P) =>
                CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
              | none => cpfqCoreBox c A B XZ (64 + 2 * c.prec)
            cases hP : cpfqPfaffArgs c A B XZ with
            | some v =>
              obtain ⟨A', B', W, P⟩ := v
              have hhA : List.Forall₂ (Ty.Mem .cplx) A a := hh.1
              have hhB : List.Forall₂ (Ty.Mem .cplx) B b := hh.2.1
              have hhZ : z ∈ XZ := hh.2.2.1
              have hy2 : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := hg
              exact cpfqPfaff_sound c hc A B XZ a b z y (64 + 2 * c.prec) A' B' W P hhA hhB hhZ hy2 hP
            | none =>
              cases hK : cpfqKummerArgs c A B XZ (64 + 2 * c.prec) with
              | some v =>
                obtain ⟨A', B', W, P⟩ := v
                have hhA : List.Forall₂ (Ty.Mem .cplx) A a := hh.1
                have hhB : List.Forall₂ (Ty.Mem .cplx) B b := hh.2.1
                have hhZ : z ∈ XZ := hh.2.2.1
                have hy2 : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := hg
                exact cpfqKummer_sound c hc A B XZ a b z y (64 + 2 * c.prec) A' B' W P hhA hhB hhZ hy2 hK
              | none =>
                have hhA : List.Forall₂ (Ty.Mem .cplx) A a := hh.1
                have hhB : List.Forall₂ (Ty.Mem .cplx) B b := hh.2.1
                have hhZ : z ∈ XZ := hh.2.2.1
                have hy2 : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := hg
                exact HGFunL_sound_complex c hc a b z A B XZ y hhA hhB hhZ hy2
          | some Br =>
            cases hZr : CBox.realOfZeroIm XZ with
            | none =>
              show y ∈ match cpfqPfaffArgs c A B XZ with
              | some (A', B', W, P) =>
                CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
              | none =>
                match cpfqKummerArgs c A B XZ (64 + 2 * c.prec) with
                | some (A', B', W, P) =>
                  CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
                | none => cpfqCoreBox c A B XZ (64 + 2 * c.prec)
              cases hP : cpfqPfaffArgs c A B XZ with
              | some v =>
                obtain ⟨A', B', W, P⟩ := v
                have hhA : List.Forall₂ (Ty.Mem .cplx) A a := hh.1
                have hhB : List.Forall₂ (Ty.Mem .cplx) B b := hh.2.1
                have hhZ : z ∈ XZ := hh.2.2.1
                have hy2 : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := hg
                exact cpfqPfaff_sound c hc A B XZ a b z y (64 + 2 * c.prec) A' B' W P hhA hhB hhZ hy2 hP
              | none =>
                cases hK : cpfqKummerArgs c A B XZ (64 + 2 * c.prec) with
                | some v =>
                  obtain ⟨A', B', W, P⟩ := v
                  have hhA : List.Forall₂ (Ty.Mem .cplx) A a := hh.1
                  have hhB : List.Forall₂ (Ty.Mem .cplx) B b := hh.2.1
                  have hhZ : z ∈ XZ := hh.2.2.1
                  have hy2 : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := hg
                  exact cpfqKummer_sound c hc A B XZ a b z y (64 + 2 * c.prec) A' B' W P hhA hhB hhZ hy2 hK
                | none =>
                  have hhA : List.Forall₂ (Ty.Mem .cplx) A a := hh.1
                  have hhB : List.Forall₂ (Ty.Mem .cplx) B b := hh.2.1
                  have hhZ : z ∈ XZ := hh.2.2.1
                  have hy2 : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := hg
                  exact HGFunL_sound_complex c hc a b z A B XZ y hhA hhB hhZ hy2
            | some Zr =>
              show y ∈ match pfqPfaffArgs c Ar Br Zr with
              | some (A', B', W, P) =>
                (⟨Ival.mul c.prec P (pfqCoreIval c A' B' W (64 + 2 * c.prec)),
                  Ival.ofRat c.prec 0⟩ : CBox)
              | none =>
                match pfqKummerArgs c Ar Br Zr (64 + 2 * c.prec) with
                | some (A', B', W, P) =>
                  (⟨Ival.mul c.prec P (pfqCoreIval c A' B' W (64 + 2 * c.prec)),
                    Ival.ofRat c.prec 0⟩ : CBox)
                | none =>
                  if pfqGuard Br (64 + 2 * c.prec) then
                    (⟨pfqCoreIval c Ar Br Zr (64 + 2 * c.prec), Ival.ofRat c.prec 0⟩ : CBox)
                    else CBox.top
              cases hP : pfqPfaffArgs c Ar Br Zr with
              | some v =>
                obtain ⟨A', B', W, P⟩ := v
                have hhA : List.Forall₂ (Ty.Mem .cplx) A a := hh.1
                have hhB : List.Forall₂ (Ty.Mem .cplx) B b := hh.2.1
                have hhZ : z ∈ XZ := hh.2.2.1
                have hExA := projectReal_some A Ar hAr
                have hExB := projectReal_some B Br hBr
                have hy2 : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := hg
                exact pfqPfaff_sound c hc A B XZ a b z y (64 + 2 * c.prec) Ar Br Zr A' B' W P hhA hhB hhZ hExA hExB hZr hy2 hP
              | none =>
                cases hK : pfqKummerArgs c Ar Br Zr (64 + 2 * c.prec) with
                | some v =>
                  obtain ⟨A', B', W, P⟩ := v
                  have hhA : List.Forall₂ (Ty.Mem .cplx) A a := hh.1
                  have hhB : List.Forall₂ (Ty.Mem .cplx) B b := hh.2.1
                  have hhZ : z ∈ XZ := hh.2.2.1
                  have hExA := projectReal_some A Ar hAr
                  have hExB := projectReal_some B Br hBr
                  have hy2 : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := hg
                  exact pfqKummer_sound c hc A B XZ a b z y (64 + 2 * c.prec) Ar Br Zr A' B' W P hhA hhB hhZ hExA hExB hZr hy2 hK
                | none =>
                  show y ∈ (if pfqGuard Br (64 + 2 * c.prec) then
                    (⟨pfqCoreIval c Ar Br Zr (64 + 2 * c.prec), Ival.ofRat c.prec 0⟩ : CBox)
                    else CBox.top)
                  cases hguard : pfqGuard Br (64 + 2 * c.prec) with
                  | false =>
                    show y ∈ CBox.top
                    exact CBox.mem_top _
                  | true =>
                    -- extraction to real parameters
                    have hExA := projectReal_some A Ar hAr
                    have hExB := projectReal_some B Br hBr
                    have hhA : List.Forall₂ (Ty.Mem .cplx) A a := hh.1
                    have hhB : List.Forall₂ (Ty.Mem .cplx) B b := hh.2.1
                    have hhZ : z ∈ XZ := hh.2.2.1
                    obtain ⟨hArLen, haLen, hmemA⟩ :=
                      extract_real_params A Ar a a rfl hhA hExA
                    obtain ⟨hBrLen, hbLen, hmemB⟩ :=
                      extract_real_params B Br b b rfl hhB hExB
                    have hre_z : z.re ∈ Zr := (realOfZeroIm_ok XZ Zr z hZr hhZ).1
                    have him_z : z.im = 0 := (realOfZeroIm_ok XZ Zr z hZr hhZ).2
                    -- denoted value via the bridge
                    have hy2 : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := hg
                    have hgetA : ∀ i : Nat, ((a.map Complex.re).getD i 0) = (a.getD i 0).re := by
                      intro i
                      have h := List.getD_map (l := a) (d := (0 : ℂ)) (n := i) (f := Complex.re)
                      simpa [Complex.zero_re] using h
                    have hgetB : ∀ i : Nat, ((b.map Complex.re).getD i 0) = (b.getD i 0).re := by
                      intro i
                      have h := List.getD_map (l := b) (d := (0 : ℂ)) (n := i) (f := Complex.re)
                      simpa [Complex.zero_re] using h
                    have hmap_a : ((a.map Complex.re).map Complex.ofReal) = a := by
                      rw [List.map_map]
                      apply List.ext_getElem (by simp)
                      intro i h1 h2
                      have e1 := List.getElem_map (f := Complex.ofReal ∘ Complex.re)
                        (l := a) (i := i) (h := h1)
                      rw [e1]
                      have hiA : i < A.length := by omega
                      have h2' := (hmemA i hiA).2
                      rw [getD_of_lt a 0 i h2] at h2'
                      -- goal: Complex.ofReal ((a[i]).re) = a[i]
                      exact ofReal_of_re h2'
                    have hmap_b : ((b.map Complex.re).map Complex.ofReal) = b := by
                      rw [List.map_map]
                      apply List.ext_getElem (by simp)
                      intro i h1 h2
                      have e1 := List.getElem_map (f := Complex.ofReal ∘ Complex.re)
                        (l := b) (i := i) (h := h1)
                      rw [e1]
                      have hiB : i < B.length := by omega
                      have h2' := (hmemB i hiB).2
                      rw [getD_of_lt b 0 i h2] at h2'
                      exact ofReal_of_re h2'
                    have hz_eq : ((z.re : ℝ) : ℂ) = z := ofReal_of_re him_z
                    -- bridge hypothesis from the guard
                    have hmemBr : ∀ i : Nat, i < Br.length → (b.getD i 0).re ∈ Br.getD i Ival.top :=
                      fun i hi => (hmemB i (by omega)).1
                    have hmB' : ∀ i : Nat, i < Br.length →
                        (fun j => (b.getD j 0).re) (0 + i) ∈ Br.getD i Ival.top := by
                      intro i hi
                      simpa using hmemBr i hi
                    have hG := pfqGuard_ok (fun j => (b.getD j 0).re) Br 0
                      (64 + 2 * c.prec) hmB' hguard
                    obtain ⟨hpos, hne⟩ := hG
                    have hb_br : ∀ j : Nat, j < (b.map Complex.re).length → ∀ m : ℕ,
                        ((((b.map Complex.re).getD j 0 : ℝ)) : ℂ) ≠ -(m : ℂ) := by
                      intro j hj m
                      have hj' : j < Br.length := by
                        have e : (b.map Complex.re).length = Br.length := by
                          rw [List.length_map]; omega
                        omega
                      rw [hgetB j]
                      exact hb_of_guard (fun k => (b.getD k 0).re) Br.length
                        (64 + 2 * c.prec)
                        (fun k hk => by
                          have h2 := hpos k hk
                          rw [Nat.zero_add] at h2
                          linarith)
                        (fun k hk t ht => by
                          have h2 := hne k hk t ht
                          rwa [Nat.zero_add] at h2)
                        j hj' m
                    have hbridge := Complex.HGFun_coe_list_eq_pfqReal
                      (a.map Complex.re) (b.map Complex.re) (z.re) hb_br
                    rw [← hmap_a, ← hmap_b, ← hz_eq] at hy2
                    rw [hbridge] at hy2
                    -- hy2 : y = ↑(pfqReal ..); core gives the real enclosure
                    have harlen : (a.map Complex.re).length = Ar.length := by
                      rw [List.length_map]; omega
                    have hbrlen : (b.map Complex.re).length = Br.length := by
                      rw [List.length_map]; omega
                    have hafun : (fun i => (a.getD i 0).re)
                        = fun i => ((a.map Complex.re).getD i 0) :=
                      funext fun i => (hgetA i).symm
                    have hbfun : (fun j => (b.getD j 0).re)
                        = fun j => ((b.map Complex.re).getD j 0) :=
                      funext fun j => (hgetB j).symm
                    have hcore : pfqReal Ar.length Br.length
                        (fun i => (a.getD i 0).re) (fun j => (b.getD j 0).re) (z.re)
                        ∈ pfqCoreIval c Ar Br Zr (64 + 2 * c.prec) :=
                      pfqCore_sound c hc _ _ _ _ Ar Br Zr _ (64 + 2 * c.prec) rfl rfl
                        (fun i hi => (hmemA i (by omega)).1)
                        (fun i hi => (hmemB i (by omega)).1)
                        hre_z
                    rw [hafun, hbfun, ← harlen, ← hbrlen] at hcore
                    have hP : pfqReal (a.map Complex.re).length (b.map Complex.re).length
                        (fun i => ((a.map Complex.re).getD i 0))
                        (fun j => ((b.map Complex.re).getD j 0)) (z.re) = y.re := by
                      rw [hy2]
                      exact (Complex.ofReal_re _).symm
                    rw [hP] at hcore
                    have hyim : y.im ∈ Ival.ofRat c.prec 0 := by
                      have e : y.im = 0 := by
                        rw [hy2]
                        exact Complex.ofReal_im _
                      rw [e]
                      exact_mod_cast Ival.mem_ofRat c.prec (0 : ℚ)
                    exact CBox.mem_def.mpr ⟨hcore, hyim⟩

@[lynth_cfn] def HGFunLR : CFn [.list .cplx, .list .cplx, .cplx] .cplx :=
  { name := "HGFun",
    fn := fun _ _ _ => (0 : ℂ),
    graph := CFn.graphOf [.list .cplx, .list .cplx, .cplx] .cplx HGFunL,
    exu := CFn.exuOf (tys := [.list .cplx, .list .cplx, .cplx]) .cplx HGFunL,
    ev := HGFunL_ev,
    sound := HGFunL_sound,
    cost := 1500 }


end Lynth.Interval.Fns
