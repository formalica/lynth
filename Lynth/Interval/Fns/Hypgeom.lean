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
heartbeats). Soundness is proved in place layer by layer (each lemma
mirrors its proved real counterpart); still-`sorry`'d parts are handed
off in `/tmp/hyperc` (each docstring names the mirror to follow).
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
def cpfqPairBox (c : Ctx) (Ai Bi : CBox) (Di : Ival) : Ival :=
  Ival.add c.prec
    (Ival.div c.prec (CBox.norm c.prec (CBox.sub c.prec Ai Bi)) Di)
    (Ival.ofRat c.prec 1)

/-- `R` denominator extras over `j ∈ [p, q)`, fuel-indexed. -/
def cpfqRDenAux (c : Ctx) (B : List CBox) (n : Nat) : Nat → Nat → List Ival
  | _, 0 => []
  | p, f + 1 => cpfqRDenAux c B n p f
    ++ [CBox.norm c.prec (CBox.add c.prec (B.getD (p + f) CBox.top) (cNatBox c n))]

/-- full `R` norm-ratio bound (mirrors `pfqRatio`, same `if`). -/
def cpfqRBox (c : Ctx) (A B : List CBox) (p q : Nat) (Zabs : Ival)
    (aq : Ival) (n : Nat) : Ival :=
  let base := Ival.div c.prec
    (Ival.mul c.prec Zabs (iprod c ((List.range (min p q)).map fun i =>
      cpfqPairBox c (A.getD i CBox.top) (B.getD i CBox.top)
        (CBox.norm c.prec (CBox.add c.prec (B.getD i CBox.top) (cNatBox c n))))))
    (Ival.mul c.prec
      (iprod c (cpfqRDenAux c B n p (q - p)))
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
      let R := cpfqRBox c A B A.length B.length (CBox.norm c.prec Z)
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
  simp only [cpfqTerm, Finset.prod_range_succ, Finset.prod_mul_distrib, Nat.factorial_succ,
    Nat.cast_mul, pow_succ]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- product-box membership (mirror `mem_iprod`). -/
theorem mem_cprod (c : Ctx) (hc : c.Valid) (L : List CBox) (v : List ℂ)
    (h : List.Forall₂ (fun z B => z ∈ B) v L) :
    v.prod ∈ cprod c L := by
  induction h with
  | nil =>
    simp only [cprod, List.prod_nil]
    exact ⟨by rw [Complex.one_re]; exact Ival.mem_one,
      by rw [Complex.one_im]; exact Ival.mem_zero⟩
  | cons hx _ ih =>
    simp only [cprod, List.prod_cons]
    exact CBox.mem_mul hx (ih)

/-- sum-box membership (mirror `mem_isum`). -/
theorem mem_csum (c : Ctx) (hc : c.Valid) (L : List CBox) (v : List ℂ)
    (h : List.Forall₂ (fun z B => z ∈ B) v L) :
    v.sum ∈ csum c L := by
  induction h with
  | nil =>
    simp only [csum, List.sum_nil]
    exact ⟨by rw [Complex.zero_re]; exact Ival.mem_zero,
      by rw [Complex.zero_im]; exact Ival.mem_zero⟩
  | cons hx _ ih =>
    simp only [csum, List.sum_cons]
    exact CBox.mem_add hx (ih)

/-- nat-cast box membership. -/
theorem mem_cNatBox (c : Ctx) (k : Nat) : ((k : ℕ) : ℂ) ∈ cNatBox c k := by
  refine ⟨?_, ?_⟩
  · rw [Complex.natCast_re]; exact_mod_cast Ival.mem_ofRat c.prec (k : ℚ)
  · rw [Complex.natCast_im]; exact Ival.mem_zero

/-- range-mapped shifted-factor memberships (mirror `pfqAddForall₂`). -/
theorem cpfqAddForall₂ (c : Ctx) (L : List CBox) (v : ℕ → ℂ) (k : Nat)
    (hm : ∀ i : Nat, i < L.length → v i ∈ L.getD i CBox.top) :
    List.Forall₂ (fun z B => z ∈ B)
      ((List.range L.length).map fun i => v i + (k : ℂ))
      ((List.range L.length).map fun i =>
        CBox.add c.prec (L.getD i CBox.top) (cNatBox c k)) := by
  have h : ∀ m : Nat, m ≤ L.length → List.Forall₂ (fun z B => z ∈ B)
      ((List.range m).map fun (i : Nat) => v i + (k : ℂ))
      ((List.range m).map fun (i : Nat) =>
        CBox.add c.prec (L.getD i CBox.top) (cNatBox c k)) := by
    intro m
    induction m with
    | zero => intro _; exact List.Forall₂.nil
    | succ m ih =>
      intro hmle
      rw [List.range_succ, List.map_append, List.map_append]
      refine List.rel_append (ih (by omega)) ?_
      refine List.Forall₂.cons ?_ List.Forall₂.nil
      have hvm := hm m (by omega)
      exact CBox.mem_add hvm (mem_cNatBox c k)
  exact h L.length le_rfl

/-- list product over a mapped range is the finset product (complex mirror
of `list_prod_map_range`). -/
theorem list_prod_map_rangeC (f : Nat → ℂ) : ∀ N : Nat,
    ((List.range N).map f).prod = (Finset.range N).prod fun k => f k
  | 0 => by simp
  | N + 1 => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one,
      Finset.prod_range_succ]
    rw [list_prod_map_rangeC f N]

/-- list sum over a mapped range is the finset sum (complex mirror
of the real `list_sum_map_range`). -/
theorem list_sum_map_rangeC (f : Nat → ℂ) : ∀ N : Nat,
    ((List.range N).map f).sum = (Finset.range N).sum fun k => f k
  | 0 => by simp
  | N + 1 => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero,
      Finset.sum_range_succ]
    rw [list_sum_map_rangeC f N]

/-- step membership (mirror `mem_pfqStep`). -/
theorem mem_cpfqStep (c : Ctx) (hc : c.Valid)
    (a b : ℕ → ℂ) (A B : List CBox) (Z : CBox) (z : ℂ) (k : Nat)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i CBox.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i CBox.top)
    (hmZ : z ∈ Z) (T : CBox) (Tk : ℂ) (hT : Tk ∈ T) :
    Tk * ((∏ i ∈ Finset.range A.length, (a i + (k : ℂ)))
      / (∏ j ∈ Finset.range B.length, (b j + (k : ℂ))) * z / ((k : ℂ) + 1))
      ∈ cpfqStepBox c A B A.length B.length Z T k := by
  have hnum := mem_cprod c hc _ _ (cpfqAddForall₂ c A a k hmA)
  rw [list_prod_map_rangeC] at hnum
  have hden := mem_cprod c hc _ _ (cpfqAddForall₂ c B b k hmB)
  rw [list_prod_map_rangeC] at hden
  have hk1C : ((k + 1 : Nat) : ℂ) ∈ cNatBox c (k + 1) := mem_cNatBox c (k + 1)
  have hval : Tk * ((∏ i ∈ Finset.range A.length, (a i + (k : ℂ)))
      / (∏ j ∈ Finset.range B.length, (b j + (k : ℂ))) * z / ((k : ℂ) + 1))
      = ((Tk * (Finset.range A.length).prod (fun i => a i + (k : ℂ))) * z)
        / ((Finset.range B.length).prod (fun j => b j + (k : ℂ))
          * ((k + 1 : Nat) : ℂ)) := by
    have e : (((k + 1 : Nat)) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
    rw [e]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hval]
  simp only [cpfqStepBox]
  exact CBox.mem_div (CBox.mem_mul (CBox.mem_mul hT hnum) hmZ)
    (CBox.mem_mul hden hk1C)

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
  intro f
  induction f with
  | zero =>
    intro k hkn S T Sr Tr hS hT hSeq hTeq
    simp only [cpfqLoop, Nat.add_zero]
    constructor
    · rw [← hSeq]; exact hS
    · rw [← hTeq]; exact hT
  | succ f ih =>
    intro k hkn S T Sr Tr hS hT hSeq hTeq
    show ((Finset.range (k + (f + 1))).sum _
        ∈ (cpfqLoop c A B A.length B.length Z f (k + 1)
          (CBox.add c.prec S T)
          (cpfqStepBox c A B A.length B.length Z T k)).1
      ∧ cpfqTerm A.length B.length a b z (k + (f + 1))
        ∈ (cpfqLoop c A B A.length B.length Z f (k + 1)
          (CBox.add c.prec S T)
          (cpfqStepBox c A B A.length B.length Z T k)).2)
    have hST : Sr + Tr ∈ CBox.add c.prec S T := CBox.mem_add hS hT
    have hTk1 : Tr
        * ((∏ i ∈ Finset.range A.length, (a i + (k : ℂ)))
          / (∏ j ∈ Finset.range B.length, (b j + (k : ℂ))) * z / ((k : ℂ) + 1))
        ∈ cpfqStepBox c A B A.length B.length Z T k :=
      mem_cpfqStep c hc a b A B Z z k hmA hmB hmZ T Tr hT
    have hTeq1 : Tr
        * ((∏ i ∈ Finset.range A.length, (a i + (k : ℂ)))
          / (∏ j ∈ Finset.range B.length, (b j + (k : ℂ))) * z / ((k : ℂ) + 1))
        = cpfqTerm A.length B.length a b z (k + 1) := by
      rw [hTeq]
      exact (cpfqTerm_succ A.length B.length a b z k
        (fun j hj => hBne j hj k (by omega))).symm
    rw [hTeq1] at hTk1
    have hSeq1 : Sr + Tr
        = (Finset.range (k + 1)).sum (fun j => cpfqTerm A.length B.length a b z j) := by
      rw [Finset.sum_range_succ, hSeq, hTeq]
    have e1 : k + (f + 1) = k + 1 + f := by omega
    rw [e1]
    exact ih (k + 1) (by omega) _ _ _ _ hST hTk1 hSeq1 rfl

/-- where `cpfqRatio` is the uniform later-term norm ratio
(`‖T_{k+1}‖/‖T_k‖ ≤ R` for `k ≥ n`), mirroring `pfqRatio`. -/
noncomputable def cpfqRatio (p q : Nat) (a b : ℕ → ℂ) (Z : ℝ) (n : Nat) : ℝ :=
  Z * (∏ i ∈ Finset.range (min p q), (‖a i - b i‖ / ‖b i + (n : ℂ)‖ + 1))
    / ((∏ j ∈ Finset.Ico p q, ‖b j + (n : ℂ)‖) * ((n : ℝ) + 1))
    * (if p = q + 1 then (‖a q‖ + (n : ℝ) + 1) else 1)

/-- extras norm equation (fuel induction to `Ico`). -/
theorem cpfqRDenAux_eq (b : ℕ → ℂ) (p f n : Nat) :
    ((List.range f).map fun t => ‖b (p + t) + (n : ℂ)‖).prod
      = ∏ j ∈ Finset.Ico p (p + f), ‖b j + (n : ℂ)‖ := by
  induction f with
  | zero => simp
  | succ f ih =>
    have h1 : p + (f + 1) = (p + f) + 1 := by omega
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, h1]
    rw [Finset.prod_Ico_succ_top (by omega : p ≤ p + f), ih]

/-- extras interval membership (fuel induction). -/
theorem cpfqRDenForall₂ (c : Ctx) (B : List CBox) (b : ℕ → ℂ) (n p : Nat)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i CBox.top) :
    ∀ f : Nat, (∀ t : Nat, t < f → p + t < B.length) → List.Forall₂ (fun x I => x ∈ I)
      ((List.range f).map fun t => ‖b (p + t) + (n : ℂ)‖)
      (cpfqRDenAux c B n p f) := by
  intro f
  induction f with
  | zero => intro _; exact List.Forall₂.nil
  | succ f ih =>
    intro hle
    rw [List.range_succ, List.map_append]
    show List.Forall₂ (fun x I => x ∈ I) _
      (cpfqRDenAux c B n p f
        ++ [CBox.norm c.prec (CBox.add c.prec (B.getD (p + f) CBox.top) (cNatBox c n))])
    refine List.rel_append (ih (fun t ht => hle t (by omega))) ?_
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    have hmem : b (p + f) ∈ B.getD (p + f) CBox.top := hmB (p + f) (hle f (Nat.lt_succ_self f))
    exact CBox.mem_norm (CBox.mem_add hmem (mem_cNatBox c n))

/-- paired-factor membership (range induction). -/
theorem cpfqPairForall₂ (c : Ctx) (A B : List CBox) (a b : ℕ → ℂ) (n : Nat)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i CBox.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i CBox.top) :
    ∀ m : Nat, m ≤ min A.length B.length → List.Forall₂ (fun x I => x ∈ I)
      ((List.range m).map fun (i : Nat) => ‖a i - b i‖ / ‖b i + (n : ℂ)‖ + 1)
      ((List.range m).map fun (i : Nat) =>
        cpfqPairBox c (A.getD i CBox.top) (B.getD i CBox.top)
          (CBox.norm c.prec (CBox.add c.prec (B.getD i CBox.top) (cNatBox c n)))) := by
  intro m
  induction m with
  | zero => intro _; exact List.Forall₂.nil
  | succ m ih =>
    intro hmle
    rw [List.range_succ, List.map_append, List.map_append]
    refine List.rel_append (ih (by omega)) ?_
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    have haM : a m ∈ A.getD m CBox.top := hmA m (by omega)
    have hbM : b m ∈ B.getD m CBox.top := hmB m (by omega)
    have hD : ‖b m + (n : ℂ)‖ ∈ CBox.norm c.prec
        (CBox.add c.prec (B.getD m CBox.top) (cNatBox c n)) :=
      CBox.mem_norm (CBox.mem_add hbM (mem_cNatBox c n))
    unfold cpfqPairBox
    exact Ival.mem_add (Ival.mem_div (CBox.mem_norm (CBox.mem_sub haM hbM)) hD)
      (by exact_mod_cast Ival.mem_ofRat c.prec (1 : ℚ))

/-- denominator extras over `[p, p + (q-p))` agree with `[p, q)` (`p ≤ q+1`). -/
theorem cpfqExtras_eq (p q : Nat) (hpq : p ≤ q + 1) (b : ℕ → ℂ) (n : Nat) :
    ∏ j ∈ Finset.Ico p (p + (q - p)), ‖b j + (n : ℂ)‖
      = ∏ j ∈ Finset.Ico p q, ‖b j + (n : ℂ)‖ := by
  by_cases h : p = q + 1
  · subst h
    have e0 : q - (q + 1) = 0 := by omega
    rw [e0, add_zero, Finset.Ico_eq_empty_of_le (le_refl (q + 1)),
      Finset.Ico_eq_empty_of_le (show q ≤ q + 1 by omega)]
  · have hle : p ≤ q := by omega
    rw [Nat.add_sub_cancel' hle]

/-- ratio-bound membership (mirror `mem_pfqRIval`; per-factor steps use
`CBox.mem_norm`, `Ival.mem_div/abs/sub` and the paired estimate
`‖a+k‖/‖b+k‖ ≤ ‖a-b‖/‖b+n‖ + 1` for `k ≥ n`). -/
theorem mem_cpfqR (c : Ctx) (hc : c.Valid)
    (a b : ℕ → ℂ) (A B : List CBox) (p q : Nat)
    (Z : CBox) (z : ℂ) (n : Nat)
    (hlenA : A.length = p) (hlenB : B.length = q)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i CBox.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i CBox.top)
    (hmZ : z ∈ Z)
    (hpq : p ≤ q + 1) :
    cpfqRatio p q a b ‖z‖ n ∈ cpfqRBox c A B p q
      (CBox.norm c.prec Z) (CBox.norm c.prec (A.getD q CBox.top)) n := by
  have hZabs : ‖z‖ ∈ CBox.norm c.prec Z := CBox.mem_norm hmZ
  have hN := mem_iprod c hc _ _
    (cpfqPairForall₂ c A B a b n hmA hmB (min p q) (by omega))
  rw [list_prod_map_range] at hN
  have hD := mem_iprod c hc _ _
    (cpfqRDenForall₂ c B b n p hmB (q - p) (fun t ht => by omega))
  rw [cpfqRDenAux_eq, cpfqExtras_eq p q hpq b n] at hD
  have hN1 : ((n : ℝ) + 1) ∈ Ival.ofRat c.prec (((n : Nat) : ℚ) + 1) := by
    exact_mod_cast Ival.mem_ofRat c.prec (((n : Nat) : ℚ) + 1)
  have hDen : (∏ j ∈ Finset.Ico p q, ‖b j + (n : ℂ)‖) * ((n : ℝ) + 1)
      ∈ Ival.mul c.prec (iprod c (cpfqRDenAux c B n p (q - p)))
        (Ival.ofRat c.prec (((n : Nat) : ℚ) + 1)) :=
    Ival.mem_mul hD hN1
  by_cases hpq1 : p = q + 1
  · have hAq : ‖a q‖ ∈ CBox.norm c.prec (A.getD q CBox.top) :=
      CBox.mem_norm (hmA q (by omega))
    have hTop : ‖a q‖ + ((n : ℝ) + 1)
        ∈ Ival.add c.prec (CBox.norm c.prec (A.getD q CBox.top))
          (Ival.ofRat c.prec (((n : Nat) : ℚ) + 1)) :=
      Ival.mem_add hAq hN1
    have hval : cpfqRatio p q a b ‖z‖ n
        = (‖z‖ * (∏ i ∈ Finset.range (min p q), (‖a i - b i‖ / ‖b i + (n : ℂ)‖ + 1))
          / ((∏ j ∈ Finset.Ico p q, ‖b j + (n : ℂ)‖) * ((n : ℝ) + 1)))
          * (‖a q‖ + ((n : ℝ) + 1)) := by
      unfold cpfqRatio
      rw [ite_eq_left hpq1]
      ring
    rw [hval]
    simp only [cpfqRBox, ite_eq_left hpq1]
    exact Ival.mem_mul
      (Ival.mem_div (Ival.mem_mul hZabs hN) hDen) hTop
  · have hbase : cpfqRatio p q a b ‖z‖ n
        = ‖z‖ * (∏ i ∈ Finset.range (min p q), (‖a i - b i‖ / ‖b i + (n : ℂ)‖ + 1))
          / ((∏ j ∈ Finset.Ico p q, ‖b j + (n : ℂ)‖) * ((n : ℝ) + 1)) := by
      unfold cpfqRatio
      rw [ite_eq_right hpq1]
      ring
    rw [hbase]
    simp only [cpfqRBox, ite_eq_right hpq1]
    exact Ival.mem_div (Ival.mem_mul hZabs hN) hDen

/-- guard element correctness: pole avoidance only — the positivity half
lives in `cpfqGuardRe` and is handled by `cpfqGuardRe_ok`. -/
theorem cpfqGuardElem_ok (J : CBox) (k : Nat) (b : ℂ) (hb : b ∈ J)
    (h : cpfqGuardElem J k = true) : (b + (k : ℂ)) ≠ 0 := by
  cases hrelo : J.re.lo with
  | none => simp only [cpfqGuardElem, hrelo] at h; exact Bool.noConfusion h
  | some rlo =>
    cases hrehi : J.re.hi with
    | none => simp only [cpfqGuardElem, hrelo, hrehi] at h; exact Bool.noConfusion h
    | some rhi =>
      cases himlo : J.im.lo with
      | none =>
        simp only [cpfqGuardElem, hrelo, hrehi, himlo] at h
        exact Bool.noConfusion h
      | some ilo =>
        cases himhi : J.im.hi with
        | none =>
          simp only [cpfqGuardElem, hrelo, hrehi, himlo, himhi] at h
          exact Bool.noConfusion h
        | some ihi =>
          rw [CBox.mem_def] at hb
          obtain ⟨hre, him⟩ := hb
          rw [Ival.mem_def] at hre
          obtain ⟨hloF, hhiF⟩ := hre
          have hloR : ((rlo.toRat : ℚ) : ℝ) ≤ b.re := hloF rlo hrelo
          have hhiR : b.re ≤ ((rhi.toRat : ℚ) : ℝ) := hhiF rhi hrehi
          rw [Ival.mem_def] at him
          obtain ⟨hiloF, hihiF⟩ := him
          have hiloR : ((ilo.toRat : ℚ) : ℝ) ≤ b.im := hiloF ilo himlo
          have hihiR : b.im ≤ ((ihi.toRat : ℚ) : ℝ) := hihiF ihi himhi
          intro hcontra
          have hcRe : b.re + ((k : ℕ) : ℝ) = 0 := by
            have := congrArg Complex.re hcontra
            rwa [Complex.zero_re, Complex.add_re, Complex.natCast_re] at this
          have hcIm : b.im = 0 := by
            have := congrArg Complex.im hcontra
            rwa [Complex.zero_im, Complex.add_im, Complex.natCast_im, add_zero] at this
          have f1 : ¬ (rhi.toRat + (k : ℚ) < 0) := by
            intro hx
            have hxR : ((rhi.toRat : ℚ) : ℝ) + ((k : ℕ) : ℝ) < 0 := by
              exact_mod_cast hx
            linarith
          have f2 : ¬ (0 < rlo.toRat + (k : ℚ)) := by
            intro hx
            have hxR : (0 : ℝ) < ((rlo.toRat : ℚ) : ℝ) + ((k : ℕ) : ℝ) := by
              exact_mod_cast hx
            linarith
          have f3 : ¬ (ihi.toRat < 0) := by
            intro hx
            have hxR : ((ihi.toRat : ℚ) : ℝ) < 0 := by exact_mod_cast hx
            linarith
          have f4 : ¬ (0 < ilo.toRat) := by
            intro hx
            have hxR : (0 : ℝ) < ((ilo.toRat : ℚ) : ℝ) := by exact_mod_cast hx
            linarith
          have heqf : cpfqGuardElem J k = false := by
            simp only [cpfqGuardElem, hrelo, hrehi, himlo, himhi,
              decide_eq_false_iff_not, not_or]
            exact ⟨⟨f1, f2⟩, ⟨f3, f4⟩⟩
          rw [heqf] at h
          exact Bool.noConfusion h

/-- guard real-part positivity (the half of `pfqGuardElem_ok` handled by
`cpfqGuardRe` in the complex engine). -/
theorem cpfqGuardRe_ok (J : CBox) (n : Nat) (b : ℂ) (hb : b ∈ J)
    (h : cpfqGuardRe J n = true) : 0 < (b + (n : ℂ)).re := by
  cases hlo : J.re.lo with
  | none => simp only [cpfqGuardRe, hlo] at h; exact Bool.noConfusion h
  | some rlo =>
    rw [CBox.mem_def] at hb
    obtain ⟨hCreal, _⟩ := hb
    rw [Ival.mem_def] at hCreal
    have hloR : ((rlo.toRat : ℚ) : ℝ) ≤ b.re := hCreal.1 rlo hlo
    simp only [cpfqGuardRe, hlo, decide_eq_true_eq] at h
    have hposR : (0 : ℝ) < ((rlo.toRat : ℚ) : ℝ) + ((n : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Complex.add_re, Complex.natCast_re]
    linarith

/-- guard correctness (mirror `pfqGuard_ok`). -/
theorem cpfqGuard_ok (b : ℕ → ℂ) (B : List CBox) (n : Nat)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i CBox.top)
    (hguard : cpfqGuard B n = true) :
    (∀ j : Nat, j < B.length → 0 < (b j + (n : ℂ)).re)
      ∧ (∀ j : Nat, j < B.length → ∀ k : Nat, k < n → (b j + (k : ℂ)) ≠ 0) := by
  have main : ∀ (Bs : List CBox) (o : Nat),
      (∀ i : Nat, i < Bs.length → b (o + i) ∈ Bs.getD i CBox.top) →
      cpfqGuard Bs n = true →
      (∀ j : Nat, j < Bs.length → 0 < (b (o + j) + (n : ℂ)).re)
      ∧ (∀ j : Nat, j < Bs.length → ∀ k : Nat, k < n →
          (b (o + j) + (k : ℂ)) ≠ 0) := by
    intro Bs
    induction Bs with
    | nil =>
      intro o _ _
      constructor <;> (intro j hj; simp at hj)
    | cons J Js ih =>
      intro o hm hg
      simp only [cpfqGuard, List.all_cons] at hg
      rw [Bool.and_eq_true] at hg
      obtain ⟨hreg, hpolg⟩ := hg
      rw [Bool.and_eq_true] at hreg
      obtain ⟨hreJ, hreJs⟩ := hreg
      have hpoleHead : ∀ k : Nat, k < n → cpfqGuardElem J k = true := by
        intro k hk
        have h1 := List.all_eq_true.mp hpolg k (List.mem_range.mpr hk)
        rw [Bool.and_eq_true] at h1
        exact h1.1
      have hpoleJs : (List.range n).all
          (fun k => Js.all (fun J' => cpfqGuardElem J' k)) = true := by
        refine List.all_eq_true.mpr (fun k hkmem => ?_)
        have h1 := List.all_eq_true.mp hpolg k hkmem
        rw [Bool.and_eq_true] at h1
        exact h1.2
      have hguardJs : cpfqGuard Js n = true := by
        simp only [cpfqGuard]
        rw [Bool.and_eq_true]
        exact ⟨hreJs, hpoleJs⟩
      have hmem : b (o + 0) ∈ (J :: Js).getD 0 CBox.top := hm 0 (by simp)
      have hhead : b o ∈ J := by simpa using hmem
      have hposHead : 0 < (b o + (n : ℂ)).re := cpfqGuardRe_ok J n (b o) hhead hreJ
      have hm' : ∀ i : Nat, i < Js.length → b ((o + 1) + i) ∈ Js.getD i CBox.top := by
        intro i hi
        have h2 : i + 1 < (J :: Js).length := by
          simp only [List.length_cons] at hi ⊢
          omega
        have h3 := hm (i + 1) h2
        have e : o + (i + 1) = (o + 1) + i := by omega
        rw [e] at h3
        simpa using h3
      have hrec := ih (o + 1) hm' hguardJs
      obtain ⟨hr1, hr2⟩ := hrec
      have hlen : (J :: Js).length = Js.length + 1 := rfl
      constructor
      · intro j hj
        cases j with
        | zero => simpa using hposHead
        | succ j =>
          have e : o + (j + 1) = (o + 1) + j := by omega
          rw [e]
          exact hr1 j (by omega)
      · intro j hj k hk
        cases j with
        | zero =>
          simpa using cpfqGuardElem_ok J k (b o) hhead (hpoleHead k hk)
        | succ j =>
          have e : o + (j + 1) = (o + 1) + j := by omega
          rw [e]
          exact hr2 j (by omega) k hk
  have hfinal := main B 0 (fun i hi => by simpa using hmB i hi) hguard
  simpa only [Nat.zero_add] using hfinal

/-- rising-product box membership (mirror `mem_risingZ`). -/
theorem mem_risingCBox (c : Ctx) (hc : c.Valid) (S : CBox) (s : ℂ)
    (hs : s ∈ S) (k : Nat) :
    (∏ j ∈ Finset.range k, (s + (j : ℂ))) ∈ risingCBox c S k := by
  induction k with
  | zero =>
    simp only [risingCBox, Finset.range_zero, Finset.prod_empty]
    exact ⟨by rw [Complex.one_re]; exact Ival.mem_one,
      by rw [Complex.one_im]; exact Ival.mem_zero⟩
  | succ k ih =>
    rw [Finset.prod_range_succ]
    simp only [risingCBox]
    exact CBox.mem_mul ih (CBox.mem_add hs (mem_cNatBox c k))

/-- closed-form term membership (mirror `mem_pfqTermIval`). -/
theorem mem_cpfqTermBox (c : Ctx) (hc : c.Valid)
    (a b : ℕ → ℂ) (A B : List CBox) (p q : Nat) (Z : CBox) (z : ℂ) (k : Nat)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i CBox.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i CBox.top)
    (hmZ : z ∈ Z) :
    cpfqTerm p q a b z k ∈ cpfqTermBox c A B p q Z k := by
  have hfaN : ∀ m : Nat, m ≤ p → List.Forall₂ (fun w B => w ∈ B)
      ((List.range m).map fun i => (∏ j ∈ Finset.range k, (a i + (j : ℂ))))
      ((List.range m).map fun i => risingCBox c (A.getD i CBox.top) k) := by
    intro m
    induction m with
    | zero => intro _; exact List.Forall₂.nil
    | succ m ih =>
      intro hmle
      rw [List.range_succ, List.map_append, List.map_append]
      refine List.rel_append (ih (by omega)) ?_
      refine List.Forall₂.cons ?_ List.Forall₂.nil
      have hmem : a m ∈ A.getD m CBox.top := by
        rcases Nat.lt_or_ge m A.length with hml | hml
        · exact hmA m hml
        · have hdefaul : A.getD m CBox.top = CBox.top :=
            List.getD_eq_default A CBox.top hml
          rw [hdefaul]
          exact CBox.mem_top _
      exact mem_risingCBox c hc _ _ hmem k
  have hfaD : ∀ m : Nat, m ≤ q → List.Forall₂ (fun w B => w ∈ B)
      ((List.range m).map fun i => (∏ j ∈ Finset.range k, (b i + (j : ℂ))))
      ((List.range m).map fun i => risingCBox c (B.getD i CBox.top) k) := by
    intro m
    induction m with
    | zero => intro _; exact List.Forall₂.nil
    | succ m ih =>
      intro hmle
      rw [List.range_succ, List.map_append, List.map_append]
      refine List.rel_append (ih (by omega)) ?_
      refine List.Forall₂.cons ?_ List.Forall₂.nil
      have hmem : b m ∈ B.getD m CBox.top := by
        rcases Nat.lt_or_ge m B.length with hml | hml
        · exact hmB m hml
        · have hdefaul : B.getD m CBox.top = CBox.top :=
            List.getD_eq_default B CBox.top hml
          rw [hdefaul]
          exact CBox.mem_top _
      exact mem_risingCBox c hc _ _ hmem k
  have hnum := mem_cprod c hc _ _ (hfaN p le_rfl)
  rw [list_prod_map_rangeC] at hnum
  have hden := mem_cprod c hc _ _ (hfaD q le_rfl)
  rw [list_prod_map_rangeC] at hden
  have hpow : z ^ k ∈ CBox.npow c.prec Z k := CBox.mem_npow hmZ k
  have hfact : ((Nat.factorial k : ℕ) : ℂ) ∈ cNatBox c (Nat.factorial k) :=
    mem_cNatBox c _
  have hval : cpfqTerm p q a b z k
      = (((Finset.range p).prod (fun i => (∏ j ∈ Finset.range k, (a i + (j : ℂ)))) * z ^ k
        / (Finset.range q).prod (fun i => (∏ j ∈ Finset.range k, (b i + (j : ℂ)))))
        / ((Nat.factorial k : ℕ) : ℂ)) := by
    simp only [cpfqTerm]
    ring
  rw [hval]
  simp only [cpfqTermBox]
  exact CBox.mem_div (CBox.mem_div (CBox.mem_mul hnum hpow) hden) hfact

/-- terminating-top exact identity (mirror `pfqTerm_exact`). -/
theorem cpfqTerm_exact (p q : Nat) (a b : ℕ → ℂ) (z : ℂ) (m : Nat) (i₀ : Nat)
    (hi₀ : i₀ < p) (hterm : a i₀ = -(m : ℂ)) :
    cpfqComplex p q a b z
      = (Finset.range (m + 1)).sum (fun k => cpfqTerm p q a b z k) := by
  unfold cpfqComplex
  apply tsum_eq_sum
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  have h0 : ∏ i ∈ Finset.range p, ∏ j ∈ Finset.range k, (a i + (j : ℂ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.2 hi₀)
    apply Finset.prod_eq_zero (i := m) (Finset.mem_range.2 (by omega))
    rw [hterm]; ring
  simp [cpfqTerm, h0]

/-- finite-prefix soundness (mirror `pfqFinite_sound`). -/
theorem cpfqFinite_sound (c : Ctx) (hc : c.Valid)
    (p q : Nat) (a b : ℕ → ℂ) (A B : List CBox) (Z : CBox) (z : ℂ)
    (m : Nat) (i₀ : Nat)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i CBox.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i CBox.top)
    (hmZ : z ∈ Z)
    (hi₀ : i₀ < p) (hterm : a i₀ = -(m : ℂ)) :
    cpfqComplex p q a b z ∈ cpfqFiniteBox c A B p q Z m := by
  have hfa : ∀ t : Nat, t ≤ m + 1 → List.Forall₂ (fun w B => w ∈ B)
      ((List.range t).map fun k => cpfqTerm p q a b z k)
      ((List.range t).map fun k => cpfqTermBox c A B p q Z k) := by
    intro t
    induction t with
    | zero => intro _; exact List.Forall₂.nil
    | succ t ih =>
      intro htle
      rw [List.range_succ, List.map_append, List.map_append]
      refine List.rel_append (ih (by omega)) ?_
      refine List.Forall₂.cons ?_ List.Forall₂.nil
      exact mem_cpfqTermBox c hc a b A B p q Z z t hmA hmB hmZ
  have hmem := mem_csum c hc _ _ (hfa (m + 1) le_rfl)
  rw [list_sum_map_rangeC] at hmem
  rw [cpfqTerm_exact p q a b z m i₀ hi₀ hterm]
  exact hmem

/-- disc membership from a norm bound. -/
theorem mem_cpfqDisc (c : Ctx) {z : ℂ} {h : Dy} (hle : ‖z‖ ≤ ((h.toRat : ℚ) : ℝ)) :
    z ∈ (⟨Ival.ofRats c.prec (-h.toRat) h.toRat,
      Ival.ofRats c.prec (-h.toRat) h.toRat⟩ : CBox) := by
  have hre : |z.re| ≤ ((h.toRat : ℚ) : ℝ) := le_trans (Complex.abs_re_le_norm z) hle
  refine ⟨?_, ?_⟩
  · obtain ⟨h1, h2⟩ := abs_le.mp hre
    have hlo : ((-h.toRat : ℚ) : ℝ) ≤ z.re := by
      simp only [Rat.cast_neg]
      exact h1
    exact Ival.mem_ofRats hlo h2
  · have him : |z.im| ≤ ((h.toRat : ℚ) : ℝ) := le_trans (Complex.abs_im_le_norm z) hle
    obtain ⟨h1, h2⟩ := abs_le.mp him
    have hlo : ((-h.toRat : ℚ) : ℝ) ≤ z.im := by
      simp only [Rat.cast_neg]
      exact h1
    exact Ival.mem_ofRats hlo h2

/-- from `0 < Re w` derive `w ≠ 0`. -/
theorem cpfq_ne_zero_of_re_pos (w : ℂ) (h : 0 < w.re) : w ≠ 0 := by
  intro hz
  rw [hz] at h
  simp only [Complex.zero_re] at h
  linarith

/-- from `0 < Re w` derive `0 < ‖w‖`. -/
theorem cpfq_norm_pos_of_re_pos (w : ℂ) (h : 0 < w.re) : 0 < ‖w‖ := by
  have h1 := Complex.abs_re_le_norm (w : ℂ)
  have h2 : 0 < |w.re| := abs_pos.mpr (ne_of_gt h)
  linarith

/-- norms of real-shifted points are monotone once the real part clears `-n`:
`Re(y + n) > 0`, `n ≤ k` imply `‖y + n‖ ≤ ‖y + k‖`. -/
theorem cpfq_norm_shift_mono (y : ℂ) (m k : Nat) (hmk : m ≤ k)
    (hy : 0 < (y + (m : ℂ)).re) :
    ‖y + (m : ℂ)‖ ≤ ‖y + (k : ℂ)‖ := by
  have hn0 : ((m : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hmk
  have hp : 0 < y.re + ((m : ℕ) : ℝ) := by
    rw [Complex.add_re, Complex.natCast_re] at hy
    exact hy
  have e1 : Complex.normSq (y + (m : ℂ)) = ((y.re + ((m:ℕ):ℝ)) ^ 2) + ((y.im) ^ 2) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.natCast_re, Complex.natCast_im]
    push_cast
    ring
  have e2 : Complex.normSq (y + (k : ℂ)) = ((y.re + ((k:ℕ):ℝ)) ^ 2) + ((y.im) ^ 2) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.natCast_re, Complex.natCast_im]
    push_cast
    ring
  have h1 : Complex.normSq (y + (m : ℂ)) ≤ Complex.normSq (y + (k : ℂ)) := by
    rw [e1, e2]
    push_cast
    have hpos : 0 ≤ 2 * y.re + ((k:ℕ):ℝ) + ((m:ℕ):ℝ) := by linarith
    nlinarith [hn0, hpos]
  have h2 : ‖y + (m : ℂ)‖ ^ 2 ≤ ‖y + (k : ℂ)‖ ^ 2 := by
    rwa [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h1
  nlinarith [norm_nonneg (y + (m : ℂ)), norm_nonneg (y + (k : ℂ))]

/-- paired estimate (complex norms, mirror `pfq_factor_le`):
`‖x + k‖/‖y + k‖ ≤ ‖x − y‖/‖y + n‖ + 1` for `k ≥ n` when `Re(y + n) > 0`. -/
theorem cpfq_factor_le (x y : ℂ) (n k : Nat) (hnk : n ≤ k)
    (hy : 0 < (y + (n : ℂ)).re) :
    ‖x + (k : ℂ)‖ / ‖y + (k : ℂ)‖ ≤ ‖x - y‖ / ‖y + (n : ℂ)‖ + 1 := by
  have hyy : ‖y + (n : ℂ)‖ ≤ ‖y + (k : ℂ)‖ := cpfq_norm_shift_mono y n k hnk hy
  have hyn : 0 < ‖y + (n : ℂ)‖ := by
    have h1 := Complex.abs_re_le_norm (y + (n : ℂ))
    have h2 : 0 < |(y + (n : ℂ)).re| := abs_pos.mpr (ne_of_gt hy)
    linarith
  have hyk : 0 < ‖y + (k : ℂ)‖ := by linarith
  rw [div_le_iff₀ hyk]
  have h1 : ‖x + (k : ℂ)‖ ≤ ‖x - y‖ + ‖y + (k : ℂ)‖ := by
    have e : x + (k : ℂ) = (x - y) + (y + (k : ℂ)) := by ring
    rw [e]
    exact norm_add_le _ _
  have h2 : ‖x - y‖ ≤ ‖x - y‖ / ‖y + (n : ℂ)‖ * ‖y + (k : ℂ)‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hyn]
    exact mul_le_mul_of_nonneg_left hyy (norm_nonneg _)
  nlinarith

/-- ratio bound for the actual step sizes (complex norms; mirror `pfq_ratio_le`). -/
theorem cpfq_ratio_le (p q : Nat) (a b : ℕ → ℂ) (z : ℂ) (n k : Nat) (hnk : n ≤ k)
    (hpq : p ≤ q + 1)
    (hBpos : ∀ j : Nat, j < q → 0 < (b j + (n : ℂ)).re) :
    ‖(∏ i ∈ Finset.range p, (a i + (k : ℂ)))
        / (∏ j ∈ Finset.range q, (b j + (k : ℂ))) * z / ((k : ℂ) + 1)‖
      ≤ cpfqRatio p q a b ‖z‖ n := by
  have hk : (n:ℝ) ≤ (k:ℝ) := by exact_mod_cast hnk
  have hkn1 : (0:ℝ) < k + 1 := by positivity
  have hn1 : (0:ℝ) < n + 1 := by positivity
  have hknc : ‖((k:ℂ) + 1)‖ = (k:ℝ) + 1 := by
    rw [← Nat.cast_add_one (k : ℕ), norm_natCast]
    push_cast
    ring
  have hBk : ∀ j, j < q → 0 < ‖b j + (k:ℂ)‖ := by
    intro j hj
    have h1 : 0 < (b j + (k:ℂ)).re := by
      rw [Complex.add_re, Complex.natCast_re]
      have h2 := hBpos j hj
      rw [Complex.add_re, Complex.natCast_re] at h2
      linarith
    exact cpfq_norm_pos_of_re_pos _ h1
  have hP : ∀ m, m ≤ q →
      (∏ i ∈ Finset.range m, ‖a i + (k:ℂ)‖)
        / (∏ i ∈ Finset.range m, ‖b i + (k:ℂ)‖)
        ≤ ∏ i ∈ Finset.range m, (‖a i - b i‖ / ‖b i + (n:ℂ)‖ + 1) := by
    intro m hmq
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_le_prod₀
    · intro i hi
      exact div_nonneg (norm_nonneg _) (hBk i (by simp at hi; omega)).le
    · intro i hi
      exact cpfq_factor_le _ _ n k hnk (hBpos i (by simp at hi; omega))
  have hPpos : ∀ m, m ≤ q → 0 < ∏ i ∈ Finset.range m, ‖b i + (k:ℂ)‖ := fun m hm =>
    Finset.prod_pos (fun i hi => hBk i (by simp at hi; omega))
  have hPbnn : ∀ m, m ≤ q →
      0 ≤ ∏ i ∈ Finset.range m, (‖a i - b i‖ / ‖b i + (n:ℂ)‖ + 1) := fun m hm =>
    Finset.prod_nonneg fun i hi =>
      add_nonneg
        (div_nonneg (norm_nonneg _)
          (cpfq_norm_pos_of_re_pos _ (hBpos i (by simp at hi; omega))).le) zero_le_one
  rcases Nat.lt_or_ge q p with hlt | hle
  · have hp : p = q + 1 := by omega
    subst hp
    have hmin : min (q+1) q = q := by omega
    simp only [cpfqRatio, hmin, ite_true, Finset.Ico_eq_empty_of_le (Nat.le_succ q),
      Finset.prod_empty, one_mul, Finset.prod_range_succ]
    have hA : ‖a q + (k:ℂ)‖ / ((k:ℝ) + 1) ≤ (‖a q‖ + (n:ℝ) + 1) / ((n:ℝ) + 1) := by
      rw [div_le_div_iff₀ hkn1 hn1]
      have hw := norm_add_le (a q) ((k:ℂ))
      rw [norm_natCast] at hw
      nlinarith [norm_nonneg (a q)]
    have e : ‖(∏ i ∈ Finset.range q, (a i + (k:ℂ))) * (a q + (k:ℂ))
        / (∏ j ∈ Finset.range q, (b j + (k:ℂ))) * z / ((k : ℂ) + 1)‖
        = ‖z‖ * ((∏ i ∈ Finset.range q, ‖a i + (k:ℂ)‖)
            / (∏ i ∈ Finset.range q, ‖b i + (k:ℂ)‖))
          * (‖a q + (k:ℂ)‖ / ((k:ℝ) + 1)) := by
      simp only [norm_div, norm_mul, hknc]
      simp only [norm_prod]
      ring
    rw [e]
    have hPq := hP q le_rfl
    calc _ ≤ ‖z‖ * (∏ i ∈ Finset.range q, (‖a i - b i‖ / ‖b i + (n:ℂ)‖ + 1))
          * ((‖a q‖ + (n:ℝ) + 1) / ((n:ℝ) + 1)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hPq (norm_nonneg (z : ℂ))) hA
            (div_nonneg (norm_nonneg (a q + (k : ℂ))) hkn1.le)
            (mul_nonneg (norm_nonneg (z : ℂ)) (hPbnn q le_rfl))
      _ = _ := by ring
  · have hmin : min p q = p := by omega
    simp only [cpfqRatio, hmin, show p ≠ q + 1 by omega, ite_false, mul_one]
    rw [← Finset.prod_range_mul_prod_Ico _ hle]
    have hD : ∀ m : ℕ, m ≥ n → 0 < ∏ j ∈ Finset.Ico p q, ‖b j + (m:ℂ)‖ := fun m hm =>
      Finset.prod_pos (fun j hj => by
        simp at hj
        have hmon := cpfq_norm_shift_mono (b j) n m hm (hBpos j hj.2)
        have hpos0 := cpfq_norm_pos_of_re_pos (b j + (n:ℂ)) (hBpos j hj.2)
        linarith [hmon, hpos0])
    have hDle : ∏ j ∈ Finset.Ico p q, ‖b j + (n:ℂ)‖ ≤ ∏ j ∈ Finset.Ico p q, ‖b j + (k:ℂ)‖ :=
      Finset.prod_le_prod₀ (fun j hj => by simp at hj; exact norm_nonneg _)
        (fun j hj => by simp at hj; exact cpfq_norm_shift_mono (b j) n k hnk (hBpos j hj.2))
    have e : ‖(∏ i ∈ Finset.range p, (a i + (k:ℂ)))
        / ((∏ j ∈ Finset.range p, (b j + (k:ℂ))) * ∏ j ∈ Finset.Ico p q, (b j + (k:ℂ)))
          * z / ((k : ℂ) + 1)‖
        = ‖z‖ * ((∏ i ∈ Finset.range p, ‖a i + (k:ℂ)‖)
            / (∏ i ∈ Finset.range p, ‖b i + (k:ℂ)‖))
          / ((∏ j ∈ Finset.Ico p q, ‖b j + (k:ℂ)‖) * ((k:ℝ) + 1)) := by
      rw [norm_div, norm_mul, norm_div, norm_mul, hknc, norm_prod, norm_prod, norm_prod]
      field_simp
    rw [e]
    apply div_le_div₀ (mul_nonneg (norm_nonneg (z : ℂ)) (hPbnn p hle))
      (mul_le_mul_of_nonneg_left (hP p hle) (norm_nonneg (z : ℂ)))
      (mul_pos (hD n le_rfl) hn1)
      (mul_le_mul hDle (by linarith) hn1.le (hD k hnk).le)

/-- one-step ratio bound for the actual terms, for all `k ≥ n`
(mirror `pfqTerm_ratio_step`). -/
theorem cpfqTerm_ratio_step (p q : Nat) (a b : ℕ → ℂ) (z : ℂ) (n : Nat)
    (hpq : p ≤ q + 1)
    (hBpos : ∀ j : Nat, j < q → 0 < (b j + (n : ℂ)).re) :
    ∀ k, n ≤ k → ‖cpfqTerm p q a b z (k + 1)‖
      ≤ cpfqRatio p q a b ‖z‖ n * ‖cpfqTerm p q a b z k‖ := by
  intro k hk
  have hkr : (n:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  rw [cpfqTerm_succ p q a b z k (fun j hj => by
      have h1 : 0 < (b j + (k:ℂ)).re := by
        rw [Complex.add_re, Complex.natCast_re]
        have h2 := hBpos j hj
        rw [Complex.add_re, Complex.natCast_re] at h2
        linarith
      exact cpfq_ne_zero_of_re_pos _ h1), norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (cpfq_ratio_le p q a b z n k hk hpq hBpos)
    (norm_nonneg _)

theorem cpfqRatio_nonneg (p q : Nat) (a b : ℕ → ℂ) (z : ℂ) (n : Nat)
    (hpq : p ≤ q + 1)
    (hBpos : ∀ j : Nat, j < q → 0 < (b j + (n : ℂ)).re) :
    0 ≤ cpfqRatio p q a b ‖z‖ n :=
  (norm_nonneg _).trans (cpfq_ratio_le p q a b z n n le_rfl hpq hBpos)

/-- geometric tail for complex series (mirror `pfq_geom_tail`). -/
theorem cpfq_geom_tail (T : ℕ → ℂ) (R : ℝ) (n : ℕ) (hR0 : 0 ≤ R) (hR : R < 1)
    (h : ∀ k, n ≤ k → ‖T (k + 1)‖ ≤ R * ‖T k‖) :
    Summable T ∧ ‖∑' k, T k - ∑ k ∈ Finset.range n, T k‖ ≤ ‖T n‖ / (1 - R) := by
  have hb : ∀ j, ‖T (j + n)‖ ≤ ‖T n‖ * R ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc ‖T (j + 1 + n)‖ = ‖T ((j + n) + 1)‖ := by rw [Nat.add_right_comm]
        _ ≤ R * ‖T (j + n)‖ := h _ (by omega)
        _ ≤ R * (‖T n‖ * R ^ j) := mul_le_mul_of_nonneg_left ih hR0
        _ = ‖T n‖ * R ^ (j + 1) := by ring
  have hg : Summable (fun j => ‖T n‖ * R ^ j) :=
    (summable_geometric_of_lt_one hR0 hR).mul_left _
  have hsn : Summable (fun j => ‖T (j + n)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hb hg
  have hs' : Summable (fun j => T (j + n)) := hsn.of_norm
  have hs : Summable T := (summable_nat_add_iff n).mp hs'
  refine ⟨hs, ?_⟩
  rw [← hs.sum_add_tsum_nat_add n, add_sub_cancel_left]
  calc ‖∑' j, T (j + n)‖ ≤ ∑' j, ‖T (j + n)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' j, ‖T n‖ * R ^ j := hsn.tsum_le_tsum hb hg
    _ = ‖T n‖ / (1 - R) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hR0 hR, div_eq_mul_inv]

/-- norm tail bound (mirror `pfqTail_corrected_succ`; the abstract
`summable + ‖·‖ ≤` step is `cpfq_geom_tail`). -/
theorem cpfqTail_bound (p q : Nat) (a b : ℕ → ℂ) (z : ℂ) (n : Nat)
    (hpq : p ≤ q + 1)
    (hBpos : ∀ j : Nat, j < q → 0 < (b j + (n : ℂ)).re)
    (hR : cpfqRatio p q a b ‖z‖ n < 1) :
    ‖cpfqComplex p q a b z
      - (Finset.range (n + 1)).sum (fun j => cpfqTerm p q a b z j)‖
      ≤ ‖cpfqTerm p q a b z n‖
        * (cpfqRatio p q a b ‖z‖ n / (1 - cpfqRatio p q a b ‖z‖ n)) := by
  set R := cpfqRatio p q a b ‖z‖ n with hRdef
  have hR0 : 0 ≤ R := cpfqRatio_nonneg p q a b z n hpq hBpos
  have hstep := cpfqTerm_ratio_step p q a b z n hpq hBpos
  have h := (cpfq_geom_tail (fun k => cpfqTerm p q a b z k) R (n + 1) hR0 hR
    (fun k hk => hstep k (by omega))).2
  have h1 : 0 < 1 - R := by linarith
  calc _ ≤ ‖cpfqTerm p q a b z (n + 1)‖ / (1 - R) := h
    _ ≤ (R * ‖cpfqTerm p q a b z n‖) / (1 - R) :=
        div_le_div_of_nonneg_right (hstep n le_rfl) h1.le
    _ = _ := by ring

/-- search result is a genuine terminating top (complex mirror of `pfqFindTerm_ok`). -/
theorem cpfqFindTerm_ok (a : ℕ → ℂ) :
    ∀ (As : List CBox) (o : Nat),
    (∀ i : Nat, i < As.length → a (o + i) ∈ As.getD i CBox.top) →
    ∀ (r : Option (Nat × Nat)), cpfqFindTerm As o = r →
    ∀ (i₀ m : Nat), r = some (i₀, m) → i₀ < o + As.length ∧ a i₀ = -(m : ℂ) := by
  intro As
  induction As with
  | nil =>
    intro o _ r hr i₀ m hrm
    simp only [cpfqFindTerm] at hr
    rw [hrm] at hr
    exact absurd hr (by simp)
  | cons B Bs ih =>
    intro o hm r hr i₀ m hrm
    have hrec_step : (cpfqFindTerm (B :: Bs) o = cpfqFindTerm Bs (o + 1)) →
        i₀ < o + (B :: Bs).length ∧ a i₀ = -(m : ℂ) := by
      intro hstep
      rw [hstep] at hr
      have hm' : ∀ i : Nat, i < Bs.length → a ((o + 1) + i) ∈ Bs.getD i CBox.top := by
        intro i hi
        have h2 : i + 1 < (B :: Bs).length := by simp only [List.length_cons] at hi ⊢; omega
        have h3 := hm (i + 1) h2
        have e : o + (i + 1) = (o + 1) + i := by omega
        rw [e] at h3
        simpa using h3
      obtain ⟨hlt, hval⟩ := ih (o + 1) hm' r hr i₀ m hrm
      have hlen : (B :: Bs).length = Bs.length + 1 := rfl
      exact ⟨by omega, hval⟩
    cases hrelo : B.re.lo with
    | none => exact hrec_step (by simp [cpfqFindTerm, hrelo])
    | some rlo =>
      cases hrehi : B.re.hi with
      | none => exact hrec_step (by simp [cpfqFindTerm, hrelo, hrehi])
      | some rhi =>
        cases himlo : B.im.lo with
        | none => exact hrec_step (by simp [cpfqFindTerm, hrelo, hrehi, himlo])
        | some ilo =>
          cases himhi : B.im.hi with
          | none => exact hrec_step (by simp [cpfqFindTerm, hrelo, hrehi, himlo, himhi])
          | some ihi =>
            by_cases hpt : (rlo = rhi && ilo = ihi && ilo.toRat = 0) = true
            · have hstep : cpfqFindTerm (B :: Bs) o =
                  (let q := rlo.toRat
                  if q.den = 1 ∧ q.num ≤ 0 then some (o, (-q.num).toNat)
                  else cpfqFindTerm Bs (o + 1)) := by
                simp [cpfqFindTerm, hrelo, hrehi, himlo, himhi, hpt]
              rw [hstep] at hr
              by_cases hnat : rlo.toRat.den = 1 ∧ rlo.toRat.num ≤ 0
              · simp only [hnat, and_self, ite_true] at hr
                have hr' : some (o, (-rlo.toRat.num).toNat) = r := hr
                rw [hrm] at hr'
                have hpair : o = i₀ ∧ (-rlo.toRat.num).toNat = m := by
                  simpa using hr'
                obtain ⟨e1, e2⟩ := hpair
                rw [← e1, ← e2]
                have hmem : a (o + 0) ∈ (B :: Bs).getD 0 CBox.top := hm 0 (by simp)
                simp only [Nat.add_zero] at hmem
                have hptB : (B :: Bs).getD 0 CBox.top = B := rfl
                rw [hptB] at hmem
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hpt
                obtain ⟨⟨hrpt, hipt⟩, him0⟩ := hpt
                have hrehi' : B.re.hi = some rlo := by rw [← hrpt] at hrehi; exact hrehi
                have himhi' : B.im.hi = some ilo := by rw [← hipt] at himhi; exact himhi
                refine ⟨?_, ?_⟩
                · have hlen : (B :: Bs).length = Bs.length + 1 := rfl
                  omega
                · have hmemRe := dyPointMem (X := B.re) hmem.1 hrelo hrehi'
                  have hmemIm := dyPointMem (X := B.im) hmem.2 himlo himhi'
                  rw [him0] at hmemIm
                  have hq : rlo.toRat = ((rlo.toRat.num : ℤ) : ℚ) := by
                    have h := rlo.toRat.num_div_den
                    rw [hnat.1] at h
                    rw [← h]
                    simp
                  rw [hq] at hmemRe
                  have hzz : (rlo.toRat.num : ℤ)
                      = -(((-rlo.toRat.num).toNat : Nat) : ℤ) := by
                    have htn : (((-rlo.toRat.num).toNat : Nat) : ℤ) = -rlo.toRat.num :=
                      Int.toNat_of_nonneg (by omega : 0 ≤ -rlo.toRat.num)
                    omega
                  have hre_eq : (a o).re = -(((-rlo.toRat.num).toNat : Nat) : ℝ) := by
                    rw [hmemRe]
                    exact_mod_cast hzz
                  have him_eq : (a o).im = 0 := by exact_mod_cast hmemIm
                  apply Complex.ext
                  · rw [hre_eq, Complex.neg_re, Complex.natCast_re]
                  · rw [him_eq, Complex.neg_im, Complex.natCast_im, neg_zero]
              · exact hrec_step (by rw [hstep, ite_eq_right hnat])
            · have hptF : (rlo = rhi && ilo = ihi && ilo.toRat = 0) = false :=
                Bool.eq_false_iff.mpr hpt
              exact hrec_step (by simp [cpfqFindTerm, hrelo, hrehi, himlo, himhi, hptF])

/-- `k = 0` term is `1`. -/
theorem cpfqTerm_zero (p q : Nat) (a b : ℕ → ℂ) (z : ℂ) :
    cpfqTerm p q a b z 0 = 1 := by
  simp [cpfqTerm]

/-- core soundness (mirror `pfqCore_sound`). -/
theorem cpfqCore_sound (c : Ctx) (hc : c.Valid)
    (p q : Nat) (a b : ℕ → ℂ) (A B : List CBox) (Z : CBox) (z : ℂ) (n : Nat)
    (hlenA : A.length = p) (hlenB : B.length = q)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i CBox.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i CBox.top)
    (hmZ : z ∈ Z) :
    cpfqComplex p q a b z ∈ cpfqCoreBox c A B Z n := by
  unfold cpfqCoreBox
  cases hft : cpfqFindTerm A 0 with
  | none =>
    show cpfqComplex p q a b z ∈
      (if A.length > B.length + 1 then CBox.top
        else if cpfqGuard B n then
          let R := cpfqRBox c A B A.length B.length (CBox.norm c.prec Z)
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
        else CBox.top)
    by_cases hlen : A.length > B.length + 1
    · rw [ite_eq_left hlen]
      exact CBox.mem_top _
    · rw [ite_eq_right hlen]
      cases hguard : cpfqGuard B n with
      | false =>
        show cpfqComplex p q a b z ∈ CBox.top
        exact CBox.mem_top _
      | true =>
        set resC := cpfqLoop c A B A.length B.length Z n 0
          ⟨Ival.zero, Ival.zero⟩ ⟨Ival.one, Ival.zero⟩ with hresC
        set SC := CBox.add c.prec resC.1 resC.2 with hSC
        set RIV := cpfqRBox c A B A.length B.length (CBox.norm c.prec Z)
          (CBox.norm c.prec (A.getD B.length CBox.top)) n with hRIV
        set W := Ival.mul c.prec (CBox.norm c.prec resC.2)
          (Ival.div c.prec RIV (Ival.sub c.prec (Ival.ofRat c.prec 1) RIV)) with hWdef
        show cpfqComplex p q a b z ∈
          (match RIV.hi with
          | none => CBox.top
          | some hR =>
            if hR.toRat < 1 then
              match W.hi with
              | some h => CBox.add c.prec SC ⟨Ival.ofRats c.prec (-h.toRat) h.toRat,
                  Ival.ofRats c.prec (-h.toRat) h.toRat⟩
              | none => CBox.top
            else CBox.top)
        rw [← hlenA, ← hlenB]
        obtain ⟨hBpos', hBne⟩ := cpfqGuard_ok b B n hmB hguard
        have hpq' : A.length ≤ B.length + 1 := by omega
        have hS0 : (0 : ℂ) ∈ (⟨Ival.zero, Ival.zero⟩ : CBox) :=
          ⟨by rw [Complex.zero_re]; exact Ival.mem_zero,
            by rw [Complex.zero_im]; exact Ival.mem_zero⟩
        have hT0 : (1 : ℂ) ∈ (⟨Ival.one, Ival.zero⟩ : CBox) :=
          ⟨by rw [Complex.one_re]; exact Ival.mem_one,
            by rw [Complex.one_im]; exact Ival.mem_zero⟩
        have hSr : (0 : ℂ)
            = (Finset.range 0).sum (fun j => cpfqTerm A.length B.length a b z j) := by
          simp
        have hTr : (1 : ℂ) = cpfqTerm A.length B.length a b z 0 :=
          (cpfqTerm_zero A.length B.length a b z).symm
        have hLoop : (Finset.range (0 + n)).sum (fun j => cpfqTerm A.length B.length a b z j)
              ∈ resC.1
            ∧ cpfqTerm A.length B.length a b z (0 + n) ∈ resC.2 :=
          mem_cpfqLoop c hc a b A B Z z n hmA hmB hmZ hBne
            n 0 (by omega) _ _ _ _ hS0 hT0 hSr hTr
        simp only [Nat.zero_add] at hLoop
        obtain ⟨hS, hT⟩ := hLoop
        have hSexact : (Finset.range (n + 1)).sum (fun j => cpfqTerm A.length B.length a b z j)
            = (Finset.range n).sum (fun j => cpfqTerm A.length B.length a b z j)
              + cpfqTerm A.length B.length a b z n :=
          Finset.sum_range_succ _ n
        have hSmem : (Finset.range (n + 1)).sum (fun j => cpfqTerm A.length B.length a b z j)
            ∈ SC := by
          rw [hSexact]
          exact CBox.mem_add hS hT
        have hRmem : cpfqRatio A.length B.length a b ‖z‖ n ∈ RIV :=
          mem_cpfqR c hc a b A B A.length B.length Z z n rfl rfl
            hmA hmB hmZ hpq'
        cases hRhi : RIV.hi with
        | none =>
          show cpfqComplex A.length B.length a b z ∈ CBox.top
          exact CBox.mem_top _
        | some hRD =>
          show cpfqComplex A.length B.length a b z ∈
            (if hRD.toRat < 1 then
              match W.hi with
              | some h => CBox.add c.prec SC ⟨Ival.ofRats c.prec (-h.toRat) h.toRat,
                  Ival.ofRats c.prec (-h.toRat) h.toRat⟩
              | none => CBox.top
            else CBox.top)
          by_cases hRlt : hRD.toRat < 1
          · rw [ite_eq_left hRlt]
            cases hW : W.hi with
            | none =>
              show cpfqComplex A.length B.length a b z ∈ CBox.top
              exact CBox.mem_top _
            | some h =>
              show cpfqComplex A.length B.length a b z ∈
                CBox.add c.prec SC ⟨Ival.ofRats c.prec (-h.toRat) h.toRat,
                  Ival.ofRats c.prec (-h.toRat) h.toRat⟩
              have hR : cpfqRatio A.length B.length a b ‖z‖ n < 1 := by
                have hle : cpfqRatio A.length B.length a b ‖z‖ n ≤ ((hRD.toRat : ℚ) : ℝ) := by
                  have hmem2 := (Ival.mem_def.mp hRmem).2
                  rw [hRhi] at hmem2
                  rw [Ival.leHi_some] at hmem2
                  rwa [Dy.toReal_def] at hmem2
                have hlt1 : ((hRD.toRat : ℚ) : ℝ) < 1 := by exact_mod_cast hRlt
                linarith
              have h1 : (1 : ℝ) ∈ Ival.ofRat c.prec 1 := by
                exact_mod_cast Ival.mem_ofRat c.prec (1 : ℚ)
              have hCmem : cpfqRatio A.length B.length a b ‖z‖ n
                  / (1 - cpfqRatio A.length B.length a b ‖z‖ n)
                  ∈ Ival.div c.prec RIV
                    (Ival.sub c.prec (Ival.ofRat c.prec 1) RIV) :=
                Ival.mem_div hRmem (Ival.mem_sub h1 hRmem)
              have hTnorm : ‖cpfqTerm A.length B.length a b z n‖ ∈ CBox.norm c.prec resC.2 :=
                CBox.mem_norm hT
              have hWmem : ‖cpfqTerm A.length B.length a b z n‖
                  * (cpfqRatio A.length B.length a b ‖z‖ n
                    / (1 - cpfqRatio A.length B.length a b ‖z‖ n)) ∈ W :=
                Ival.mem_mul hTnorm hCmem
              have hWle : ‖cpfqTerm A.length B.length a b z n‖
                  * (cpfqRatio A.length B.length a b ‖z‖ n
                    / (1 - cpfqRatio A.length B.length a b ‖z‖ n))
                  ≤ ((h.toRat : ℚ) : ℝ) := by
                have hle := (Ival.mem_def.mp hWmem).2
                rw [hW] at hle
                rw [Ival.leHi_some] at hle
                rwa [Dy.toReal_def] at hle
              have htail := cpfqTail_bound A.length B.length a b z n
                hpq' hBpos' hR
              have hrad : ‖cpfqComplex A.length B.length a b z
                  - (Finset.range (n + 1)).sum
                    (fun j => cpfqTerm A.length B.length a b z j)‖
                  ≤ ((h.toRat : ℚ) : ℝ) :=
                le_trans htail hWle
              have hdiff := mem_cpfqDisc c hrad
              have hpeq : cpfqComplex A.length B.length a b z
                  = (Finset.range (n + 1)).sum
                      (fun j => cpfqTerm A.length B.length a b z j)
                    + (cpfqComplex A.length B.length a b z
                      - (Finset.range (n + 1)).sum
                        (fun j => cpfqTerm A.length B.length a b z j)) := by
                ring
              rw [hpeq]
              exact CBox.mem_add hSmem hdiff
          · rw [ite_eq_right hRlt]
            show cpfqComplex A.length B.length a b z ∈ CBox.top
            exact CBox.mem_top _
  | some r =>
    obtain ⟨i₀, m⟩ := r
    show cpfqComplex p q a b z ∈
      (if cpfqGuard B n then cpfqFiniteBox c A B A.length B.length Z m else CBox.top)
    cases hguard : cpfqGuard B n with
    | false =>
      show cpfqComplex p q a b z ∈ CBox.top
      exact CBox.mem_top _
    | true =>
      rw [← hlenA, ← hlenB]
      have hmA' : ∀ i : Nat, i < A.length → a (0 + i) ∈ A.getD i CBox.top := by
        intro i hi
        rw [Nat.zero_add]
        exact hmA i hi
      have hok := cpfqFindTerm_ok a A 0 hmA' _ hft i₀ m rfl
      obtain ⟨hlt, hval⟩ := hok
      have hi₀ : i₀ < A.length := by omega
      exact cpfqFinite_sound c hc _ _ a b A B Z z m i₀ hmA hmB hmZ hi₀ hval

/-- complex guard facts give the bridge hypothesis: bottoms avoid nonpositive integers. -/
theorem hb_of_cguard (b : ℕ → ℂ) (q n : Nat)
    (hpos : ∀ j : Nat, j < q → 0 < (b j + (n : ℂ)).re)
    (hne : ∀ j : Nat, j < q → ∀ k : Nat, k < n → b j + (k : ℂ) ≠ 0) :
    ∀ j : Nat, j < q → ∀ m : ℕ, b j ≠ -(m : ℂ) := by
  intro j hj m heq
  by_cases hm : m < n
  · exact hne j hj m hm (by rw [heq]; ring)
  · exfalso
    have hle : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : n ≤ m)
    have h1 := hpos j hj
    rw [heq, Complex.add_re, Complex.neg_re, Complex.natCast_re, Complex.natCast_re] at h1
    linarith
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

lemma ascPochhammer_eval_add_right (x : ℂ) (k m : ℕ) :
    (ascPochhammer ℂ (k + m)).eval x =
      (ascPochhammer ℂ k).eval x * (ascPochhammer ℂ m).eval (x + k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, ascPochhammer_succ_right, ascPochhammer_succ_right]
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_natCast, ih, Nat.cast_add]
    ring

lemma ascPochhammer_eval_succ_left (x : ℂ) (k : ℕ) :
    (ascPochhammer ℂ (k + 1)).eval x = x * (ascPochhammer ℂ k).eval (x + 1) := by
  have h := ascPochhammer_eval_add_right x 1 k
  rw [Nat.add_comm 1 k] at h
  simpa using h

lemma kummer_pochhammer_sum (n : ℕ) : ∀ (a b : ℂ),
    ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℂ) * (-1 : ℂ) ^ k *
        (ascPochhammer ℂ k).eval (b - a) *
        (ascPochhammer ℂ (n - k)).eval (b + k) =
      (ascPochhammer ℂ n).eval a := by
  induction n with
  | zero =>
    intro a b
    simp
  | succ n ih =>
    intro a b
    let F := fun (m k : ℕ) (x y : ℂ) =>
      (Nat.choose m k : ℂ) * (-1 : ℂ) ^ k *
        (ascPochhammer ℂ k).eval (y - x) *
        (ascPochhammer ℂ (m - k)).eval (y + k)
    let G := fun k : ℕ =>
      (Nat.choose n k : ℂ) * (-1 : ℂ) ^ k *
        (ascPochhammer ℂ k).eval (b - a) *
        (ascPochhammer ℂ (n + 1 - k)).eval (b + (k : ℕ))
    change ∑ k ∈ Finset.range (n + 1 + 1), F (n + 1) k a b = (ascPochhammer ℂ (n + 1)).eval a
    rw [Finset.sum_range_succ' (fun k => F (n + 1) k a b) (n + 1)]
    have hsplit : ∀ k ∈ Finset.range (n + 1),
        F (n + 1) (k + 1) a b = G (k + 1) + (-(b - a)) * F n k a (b + 1) := by
      intro k _
      dsimp [F, G]
      rw [Nat.choose_succ_succ n k, Nat.succ_sub_succ_eq_sub,
        ascPochhammer_eval_succ_left (b - a) k, pow_succ]
      push_cast
      rw [show b - a + 1 = b + 1 - a by ring, show b + ((k : ℂ) + 1) = b + 1 + k by ring]
      ring
    have hA0 : F (n + 1) 0 a b = G 0 := by dsimp [F, G]; simp
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum,
      ih a (b + 1), hA0, add_right_comm, ← Finset.sum_range_succ' G (n + 1)]
    have hGn1 : G (n + 1) = 0 := by
      dsimp [G]
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)]
      simp
    rw [Finset.sum_range_succ G (n + 1), hGn1, add_zero]
    have hGstep : ∀ k ∈ Finset.range (n + 1),
        G k = (b + n) * F n k a b := by
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      dsimp [G, F]
      rw [Nat.succ_sub hkn, ascPochhammer_succ_right]
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_natCast]
      rw [Nat.cast_sub hkn]
      ring
    rw [Finset.sum_congr rfl hGstep, ← Finset.mul_sum, ih a b, ascPochhammer_succ_right]
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_natCast]
    ring

lemma ascPochhammer_eval_ne_zero {b : ℂ} (hb : ∀ m : ℕ, b + m ≠ 0) (k : ℕ) :
    (ascPochhammer ℂ k).eval b ≠ 0 := by
  rw [ascPochhammer_eval_eq_prod_range]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => hb j

lemma kummer_coeff_sum (a b z : ℂ) (hb : ∀ m : ℕ, b + m ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (z ^ k / (Nat.factorial k : ℂ)) *
        (HGFunCoeff {b - a} {b} (n - k) * (-z) ^ (n - k)) =
      HGFunCoeff {a} {b} n * z ^ n := by
  rw [← Finset.sum_range_reflect]
  simp only [Nat.add_succ_sub_one, add_zero]
  have hsub : ∀ k ∈ Finset.range (n + 1), n - (n - k) = k :=
    fun k hk => Nat.sub_sub_self (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hb' : ∀ j ∈ ({b} : Multiset ℂ), ∀ m : ℕ, j ≠ -(m : ℂ) := by
    intro j hj m heq
    rw [Multiset.mem_singleton] at hj
    exact hb m (by rw [← hj, heq]; ring)
  have hbn : (ascPochhammer ℂ n).eval b ≠ 0 := ascPochhammer_eval_ne_zero hb n
  have hfacn : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [HGFunCoeff_eq_ascPochhammer {a} hb' n]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (z ^ (n - k) / (Nat.factorial (n - k) : ℂ)) *
        (HGFunCoeff {b - a} {b} (n - (n - k)) * (-z) ^ (n - (n - k))) =
      ((Nat.choose n k : ℂ) * (-1 : ℂ) ^ k *
        (ascPochhammer ℂ k).eval (b - a) *
        (ascPochhammer ℂ (n - k)).eval (b + k)) * z ^ n /
        ((Nat.factorial n : ℂ) * (ascPochhammer ℂ n).eval b) := by
    intro k hk
    rw [hsub k hk]
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [HGFunCoeff_eq_ascPochhammer {b - a} hb' k]
    simp only [Multiset.map_singleton, Multiset.prod_singleton]
    have hbk : (ascPochhammer ℂ k).eval b ≠ 0 := ascPochhammer_eval_ne_zero hb k
    have hfack : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hfacnk : ((Nat.factorial (n - k) : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - k)
    have hchoose : (Nat.choose n k : ℂ) * (Nat.factorial k : ℂ) * (Nat.factorial (n - k) : ℂ) =
        (Nat.factorial n : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
    have hpoch : (ascPochhammer ℂ n).eval b =
        (ascPochhammer ℂ k).eval b * (ascPochhammer ℂ (n - k)).eval (b + k) := by
      have h1 := ascPochhammer_eval_add_right b k (n - k)
      rwa [Nat.add_sub_of_le hkn] at h1
    have hpow : z ^ (n - k) * (-z) ^ k = (-1 : ℂ) ^ k * z ^ n := by
      rw [neg_eq_neg_one_mul z, mul_pow, ← mul_assoc, mul_comm (z ^ (n - k)),
        mul_assoc, ← pow_add, Nat.sub_add_cancel hkn]
    calc (z ^ (n - k) / (Nat.factorial (n - k) : ℂ)) *
          ((ascPochhammer ℂ k).eval (b - a) / ((Nat.factorial k : ℂ) * (ascPochhammer ℂ k).eval b) * (-z) ^ k)
        = (z ^ (n - k) * (-z) ^ k) * (ascPochhammer ℂ k).eval (b - a) /
            ((Nat.factorial k : ℂ) * (Nat.factorial (n - k) : ℂ) * (ascPochhammer ℂ k).eval b) := by ring
      _ = ((-1 : ℂ) ^ k * z ^ n) * (ascPochhammer ℂ k).eval (b - a) /
            ((Nat.factorial k : ℂ) * (Nat.factorial (n - k) : ℂ) * (ascPochhammer ℂ k).eval b) := by rw [hpow]
      _ = ((Nat.choose n k : ℂ) * (-1 : ℂ) ^ k *
            (ascPochhammer ℂ k).eval (b - a) *
            (ascPochhammer ℂ (n - k)).eval (b + k)) * z ^ n /
            ((Nat.factorial n : ℂ) * (ascPochhammer ℂ n).eval b) := by
            rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero hfack hfacnk) hbk)
              (mul_ne_zero hfacn hbn), ← hchoose, hpoch]
            ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Finset.sum_mul,
    kummer_pochhammer_sum n a b, div_mul_eq_mul_div]

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
`pfqReal` at every real point `z`. -/
theorem HGFun_ofReal_eq_pfqReal (p q : Nat) (a b : ℕ → ℝ) (z : ℝ)
    (hb : ∀ j : ℕ, j < q → ∀ m : ℕ, (b j : ℂ) ≠ -(m : ℂ))
    (hnp : ¬ IsPfaffRegime ((Multiset.range p).map (fun i => (a i : ℂ)))
      ((Multiset.range q).map (fun j => (b j : ℂ))) (z : ℂ) := by not_pfaff_tac) :
    HGFun ((Multiset.range p).map (fun i => (a i : ℂ)))
        ((Multiset.range q).map (fun j => (b j : ℂ))) (z : ℂ)
      = ((Lynth.Interval.Fns.pfqReal p q a b z : ℝ) : ℂ) := by
  rw [HGFun_eq_tsum _ _ _ hnp]
  unfold Lynth.Interval.Fns.pfqReal
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun k => HGFunCoeff_mul_pow_ofReal p q a b z k hb

/-- LIST BRIDGE (ported from `/tmp/pfq_thm_proof.lean`): `HGFun` over coerced
lists agrees with `pfqReal` over the list elements. Consumed by `HGFunL_sound`. -/
theorem HGFun_coe_list_eq_pfqReal (ar br : List ℝ) (zr : ℝ)
    (hb : ∀ j : Nat, j < br.length → ∀ m : ℕ, (br.getD j 0 : ℂ) ≠ -(m : ℂ))
    (hnp : ¬ IsPfaffRegime (↑(ar.map Complex.ofReal) : Multiset ℂ)
      (↑(br.map Complex.ofReal) : Multiset ℂ) (zr : ℂ) := by not_pfaff_tac) :
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
  rw [hl ar, hl br] at hnp ⊢
  exact HGFun_ofReal_eq_pfqReal _ _ _ _ zr hb hnp

/-- BRIDGE (coefficients, complex): at parameters with no bottom
parameter a nonpositive integer, the `k`-th term of the (Γ-normalized)
series `HGFun` is the complex mirror `cpfqTerm`. Mirror
`HGFunCoeff_mul_pow_ofReal` (same Gamma manipulation, over `ℂ`). -/
theorem HGFunCoeff_mul_pow_ofComplex (p q : Nat) (a b : ℕ → ℂ) (z : ℂ) (k : ℕ)
    (hb : ∀ j : Nat, j < q → ∀ m : ℕ, b j ≠ -(m : ℂ)) :
    HGFunCoeff ((Multiset.range p).map a) ((Multiset.range q).map b) k * z ^ k
      = Lynth.Interval.Fns.cpfqTerm p q a b z k := by
  have hG : ∀ j ∈ Finset.range q, Complex.Gamma (b j + k)
      = Complex.Gamma (b j) * ∏ i ∈ Finset.range k, (b j + (i : ℂ)) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have hne : Complex.Gamma (b j) ≠ 0 := Complex.Gamma_ne_zero (hb j hj')
    rw [← ascPochhammer_eval_eq_prod_range, ← Complex.Gamma_add_nat_div_Gamma_eq _ (hb j hj')]
    field_simp
  have hGne : ∏ j ∈ Finset.range q, Complex.Gamma (b j) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j hj => Complex.Gamma_ne_zero (hb j (Finset.mem_range.1 hj))
  have hm : ∀ {R : Type} [CommMonoid R] (n : ℕ) (f : ℕ → R),
      ((Multiset.range n).map f).prod = ∏ i ∈ Finset.range n, f i := fun _ _ => rfl
  unfold HGFunCoeff Complex.regularizedHGFunCoeff Lynth.Interval.Fns.cpfqTerm
  simp only [Multiset.map_map, Function.comp_def, hm]
  rw [Finset.prod_congr rfl hG, Finset.prod_mul_distrib]
  simp only [ascPochhammer_eval_eq_prod_range]
  field_simp

/-- FUNCTION BRIDGE (complex): `HGFun` over range-mapped parameters agrees
with the complex mirror `cpfqComplex`. -/
theorem HGFun_eq_cpfqComplex (p q : Nat) (a b : ℕ → ℂ) (z : ℂ)
    (hb : ∀ j : Nat, j < q → ∀ m : ℕ, b j ≠ -(m : ℂ))
    (hnp : ¬ IsPfaffRegime ((Multiset.range p).map a) ((Multiset.range q).map b) z := by not_pfaff_tac) :
    HGFun ((Multiset.range p).map a) ((Multiset.range q).map b) z
      = Lynth.Interval.Fns.cpfqComplex p q a b z := by
  rw [HGFun_eq_tsum _ _ _ hnp]
  unfold Lynth.Interval.Fns.cpfqComplex
  refine tsum_congr fun k => ?_
  exact HGFunCoeff_mul_pow_ofComplex p q a b z k hb

/-- LIST BRIDGE (complex): `HGFun` over coerced lists agrees with
`cpfqComplex` over the list elements. Consumed by `HGFunL_sound_complex`. -/
theorem HGFun_coe_list_eq_cpfqComplex (ar br : List ℂ) (zr : ℂ)
    (hb : ∀ j : Nat, j < br.length → ∀ m : ℕ, (br.getD j 0) ≠ -(m : ℂ))
    (hnp : ¬ IsPfaffRegime (↑ar : Multiset ℂ) (↑br : Multiset ℂ) zr := by not_pfaff_tac) :
    Complex.HGFun (↑ar : Multiset ℂ) (↑br : Multiset ℂ) zr
      = Lynth.Interval.Fns.cpfqComplex ar.length br.length
        (fun i => ar.getD i 0) (fun j => br.getD j 0) zr := by
  have hl : ∀ l : List ℂ, (↑l : Multiset ℂ)
      = (Multiset.range l.length).map (fun i => l.getD i 0) := by
    intro l
    rw [Multiset.range, Multiset.map_coe, Multiset.coe_eq_coe]
    apply List.Perm.of_eq
    apply List.ext_getElem (by simp)
    intro n h1 _
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]
  rw [hl ar, hl br] at hnp ⊢
  exact HGFun_eq_cpfqComplex _ _ _ _ zr hb hnp

/-- Pfaff transformation (DLMF 15.8.1): `2F1(a;b;c;z) = (1-z)^{-a} · 2F1(a,c-b;c;z/(z-1))`,
valid left of `Re z = -1` in `IsPfaffRegime`. -/
theorem HGFun_pfaff (a b c z : ℂ) (hz : z.re < -1)
    (ha : 0 < a.re) (hb : 0 < b.re) (hle : cplxLe a b) :
    Complex.HGFun (↑[a, b] : Multiset ℂ) (↑[c] : Multiset ℂ) z
      = (1 - z) ^ (-a) * Complex.HGFun (↑[a, c - b] : Multiset ℂ) (↑[c] : Multiset ℂ)
        (z / (z - 1)) :=
  HGFun_pfaff_eq a b c z hz ha hb hle

/-- Kummer transformation: `1F1(a;b;z) = e^z · 1F1(b-a;b;-z)` (entire). -/
theorem HGFun_kummer (a b z : ℂ) (hb : ∀ m : ℕ, b + m ≠ 0) :
    Complex.HGFun (↑[a] : Multiset ℂ) (↑[b] : Multiset ℂ) z
      = Complex.exp z * Complex.HGFun (↑[b - a] : Multiset ℂ) (↑[b] : Multiset ℂ) (-z) := by
  have h1 : (↑[a] : Multiset ℂ) = {a} := rfl
  have h2 : (↑[b] : Multiset ℂ) = {b} := rfl
  have h3 : (↑[b - a] : Multiset ℂ) = {b - a} := rfl
  rw [h1, h2, h3, HGFun_eq_tsum {a} {b} z, HGFun_eq_tsum {b - a} {b} (-z),
    Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  have hf : Summable fun k : ℕ => ‖z ^ k / (Nat.factorial k : ℂ)‖ := by
    have h := Real.summable_pow_div_factorial ‖z‖
    refine h.congr fun k => ?_
    rw [norm_div, norm_pow, Complex.norm_natCast]
  have hg : Summable fun k : ℕ => ‖HGFunCoeff {b - a} {b} k * (-z) ^ k‖ := by
    have hrad : (-z) ∈ Metric.eball 0 (regularizedHGFunSeries {b - a} {b}).radius := by
      rw [Metric.mem_eball, Complex.radius_regularizedHGFunSeries_eq_top (by simp)]
      exact edist_lt_top (-z) 0
    have hs := (regularizedHGFunSeries {b - a} {b}).summable_norm_apply hrad
    have hs' := hs.mul_left ‖(({b} : Multiset ℂ).map Gamma).prod‖
    refine hs'.congr fun k => ?_
    rw [← norm_mul, HGFunCoeff_def, mul_assoc]
    congr 2
    rw [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg]
  exact (tsum_congr (kummer_coeff_sum a b z hb)).symm

end Complex
namespace Lynth.Interval.Fns

/-! ### 2F1/1F1 transform drivers (FLINT `2f1_choose` + Kummer).

Pfaff and Kummer need no Gamma factors, so they compose the existing
cores (`pfqCoreIval` / `cpfqCoreBox`, `rpowIval`, `expIval`, cpow-style
boxes). Heavier connection formulas (2F1 terms 2–5) and the `z ≈ 1` corner
stay on the direct path (top on failure) — see `/tmp/hyperc`.
* Pfaff: `2F1(a;b;c;z) = (1-z)^{-a} · 2F1(a,c-b;c;z/(z-1))`, used when the
  direct series does not terminate and `|z/(z-1)| < |z|` at midpoints with
  `Re z < -1` (mirrors FLINT's `mag[1] < mag[0]` pick).
* Kummer: `1F1(a;b;z) = e^z · 1F1(b-a;b;-z)`, used when the direct series
  does not terminate but the transformed one does (`b - a = -m`, `m ≤ n`).
Both fire only when the direct engine would not close exactly, so existing
passing tests keep their paths unless the transform strictly applies. -/

theorem ival_lo_le {X : Ival} {x : ℝ} {lo : Dy} (hm : x ∈ X) (hlo : X.lo = some lo) :
    ((lo.toRat : ℚ) : ℝ) ≤ x := by
  have h := (Ival.mem_def.mp hm).1
  rw [hlo, Ival.loLe_some, Dy.toReal_def] at h
  exact h

theorem ival_le_hi {X : Ival} {x : ℝ} {hi : Dy} (hm : x ∈ X) (hhi : X.hi = some hi) :
    x ≤ ((hi.toRat : ℚ) : ℝ) := by
  have h := (Ival.mem_def.mp hm).2
  rw [hhi, Ival.leHi_some, Dy.toReal_def] at h
  exact h

theorem forall2_singleton {α β : Type _} {R : α → β → Prop} {x₀ : α} {ys : List β}
    (h : List.Forall₂ R [x₀] ys) :
    ∃ y₀, ys = [y₀] ∧ R x₀ y₀ := by
  cases h with
  | cons h1 h2 =>
    cases h2
    exact ⟨_, rfl, h1⟩

theorem forall2_pair {α β : Type _} {R : α → β → Prop} {x₀ x₁ : α} {ys : List β}
    (h : List.Forall₂ R [x₀, x₁] ys) :
    ∃ y₀ y₁, ys = [y₀, y₁] ∧ R x₀ y₀ ∧ R x₁ y₁ := by
  cases h with
  | cons h1 h2 =>
    cases h2 with
    | cons h3 h4 =>
      cases h4
      exact ⟨_, _, rfl, h1, h3⟩

theorem forall2_singleton_right {α β : Type _} {R : α → β → Prop} {xs : List α} {y₀ : β}
    (h : List.Forall₂ R xs [y₀]) :
    ∃ x₀, xs = [x₀] ∧ R x₀ y₀ := by
  cases h with
  | cons h1 h2 =>
    cases h2
    exact ⟨_, rfl, h1⟩

theorem forall2_pair_right {α β : Type _} {R : α → β → Prop} {xs : List α} {y₀ y₁ : β}
    (h : List.Forall₂ R xs [y₀, y₁]) :
    ∃ x₀ x₁, xs = [x₀, x₁] ∧ R x₀ y₀ ∧ R x₁ y₁ := by
  cases h with
  | cons h1 h2 =>
    cases h2 with
    | cons h3 h4 =>
      cases h4
      exact ⟨_, _, rfl, h1, h3⟩

theorem forall2_mem_getD {A : List CBox} {a : List ℂ}
    (h : List.Forall₂ (Ty.Mem .cplx) A a) :
    A.length = a.length ∧ ∀ i : Nat, i < A.length → a.getD i 0 ∈ A.getD i CBox.top := by
  induction h with
  | nil => exact ⟨rfl, fun i hi => by simp at hi⟩
  | cons h1 h2 ih =>
    refine ⟨congrArg (· + 1) ih.1, fun i hi => ?_⟩
    cases i with
    | zero => exact h1
    | succ i =>
      simp only [List.length_cons] at hi
      exact ih.2 i (by omega)

/-- Pfaff for real series values (follows `Complex.HGFun_pfaff` via the
ofReal bridge `HGFun_coe_list_eq_pfqReal`). -/
theorem pfqReal_pfaff (a₀ a₁ b₀ z : ℝ) (hz : z < -1)
    (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hle : a₀ ≤ a₁)
    (hb : ∀ m : ℕ, b₀ + m ≠ 0) :
    Complex.HGFun (↑[(a₀ : ℂ), (a₁ : ℂ)] : Multiset ℂ) (↑[(b₀ : ℂ)] : Multiset ℂ) (z : ℂ)
      = (((1 - z) ^ (-a₀) * pfqReal 2 1 (fun i => [a₀, b₀ - a₁].getD i 0)
        (fun j => [b₀].getD j 0) (z / (z - 1)) : ℝ) : ℂ) := by
  have hz' : (z : ℂ).re < -1 := by simpa using hz
  have ha₀' : 0 < (a₀ : ℂ).re := by simpa using ha₀
  have ha₁' : 0 < (a₁ : ℂ).re := by simpa using ha₁
  have hle' : Complex.cplxLe (a₀ : ℂ) (a₁ : ℂ) := by
    rcases lt_or_eq_of_le hle with hlt | rfl
    · exact Or.inl (by simpa using hlt)
    · exact Or.inr ⟨rfl, le_rfl⟩
  rw [Complex.HGFun_pfaff (a₀ : ℂ) (a₁ : ℂ) (b₀ : ℂ) (z : ℂ) hz' ha₀' ha₁' hle']
  have hpos : 0 ≤ 1 - z := by linarith
  have hpow : ((1 : ℂ) - (z : ℂ)) ^ (-(a₀ : ℂ)) = (((1 - z) ^ (-a₀) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_neg,
      Complex.ofReal_cpow hpos]
  have hb' : ∀ j : Nat, j < ([b₀] : List ℝ).length → ∀ m : ℕ, (([b₀].getD j 0 : ℝ) : ℂ) ≠ -(m : ℂ) := by
    intro j hj m h
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    simp only [List.getD_cons_zero] at h
    exact hb m (by exact_mod_cast (by linear_combination h : (b₀ : ℂ) + m = 0))
  have hnp : ¬ Complex.IsPfaffRegime
      (↑(([a₀, b₀ - a₁] : List ℝ).map Complex.ofReal) : Multiset ℂ)
      (↑(([b₀] : List ℝ).map Complex.ofReal) : Multiset ℂ)
      (((z / (z - 1) : ℝ) : ℂ)) := by
    apply Complex.not_isPfaffRegime_of_re_ge
    have hre := Complex.div_sub_one_re_pos hz'
    have heq : ((z / (z - 1) : ℝ) : ℂ) = (z : ℂ) / ((z : ℂ) - 1) := by push_cast; rfl
    rw [heq]
    linarith
  have hbridge := Complex.HGFun_coe_list_eq_pfqReal [a₀, b₀ - a₁] [b₀] (z / (z - 1)) hb' hnp
  simp only [List.map_cons, List.map_nil, Complex.ofReal_sub, List.length_cons,
    List.length_nil] at hbridge
  have hw : (z : ℂ) / ((z : ℂ) - 1) = ((z / (z - 1) : ℝ) : ℂ) := by push_cast; rfl
  rw [hpow, hw, hbridge, Complex.ofReal_mul]

/-- Kummer for real series values (follows `Complex.HGFun_kummer` via the
ofReal bridge). -/
theorem pfqReal_kummer (a₀ b₀ z : ℝ)
    (hb : ∀ m : ℕ, b₀ + m ≠ 0) :
    pfqReal 1 1 (fun i => [a₀].getD i 0) (fun j => [b₀].getD j 0) z
      = Real.exp z * pfqReal 1 1 (fun i => [b₀ - a₀].getD i 0) (fun j => [b₀].getD j 0) (-z) := by
  have hb' : ∀ j : Nat, j < ([b₀] : List ℝ).length → ∀ m : ℕ, (([b₀].getD j 0 : ℝ) : ℂ) ≠ -(m : ℂ) := by
    intro j hj m h
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    simp only [List.getD_cons_zero] at h
    exact hb m (by exact_mod_cast (by linear_combination h : (b₀ : ℂ) + m = 0))
  have hb'' : ∀ m : ℕ, (b₀ : ℂ) + m ≠ 0 := fun m => by exact_mod_cast hb m
  have h1 := Complex.HGFun_coe_list_eq_pfqReal [a₀] [b₀] z hb'
    (Complex.not_isPfaffRegime_of_card_a (by simp))
  have h2 := Complex.HGFun_coe_list_eq_pfqReal [b₀ - a₀] [b₀] (-z) hb'
    (Complex.not_isPfaffRegime_of_card_a (by simp))
  simp only [List.map_cons, List.map_nil, Complex.ofReal_sub, List.length_cons,
    List.length_nil] at h1 h2
  have hk := Complex.HGFun_kummer (a₀ : ℂ) (b₀ : ℂ) (z : ℂ) hb''
  rw [← Complex.ofReal_neg] at hk
  rw [h1, h2, ← Complex.ofReal_exp, ← Complex.ofReal_mul] at hk
  exact Complex.ofReal_injective hk

/-- midpoint squared modulus of a real interval (`none` if unbounded). -/
def ivalMidSq (X : Ival) : Option ℚ :=
  match X.lo, X.hi with
  | some lo, some hi =>
    let m := (lo.toRat + hi.toRat) / 2
    some (m * m)
  | _, _ => none

/-- Pfaff-transformed problem, when the direct 2F1 does not terminate and
`|z/(z-1)| < |z|` with `Re z < -1`. -/
def pfqPfaffArgs (c : Ctx) (A B : List Ival) (Z : Ival) (n : Nat) :
    Option (List Ival × List Ival × Ival × Ival) :=
  match A, B with
  | [A0, A1], [B0] =>
    match pfqFindTerm [A0, A1] 0, ivalMidSq Z, Z.hi, A0.lo, A0.hi, A1.lo with
    | none, some mz, some zhi, some a0lo, some a0hi, some a1lo =>
      if pfqGuard [B0] n ∧ 0 < a0lo.toRat ∧ 0 < a1lo.toRat ∧ a0hi.toRat ≤ a1lo.toRat then
        let W := Ival.div c.prec Z (Ival.sub c.prec Z (Ival.ofRat c.prec 1))
        match ivalMidSq W with
        | some mw =>
          if mw < mz ∧ zhi.toRat < -1 then
            let P := rpowIval c (Ival.sub c.prec (Ival.ofRat c.prec 1) Z)
              (Ival.neg A0)
            some ([A0, Ival.sub c.prec B0 A1], [B0], W, P)
          else none
        | none => none
      else none
    | _, _, _, _, _, _ => none
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
      if pfqGuard [B0] n then
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
      else none
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
    (hArgs : pfqPfaffArgs c Ar Br Zr n = some (A', B', W, P)) :
    y ∈ (⟨Ival.mul c.prec P (pfqCoreIval c A' B' W n),
      Ival.ofRat c.prec 0⟩ : CBox) := by
  rcases Ar with _ | ⟨A0, _ | ⟨A1, _ | _⟩⟩ <;> try (simp [pfqPfaffArgs] at hArgs; done)
  rcases Br with _ | ⟨B0, _ | _⟩ <;> try (simp [pfqPfaffArgs] at hArgs; done)
  unfold pfqPfaffArgs at hArgs
  cases hft : pfqFindTerm [A0, A1] 0 with
  | some _ => simp [hft] at hArgs
  | none =>
    cases hmz : ivalMidSq Zr with
    | none => simp [hft, hmz] at hArgs
    | some mz =>
      cases hzhi : Zr.hi with
      | none => simp [hft, hmz, hzhi] at hArgs
      | some zhi =>
        cases ha0lo : A0.lo with
        | none => simp [hft, hmz, hzhi, ha0lo] at hArgs
        | some a0lo =>
          cases ha0hi : A0.hi with
          | none => simp [hft, hmz, hzhi, ha0lo, ha0hi] at hArgs
          | some a0hi =>
            cases ha1lo : A1.lo with
            | none => simp [hft, hmz, hzhi, ha0lo, ha0hi, ha1lo] at hArgs
            | some a1lo =>
              simp only [hft, hmz, hzhi, ha0lo, ha0hi, ha1lo] at hArgs
              split_ifs at hArgs with hg1
              rcases hmw' : ivalMidSq (Ival.div c.prec Zr (Ival.sub c.prec Zr (Ival.ofRat c.prec 1))) with _ | mw
              · simp [hmw'] at hArgs
              · simp only [hmw'] at hArgs
                split_ifs at hArgs with hg2
                rcases hArgs with ⟨⟩
                obtain ⟨CA0, CA1, rfl, hExA0, hExA1⟩ := forall2_pair_right hExA
                obtain ⟨CB0, rfl, hExB0⟩ := forall2_singleton_right hExB
                obtain ⟨a₀, a₁, rfl, hmemCA0, hmemCA1⟩ := forall2_pair hhA
                obtain ⟨b₀, rfl, hmemCB0⟩ := forall2_singleton hhB
                obtain ⟨ha0_re, ha0_im⟩ := realOfZeroIm_ok CA0 A0 a₀ hExA0 hmemCA0
                obtain ⟨ha1_re, ha1_im⟩ := realOfZeroIm_ok CA1 A1 a₁ hExA1 hmemCA1
                obtain ⟨hb0_re, hb0_im⟩ := realOfZeroIm_ok CB0 B0 b₀ hExB0 hmemCB0
                obtain ⟨hz_re, hz_im⟩ := realOfZeroIm_ok Z Zr z hZr hhZ
                have ha0_eq : a₀ = (a₀.re : ℂ) := (ofReal_of_re ha0_im).symm
                have ha1_eq : a₁ = (a₁.re : ℂ) := (ofReal_of_re ha1_im).symm
                have hb0_eq : b₀ = (b₀.re : ℂ) := (ofReal_of_re hb0_im).symm
                have hz_eq : z = (z.re : ℂ) := (ofReal_of_re hz_im).symm
                have hz_lt : z.re < -1 := by
                  have h1 := ival_le_hi hz_re hzhi
                  have h2 : ((zhi.toRat : ℚ) : ℝ) < -1 := by exact_mod_cast hg2.2
                  linarith
                have ha0_pos : 0 < a₀.re := by
                  have h1 := ival_lo_le ha0_re ha0lo
                  have h2 : (0 : ℝ) < ((a0lo.toRat : ℚ) : ℝ) := by exact_mod_cast hg1.2.1
                  linarith
                have ha1_pos : 0 < a₁.re := by
                  have h1 := ival_lo_le ha1_re ha1lo
                  have h2 : (0 : ℝ) < ((a1lo.toRat : ℚ) : ℝ) := by exact_mod_cast hg1.2.2.1
                  linarith
                have ha_le : a₀.re ≤ a₁.re := by
                  have h1 := ival_le_hi ha0_re ha0hi
                  have h2 := ival_lo_le ha1_re ha1lo
                  have h3 : ((a0hi.toRat : ℚ) : ℝ) ≤ ((a1lo.toRat : ℚ) : ℝ) := by
                    exact_mod_cast hg1.2.2.2
                  linarith
                have hmB' : ∀ i : Nat, i < ([B0] : List Ival).length →
                    (fun _ => b₀.re) (0 + i) ∈ [B0].getD i Ival.top := by
                  intro i hi
                  have hi0 : i = 0 := by simpa using hi
                  subst hi0
                  exact hb0_re
                obtain ⟨hposB, hneB⟩ := pfqGuard_ok (fun _ => b₀.re) [B0] 0 n hmB' hg1.1
                have hb_ne : ∀ m : ℕ, b₀.re + m ≠ 0 := by
                  intro m hm0
                  have h := hb_of_guard (fun _ => b₀.re) 1 n
                    (fun j hj => by have := hposB j hj; linarith)
                    (fun j hj k hk => hneB j hj k hk) 0 (by decide) m
                  exact h (by exact_mod_cast (by linarith : b₀.re = -(m : ℝ)))
                rw [ha0_eq, ha1_eq, hb0_eq, hz_eq,
                  pfqReal_pfaff a₀.re a₁.re b₀.re z.re hz_lt ha0_pos ha1_pos ha_le hb_ne] at hy
                have h1mem : (1 : ℝ) ∈ Ival.ofRat c.prec 1 := by
                  exact_mod_cast Ival.mem_ofRat c.prec (1 : ℚ)
                have hPmem : (1 - z.re) ^ (-a₀.re) ∈
                    rpowIval c (Ival.sub c.prec (Ival.ofRat c.prec 1) Zr) (Ival.neg A0) :=
                  mem_rpowIval hc (Ival.mem_sub h1mem hz_re) (Ival.mem_neg ha0_re)
                have hWmem : z.re / (z.re - 1) ∈
                    Ival.div c.prec Zr (Ival.sub c.prec Zr (Ival.ofRat c.prec 1)) :=
                  Ival.mem_div hz_re (Ival.mem_sub hz_re h1mem)
                have hmA' : ∀ i : Nat, i < ([A0, Ival.sub c.prec B0 A1] : List Ival).length →
                    [a₀.re, b₀.re - a₁.re].getD i 0 ∈
                      [A0, Ival.sub c.prec B0 A1].getD i Ival.top := by
                  intro i hi
                  rcases i with _ | ⟨_ | i⟩
                  · exact ha0_re
                  · exact Ival.mem_sub hb0_re ha1_re
                  · simp at hi
                have hmB0 : ∀ i : Nat, i < ([B0] : List Ival).length →
                    [b₀.re].getD i 0 ∈ [B0].getD i Ival.top := by
                  intro i hi
                  have hi0 : i = 0 := by simpa using hi
                  subst hi0
                  exact hb0_re
                have hcore := pfqCore_sound c hc 2 1
                  (fun i => [a₀.re, b₀.re - a₁.re].getD i 0)
                  (fun j => [b₀.re].getD j 0)
                  [A0, Ival.sub c.prec B0 A1] [B0]
                  (Ival.div c.prec Zr (Ival.sub c.prec Zr (Ival.ofRat c.prec 1)))
                  (z.re / (z.re - 1)) n rfl rfl hmA' hmB0 hWmem
                have hy_re : y.re ∈ Ival.mul c.prec
                    (rpowIval c (Ival.sub c.prec (Ival.ofRat c.prec 1) Zr) (Ival.neg A0))
                    (pfqCoreIval c [A0, Ival.sub c.prec B0 A1] [B0]
                      (Ival.div c.prec Zr (Ival.sub c.prec Zr (Ival.ofRat c.prec 1))) n) := by
                  rw [hy, Complex.ofReal_re]
                  exact Ival.mem_mul hPmem hcore
                have hy_im : y.im ∈ Ival.ofRat c.prec 0 := by
                  rw [hy, Complex.ofReal_im]
                  exact_mod_cast Ival.mem_ofRat c.prec (0 : ℚ)
                exact CBox.mem_def.mpr ⟨hy_re, hy_im⟩

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
  rcases Ar with _ | ⟨A0, _ | _⟩ <;> try (simp [pfqKummerArgs] at hArgs; done)
  rcases Br with _ | ⟨B0, _ | _⟩ <;> try (simp [pfqKummerArgs] at hArgs; done)
  unfold pfqKummerArgs at hArgs
  cases hft : pfqFindTerm [A0] 0
  swap; · simp [hft] at hArgs
  simp only [hft] at hArgs
  split_ifs at hArgs with hguard
  set D := Ival.sub c.prec B0 A0
  cases hlo : D.lo
  · simp [hlo] at hArgs
  cases hhi : D.hi
  · simp [hlo, hhi] at hArgs
  simp only [hlo, hhi] at hArgs
  split_ifs at hArgs with h1 h2
  rcases hArgs with ⟨⟩
  obtain ⟨CA0, rfl, hExA0⟩ := forall2_singleton_right hExA
  obtain ⟨CB0, rfl, hExB0⟩ := forall2_singleton_right hExB
  obtain ⟨a₀, rfl, hmemCA0⟩ := forall2_singleton hhA
  obtain ⟨b₀, rfl, hmemCB0⟩ := forall2_singleton hhB
  obtain ⟨ha0_re, ha0_im⟩ := realOfZeroIm_ok CA0 A0 a₀ hExA0 hmemCA0
  obtain ⟨hb0_re, hb0_im⟩ := realOfZeroIm_ok CB0 B0 b₀ hExB0 hmemCB0
  obtain ⟨hz_re, hz_im⟩ := realOfZeroIm_ok Z Zr z hZr hhZ
  have ha0_eq : a₀ = (a₀.re : ℂ) := (ofReal_of_re ha0_im).symm
  have hb0_eq : b₀ = (b₀.re : ℂ) := (ofReal_of_re hb0_im).symm
  have hz_eq : z = (z.re : ℂ) := (ofReal_of_re hz_im).symm
  have hmB' : ∀ i : Nat, i < ([B0] : List Ival).length →
      (fun _ => b₀.re) (0 + i) ∈ [B0].getD i Ival.top := by
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    exact hb0_re
  obtain ⟨hposB, hneB⟩ := pfqGuard_ok (fun _ => b₀.re) [B0] 0 n hmB' hguard
  have hb_c : ∀ j : Nat, j < ([b₀.re] : List ℝ).length → ∀ m : ℕ,
      (([b₀.re].getD j 0 : ℝ) : ℂ) ≠ -(m : ℂ) := by
    intro j hj m
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    exact hb_of_guard (fun _ => b₀.re) 1 n
      (fun k hk => by have := hposB k hk; linarith)
      (fun k hk t ht => hneB k hk t ht) 0 (by decide) m
  have hb_ne : ∀ m : ℕ, b₀.re + m ≠ 0 := by
    intro m hm0
    exact hb_c 0 (by simp) m (by exact_mod_cast (by linarith : b₀.re = -(m : ℝ)))
  have hbridge := Complex.HGFun_coe_list_eq_pfqReal [a₀.re] [b₀.re] z.re hb_c
    (Complex.not_isPfaffRegime_of_card_a (by simp))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hbridge
  rw [ha0_eq, hb0_eq, hz_eq, hbridge, pfqReal_kummer a₀.re b₀.re z.re hb_ne] at hy
  have hPmem : Real.exp z.re ∈ expIval c Zr := mem_expIval c hz_re
  have hWmem : -z.re ∈ Ival.neg Zr := Ival.mem_neg hz_re
  have hmA' : ∀ i : Nat, i < ([D] : List Ival).length →
      [b₀.re - a₀.re].getD i 0 ∈ [D].getD i Ival.top := by
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    exact Ival.mem_sub hb0_re ha0_re
  have hmB0 : ∀ i : Nat, i < ([B0] : List Ival).length →
      [b₀.re].getD i 0 ∈ [B0].getD i Ival.top := by
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    exact hb0_re
  have hcore := pfqCore_sound c hc 1 1
    (fun i => [b₀.re - a₀.re].getD i 0) (fun j => [b₀.re].getD j 0)
    [D] [B0] (Ival.neg Zr) (-z.re) n rfl rfl hmA' hmB0 hWmem
  have hy_re : y.re ∈ Ival.mul c.prec (expIval c Zr) (pfqCoreIval c [D] [B0] (Ival.neg Zr) n) := by
    rw [hy, Complex.ofReal_re]
    exact Ival.mem_mul hPmem hcore
  have hy_im : y.im ∈ Ival.ofRat c.prec 0 := by
    rw [hy, Complex.ofReal_im]
    exact_mod_cast Ival.mem_ofRat c.prec (0 : ℚ)
  exact CBox.mem_def.mpr ⟨hy_re, hy_im⟩

/-! ### Complex transform drivers (same FLINT picks, `CBox` arithmetic).

Mirror of the real drivers above: Pfaff when `|z/(z-1)| < |z|` at box
midpoints with `Re z < -1`, Kummer when the direct series does
not terminate but the transformed one does. Prefactors use the `cpow`
pattern (`exp (log · * ·)`, nonzero-modulus gate) mirroring `cpowC.ev`. -/

/-- midpoint squared modulus of a complex box (`none` if unbounded). -/
def cboxMidSq (B : CBox) : Option ℚ :=
  match B.re.lo, B.re.hi, B.im.lo, B.im.hi with
  | some rlo, some rhi, some ilo, some ihi =>
    let rx := (rlo.toRat + rhi.toRat) / 2
    let ix := (ilo.toRat + ihi.toRat) / 2
    some (rx * rx + ix * ix)
  | _, _, _, _ => none

/-- Pfaff-transformed problem, complex version. -/
def cpfqPfaffArgs (c : Ctx) (A B : List CBox) (Z : CBox) (n : Nat) :
    Option (List CBox × List CBox × CBox × CBox) :=
  let one : CBox := ⟨Ival.ofRat c.prec 1, Ival.zero⟩
  match A, B with
  | [A0, A1], [B0] =>
    match cpfqFindTerm [A0, A1] 0, cboxMidSq Z, Z.re.hi,
        A0.re.lo, A0.re.hi, A0.im.hi, A1.re.lo, A1.re.hi, A1.im.lo with
    | none, some mz, some zhi,
        some a0rlo, some a0rhi, some a0ihi, some a1rlo, some a1rhi, some a1ilo =>
      if cpfqGuard [B0] n ∧ 0 < a0rlo.toRat ∧ 0 < a1rlo.toRat ∧
          (a0rhi.toRat < a1rlo.toRat ∨
            (a0rlo = a0rhi ∧ a1rlo = a1rhi ∧ a0rhi = a1rlo ∧ a0ihi.toRat ≤ a1ilo.toRat)) then
        let W := CBox.div c.prec Z (CBox.sub c.prec Z one)
        match cboxMidSq W with
        | some mw =>
          if mw < mz ∧ zhi.toRat < -1 then
            let X1 := CBox.sub c.prec one Z
            let P := cpowC.ev c X1 (CBox.neg A0)
            some ([A0, CBox.sub c.prec B0 A1], [B0], W, P)
          else none
        | none => none
      else none
    | _, _, _, _, _, _, _, _, _ => none
  | _, _ => none

/-- Kummer-transformed problem, complex version. -/
def cpfqKummerArgs (c : Ctx) (A B : List CBox) (Z : CBox) (n : Nat) :
    Option (List CBox × List CBox × CBox × CBox) :=
  match A, B with
  | [A0], [B0] =>
    match cpfqFindTerm [A0] 0 with
    | some _ => none
    | none =>
      if cpfqGuard [B0] n then
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
      else none
  | _, _ => none

/-- complex Pfaff assembly soundness (identity + inner core + prefactor). -/
theorem cpfqPfaff_sound (c : Ctx) (hc : c.Valid)
    (A B : List CBox) (Z : CBox) (a b : List ℂ) (z y : ℂ) (n : Nat)
    (A' B' : List CBox) (W P : CBox)
    (hhA : List.Forall₂ (Ty.Mem .cplx) A a)
    (hhB : List.Forall₂ (Ty.Mem .cplx) B b)
    (hhZ : z ∈ Z)
    (hy : y = Complex.HGFun (↑a : Multiset ℂ) (↑b : Multiset ℂ) z)
    (hArgs : cpfqPfaffArgs c A B Z n = some (A', B', W, P)) :
    y ∈ CBox.mul c.prec P (cpfqCoreBox c A' B' W n) := by
  rcases A with _ | ⟨A0, _ | ⟨A1, _ | _⟩⟩ <;> try (simp [cpfqPfaffArgs] at hArgs; done)
  rcases B with _ | ⟨B0, _ | _⟩ <;> try (simp [cpfqPfaffArgs] at hArgs; done)
  unfold cpfqPfaffArgs at hArgs
  cases hft : cpfqFindTerm [A0, A1] 0 with
  | some _ => simp [hft] at hArgs
  | none =>
    cases hmz : cboxMidSq Z with
    | none => simp [hft, hmz] at hArgs
    | some mz =>
      cases hzhi : Z.re.hi with
      | none => simp [hft, hmz, hzhi] at hArgs
      | some zhi =>
        cases ha0rlo : A0.re.lo with
        | none => simp [hft, hmz, hzhi, ha0rlo] at hArgs
        | some a0rlo =>
          cases ha0rhi : A0.re.hi with
          | none => simp [hft, hmz, hzhi, ha0rlo, ha0rhi] at hArgs
          | some a0rhi =>
            cases ha0ihi : A0.im.hi with
            | none => simp [hft, hmz, hzhi, ha0rlo, ha0rhi, ha0ihi] at hArgs
            | some a0ihi =>
              cases ha1rlo : A1.re.lo with
              | none => simp [hft, hmz, hzhi, ha0rlo, ha0rhi, ha0ihi, ha1rlo] at hArgs
              | some a1rlo =>
                cases ha1rhi : A1.re.hi with
                | none => simp [hft, hmz, hzhi, ha0rlo, ha0rhi, ha0ihi, ha1rlo, ha1rhi] at hArgs
                | some a1rhi =>
                  cases ha1ilo : A1.im.lo with
                  | none => simp [hft, hmz, hzhi, ha0rlo, ha0rhi, ha0ihi, ha1rlo, ha1rhi, ha1ilo] at hArgs
                  | some a1ilo =>
                    simp only [hft, hmz, hzhi, ha0rlo, ha0rhi, ha0ihi, ha1rlo, ha1rhi, ha1ilo] at hArgs
                    split_ifs at hArgs with hg1
                    set one : CBox := ⟨Ival.ofRat c.prec 1, Ival.zero⟩
                    rcases hmw' : cboxMidSq (CBox.div c.prec Z (CBox.sub c.prec Z one)) with _ | mw
                    · simp [hmw'] at hArgs
                    · simp only [hmw'] at hArgs
                      split_ifs at hArgs with hg2
                      rcases hArgs with ⟨⟩
                      obtain ⟨a₀, a₁, rfl, ha0, ha1⟩ := forall2_pair hhA
                      obtain ⟨b₀, rfl, hb0⟩ := forall2_singleton hhB
                      have hz_lt : z.re < -1 := by
                        have h1 := ival_le_hi hhZ.1 hzhi
                        have h2 : ((zhi.toRat : ℚ) : ℝ) < -1 := by exact_mod_cast hg2.2
                        linarith
                      have ha0_pos : 0 < a₀.re := by
                        have h1 := ival_lo_le ha0.1 ha0rlo
                        have h2 : (0 : ℝ) < ((a0rlo.toRat : ℚ) : ℝ) := by exact_mod_cast hg1.2.1
                        linarith
                      have ha1_pos : 0 < a₁.re := by
                        have h1 := ival_lo_le ha1.1 ha1rlo
                        have h2 : (0 : ℝ) < ((a1rlo.toRat : ℚ) : ℝ) := by exact_mod_cast hg1.2.2.1
                        linarith
                      have hle : Complex.cplxLe a₀ a₁ := by
                        rcases hg1.2.2.2 with hlt | ⟨heq0, heq1, heq01, him⟩
                        · left
                          have h1 := ival_le_hi ha0.1 ha0rhi
                          have h2 := ival_lo_le ha1.1 ha1rlo
                          have h3 : ((a0rhi.toRat : ℚ) : ℝ) < ((a1rlo.toRat : ℚ) : ℝ) := by
                            exact_mod_cast hlt
                          linarith
                        · right
                          have hpt0 := dyPointMem ha0.1 ha0rlo (by rwa [← heq0] at ha0rhi)
                          have hpt1 := dyPointMem ha1.1 ha1rlo (by rwa [← heq1] at ha1rhi)
                          have hre_eq : a₀.re = a₁.re := by
                            rw [hpt0, hpt1, heq0, heq01]
                          have him_le : a₀.im ≤ a₁.im := by
                            have h1 := ival_le_hi ha0.2 ha0ihi
                            have h2 := ival_lo_le ha1.2 ha1ilo
                            have h3 : ((a0ihi.toRat : ℚ) : ℝ) ≤ ((a1ilo.toRat : ℚ) : ℝ) := by
                              exact_mod_cast him
                            linarith
                          exact ⟨hre_eq, him_le⟩
                      have hmB' : ∀ i : Nat, i < ([B0] : List CBox).length →
                          (fun _ => b₀) i ∈ [B0].getD i CBox.top := by
                        intro i hi
                        have hi0 : i = 0 := by simpa using hi
                        subst hi0
                        exact hb0
                      obtain ⟨hposB, hneB⟩ := cpfqGuard_ok (fun _ => b₀) [B0] n hmB' hg1.1
                      have hb_c : ∀ j : Nat, j < ([b₀] : List ℂ).length → ∀ m : ℕ,
                          ([b₀].getD j 0) ≠ -(m : ℂ) := by
                        intro j hj m
                        have hj0 : j = 0 := by simpa using hj
                        subst hj0
                        exact hb_of_cguard (fun _ => b₀) 1 n
                          (fun k hk => hposB k hk)
                          (fun k hk t ht => hneB k hk t ht) 0 (by decide) m
                      rw [Complex.HGFun_pfaff a₀ a₁ b₀ z hz_lt ha0_pos ha1_pos hle] at hy
                      have hnp : ¬ Complex.IsPfaffRegime
                          (↑([a₀, b₀ - a₁] : List ℂ) : Multiset ℂ)
                          (↑([b₀] : List ℂ) : Multiset ℂ) (z / (z - 1)) :=
                        Complex.not_isPfaffRegime_of_re_ge
                          (by linarith [Complex.div_sub_one_re_pos hz_lt])
                      rw [Complex.HGFun_coe_list_eq_cpfqComplex [a₀, b₀ - a₁] [b₀] (z / (z - 1))
                        hb_c hnp] at hy
                      have h1mem : (1 : ℂ) ∈ one := by
                        refine ⟨?_, ?_⟩
                        · simpa using (Ival.mem_ofRat c.prec (1 : ℚ))
                        · simpa using Ival.mem_zero
                      have hX1 : 1 - z ∈ CBox.sub c.prec one Z := CBox.mem_sub h1mem hhZ
                      have hPmem : (1 - z) ^ (-a₀) ∈
                          cpowC.ev c (CBox.sub c.prec one Z) (CBox.neg A0) :=
                        cpowC.sound c (1 - z) (-a₀) ((1 - z) ^ (-a₀))
                          (CBox.sub c.prec one Z) (CBox.neg A0) hc rfl hX1 (CBox.mem_neg ha0)
                      have hWmem : z / (z - 1) ∈ CBox.div c.prec Z (CBox.sub c.prec Z one) :=
                        CBox.mem_div hhZ (CBox.mem_sub hhZ h1mem)
                      have hmA' : ∀ i : Nat, i < ([A0, CBox.sub c.prec B0 A1] : List CBox).length →
                          [a₀, b₀ - a₁].getD i 0 ∈
                            [A0, CBox.sub c.prec B0 A1].getD i CBox.top := by
                        intro i hi
                        rcases i with _ | ⟨_ | i⟩
                        · exact ha0
                        · exact CBox.mem_sub hb0 ha1
                        · simp at hi
                      have hmB0 : ∀ i : Nat, i < ([B0] : List CBox).length →
                          [b₀].getD i 0 ∈ [B0].getD i CBox.top := by
                        intro i hi
                        have hi0 : i = 0 := by simpa using hi
                        subst hi0
                        exact hb0
                      have hcore := cpfqCore_sound c hc 2 1
                        (fun i => [a₀, b₀ - a₁].getD i 0) (fun j => [b₀].getD j 0)
                        [A0, CBox.sub c.prec B0 A1] [B0]
                        (CBox.div c.prec Z (CBox.sub c.prec Z one)) (z / (z - 1)) n
                        rfl rfl hmA' hmB0 hWmem
                      rw [hy]
                      exact CBox.mem_mul hPmem hcore

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
  rcases A with _ | ⟨A0, _ | _⟩ <;> try (simp [cpfqKummerArgs] at hArgs; done)
  rcases B with _ | ⟨B0, _ | _⟩ <;> try (simp [cpfqKummerArgs] at hArgs; done)
  unfold cpfqKummerArgs at hArgs
  cases hft : cpfqFindTerm [A0] 0
  swap; · simp [hft] at hArgs
  simp only [hft] at hArgs
  split_ifs at hArgs with hguard
  set D := CBox.sub c.prec B0 A0
  cases hrlo : D.re.lo
  · simp [hrlo] at hArgs
  cases hrhi : D.re.hi
  · simp [hrlo, hrhi] at hArgs
  cases hilo : D.im.lo
  · simp [hrlo, hrhi, hilo] at hArgs
  cases hihi : D.im.hi
  · simp [hrlo, hrhi, hilo, hihi] at hArgs
  simp only [hrlo, hrhi, hilo, hihi] at hArgs
  split_ifs at hArgs with h1 h2
  rcases hArgs with ⟨⟩
  obtain ⟨a₀, rfl, ha0⟩ := forall2_singleton hhA
  obtain ⟨b₀, rfl, hb0⟩ := forall2_singleton hhB
  have hmB' : ∀ i : Nat, i < ([B0] : List CBox).length →
      (fun _ => b₀) i ∈ [B0].getD i CBox.top := by
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    exact hb0
  obtain ⟨hposB, hneB⟩ := cpfqGuard_ok (fun _ => b₀) [B0] n hmB' hguard
  have hb_c : ∀ j : Nat, j < ([b₀] : List ℂ).length → ∀ m : ℕ,
      ([b₀].getD j 0) ≠ -(m : ℂ) := by
    intro j hj m
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    exact hb_of_cguard (fun _ => b₀) 1 n
      (fun k hk => hposB k hk)
      (fun k hk t ht => hneB k hk t ht) 0 (by decide) m
  have hb_ne : ∀ m : ℕ, b₀ + m ≠ 0 := by
    intro m hm0
    exact hb_c 0 (by simp) m (by simp; linear_combination hm0)
  rw [Complex.HGFun_kummer a₀ b₀ z hb_ne,
    Complex.HGFun_coe_list_eq_cpfqComplex [b₀ - a₀] [b₀] (-z) hb_c
      (Complex.not_isPfaffRegime_of_card_a (by simp))] at hy
  have hPmem : Complex.exp z ∈ expBox c Z := mem_expBox c hc hhZ
  have hWmem : -z ∈ CBox.neg Z := CBox.mem_neg hhZ
  have hmA' : ∀ i : Nat, i < ([D] : List CBox).length →
      [b₀ - a₀].getD i 0 ∈ [D].getD i CBox.top := by
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    exact CBox.mem_sub hb0 ha0
  have hmB0 : ∀ i : Nat, i < ([B0] : List CBox).length →
      [b₀].getD i 0 ∈ [B0].getD i CBox.top := by
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    exact hb0
  have hcore := cpfqCore_sound c hc 1 1
    (fun i => [b₀ - a₀].getD i 0) (fun j => [b₀].getD j 0)
    [D] [B0] (CBox.neg Z) (-z) n rfl rfl hmA' hmB0 hWmem
  rw [hy]
  exact CBox.mem_mul hPmem hcore

/-! ### List-based `HGFun` mirror (single registry entry).

Users write `Complex.HGFun` over multisets in goals; the reifier
(`reifyMultisetHGFun?`) normalizes literal spines to lists and targets
`HGFunL` below. The evaluator extracts real parts (imaginary parts must
be exactly zero) and runs the general `pfqCoreIval` core at any lengths. -/

theorem not_isPfaffRegime_of_term (a b : List ℂ) (z : ℂ) (i₀ m : Nat)
    (hi₀ : i₀ < a.length) (hterm : (a.getD i₀ 0).re = -(m : ℝ)) :
    ¬ Complex.IsPfaffRegime (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := by
  intro hPf
  have hmem : a.getD i₀ 0 ∈ (↑a : Multiset ℂ) := by
    rw [getD_of_lt a 0 i₀ hi₀, Multiset.mem_coe]
    exact List.getElem_mem hi₀
  have hpos := hPf.2.1 (a.getD i₀ 0) hmem
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem not_isPfaffRegime_of_cpfqRatio_lt_one (a b : List ℂ) (z : ℂ) (n : Nat)
    (hBpos : ∀ j : Nat, j < b.length → 0 < (b.getD j 0 + (n : ℂ)).re)
    (hR : cpfqRatio a.length b.length (fun i => a.getD i 0) (fun j => b.getD j 0) ‖z‖ n < 1) :
    ¬ Complex.IsPfaffRegime (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := by
  rintro ⟨hz, _, ⟨p, ha, _⟩, ⟨c, hb⟩⟩
  have halen : a.length = 2 := by
    have := congrArg Multiset.card ha
    simpa using this
  have hblen : b.length = 1 := by
    have := congrArg Multiset.card hb
    simpa using this
  have hz1 : 1 < ‖z‖ := by
    have h1 := Complex.abs_re_le_norm z
    have h2 : 1 < |z.re| := by rw [abs_of_neg (by linarith)]; linarith
    linarith
  have hb0 : 0 < ‖b.getD 0 0 + (n : ℂ)‖ :=
    cpfq_norm_pos_of_re_pos (b.getD 0 0 + (n : ℂ)) (hBpos 0 (by omega))
  have hpair : 1 ≤ ‖a.getD 0 0 - b.getD 0 0‖ / ‖b.getD 0 0 + (n : ℂ)‖ + 1 := by
    have : 0 ≤ ‖a.getD 0 0 - b.getD 0 0‖ / ‖b.getD 0 0 + (n : ℂ)‖ :=
      div_nonneg (norm_nonneg _) hb0.le
    linarith
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have htop : (n : ℝ) + 1 ≤ ‖a.getD 1 0‖ + (n : ℝ) + 1 := by
    linarith [norm_nonneg (a.getD 1 0)]
  have hRge : 1 < cpfqRatio a.length b.length (fun i => a.getD i 0) (fun j => b.getD j 0) ‖z‖ n := by
    rw [halen, hblen]
    unfold cpfqRatio
    rw [show min 2 1 = 1 from rfl, Finset.range_one, Finset.prod_singleton,
      Finset.Ico_eq_empty_of_le (by decide : 1 ≤ 2), Finset.prod_empty, one_mul,
      ite_eq_left (rfl : 2 = 1 + 1), div_mul_eq_mul_div, lt_div_iff₀ hn1]
    dsimp only
    have h12 : 1 < ‖z‖ * (‖a.getD 0 0 - b.getD 0 0‖ / ‖b.getD 0 0 + (n : ℂ)‖ + 1) := by nlinarith
    nlinarith
  linarith

theorem not_isPfaffRegime_of_pfqRatio_lt_one (a b : List ℂ) (z : ℂ) (n : Nat)
    (hBpos : ∀ j : Nat, j < b.length → 0 < (b.getD j 0).re + (n : ℝ))
    (hR : pfqRatio a.length b.length (fun i => (a.getD i 0).re) (fun j => (b.getD j 0).re) |z.re| n < 1) :
    ¬ Complex.IsPfaffRegime (↑a : Multiset ℂ) (↑b : Multiset ℂ) z := by
  rintro ⟨hz, _, ⟨p, ha, _⟩, ⟨c, hb⟩⟩
  have halen : a.length = 2 := by
    have := congrArg Multiset.card ha
    simpa using this
  have hblen : b.length = 1 := by
    have := congrArg Multiset.card hb
    simpa using this
  have hz1 : 1 < |z.re| := by rw [abs_of_neg (by linarith)]; linarith
  have hb0 : 0 < (b.getD 0 0).re + (n : ℝ) := hBpos 0 (by omega)
  have hpair : 1 ≤ |(a.getD 0 0).re - (b.getD 0 0).re| / ((b.getD 0 0).re + (n : ℝ)) + 1 := by
    have : 0 ≤ |(a.getD 0 0).re - (b.getD 0 0).re| / ((b.getD 0 0).re + (n : ℝ)) :=
      div_nonneg (abs_nonneg _) hb0.le
    linarith
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have htop : (n : ℝ) + 1 ≤ |(a.getD 1 0).re| + (n : ℝ) + 1 := by
    linarith [abs_nonneg (a.getD 1 0).re]
  have hRge : 1 < pfqRatio a.length b.length (fun i => (a.getD i 0).re) (fun j => (b.getD j 0).re) |z.re| n := by
    rw [halen, hblen]
    unfold pfqRatio
    rw [show min 2 1 = 1 from rfl, Finset.range_one, Finset.prod_singleton,
      Finset.Ico_eq_empty_of_le (by decide : 1 ≤ 2), Finset.prod_empty, one_mul,
      ite_eq_left (rfl : 2 = 1 + 1), div_mul_eq_mul_div, lt_div_iff₀ hn1]
    dsimp only
    have h12 : 1 < |z.re| * (|(a.getD 0 0).re - (b.getD 0 0).re| / ((b.getD 0 0).re + (n : ℝ)) + 1) := by nlinarith
    nlinarith
  linarith

theorem cpfqCoreBox_not_pfaff_or_top (c : Ctx) (hc : c.Valid)
    (a b : List ℂ) (z : ℂ) (A B : List CBox) (XZ : CBox) (n : Nat)
    (hhA : List.Forall₂ (Ty.Mem .cplx) A a)
    (hhB : List.Forall₂ (Ty.Mem .cplx) B b)
    (hhZ : z ∈ XZ) :
    cpfqCoreBox c A B XZ n = CBox.top ∨
      (cpfqGuard B n = true ∧ ¬ Complex.IsPfaffRegime (↑a : Multiset ℂ) (↑b : Multiset ℂ) z) := by
  obtain ⟨hlenA, hmA⟩ := forall2_mem_getD hhA
  obtain ⟨hlenB, hmB⟩ := forall2_mem_getD hhB
  unfold cpfqCoreBox
  cases hft : cpfqFindTerm A 0 with
  | some r =>
    obtain ⟨i₀, m⟩ := r
    cases hguard : cpfqGuard B n with
    | false => left; rfl
    | true =>
      right
      have hmA' : ∀ i : Nat, i < A.length → (fun k => a.getD k 0) (0 + i) ∈ A.getD i CBox.top := by
        intro i hi; simpa using hmA i hi
      obtain ⟨hlt, hval⟩ := cpfqFindTerm_ok (fun k => a.getD k 0) A 0 hmA' _ hft i₀ m rfl
      refine ⟨rfl, not_isPfaffRegime_of_term a b z i₀ m (by omega) ?_⟩
      rw [hval, Complex.neg_re, Complex.natCast_re]
  | none =>
    dsimp only
    by_cases hlen : A.length > B.length + 1
    · left; exact ite_eq_left hlen
    · rw [ite_eq_right hlen]
      cases hguard : cpfqGuard B n with
      | false => left; rfl
      | true =>
        rw [ite_eq_left rfl]
        cases hRhi : (cpfqRBox c A B A.length B.length (CBox.norm c.prec XZ)
          (CBox.norm c.prec (A.getD B.length CBox.top)) n).hi with
        | none => left; rfl
        | some hRD =>
          dsimp only
          by_cases hRlt : hRD.toRat < 1
          · right
            obtain ⟨hpos, _⟩ := cpfqGuard_ok (fun k => b.getD k 0) B n hmB hguard
            have hpq' : A.length ≤ B.length + 1 := by omega
            have hRmem := mem_cpfqR c hc (fun i => a.getD i 0) (fun j => b.getD j 0)
              A B A.length B.length XZ z n rfl rfl hmA hmB hhZ hpq'
            have hle := ival_le_hi hRmem hRhi
            have hlt1 : ((hRD.toRat : ℚ) : ℝ) < 1 := by exact_mod_cast hRlt
            have hR : cpfqRatio a.length b.length (fun i => a.getD i 0) (fun j => b.getD j 0) ‖z‖ n < 1 := by
              rw [← hlenA, ← hlenB]; linarith
            refine ⟨rfl, not_isPfaffRegime_of_cpfqRatio_lt_one a b z n ?_ hR⟩
            intro j hj
            simpa using hpos j (by omega)
          · left; exact ite_eq_right hRlt

theorem pfqCoreIval_not_pfaff_or_top (c : Ctx) (hc : c.Valid)
    (a b : List ℂ) (z : ℂ) (Ar Br : List Ival) (Zr : Ival) (n : Nat)
    (hArLen : Ar.length = a.length) (hBrLen : Br.length = b.length)
    (hmA : ∀ i : Nat, i < Ar.length → (a.getD i 0).re ∈ Ar.getD i Ival.top)
    (hmB : ∀ i : Nat, i < Br.length → (b.getD i 0).re ∈ Br.getD i Ival.top)
    (hmZ : z.re ∈ Zr) :
    pfqCoreIval c Ar Br Zr n = Ival.top ∨
      (pfqGuard Br n = true ∧ ¬ Complex.IsPfaffRegime (↑a : Multiset ℂ) (↑b : Multiset ℂ) z) := by
  unfold pfqCoreIval
  cases hft : pfqFindTerm Ar 0 with
  | some r =>
    obtain ⟨i₀, m⟩ := r
    cases hguard : pfqGuard Br n with
    | false => left; rfl
    | true =>
      right
      have hmA' : ∀ i : Nat, i < Ar.length → (fun k => (a.getD k 0).re) (0 + i) ∈ Ar.getD i Ival.top := by
        intro i hi; simpa using hmA i hi
      obtain ⟨hlt, hval⟩ := pfqFindTerm_ok (fun k => (a.getD k 0).re) Ar 0 hmA' _ hft i₀ m rfl
      exact ⟨rfl, not_isPfaffRegime_of_term a b z i₀ m (by omega) hval⟩
  | none =>
    dsimp only
    by_cases hlen : Ar.length > Br.length + 1
    · left; exact ite_eq_left hlen
    · rw [ite_eq_right hlen]
      cases hguard : pfqGuard Br n with
      | false => left; rfl
      | true =>
        rw [ite_eq_left rfl]
        cases hRhi : (pfqRIval c Ar Br Ar.length Br.length (Ival.abs Zr)
          (Ival.abs (Ar.getD Br.length Ival.top)) n).hi with
        | none => left; rfl
        | some hRD =>
          dsimp only
          by_cases hRlt : hRD.toRat < 1
          · right
            have hmB' : ∀ i : Nat, i < Br.length → (fun k => (b.getD k 0).re) (0 + i) ∈ Br.getD i Ival.top := by
              intro i hi; simpa using hmB i hi
            obtain ⟨hpos, _⟩ := pfqGuard_ok (fun k => (b.getD k 0).re) Br 0 n hmB' hguard
            have hpq' : Ar.length ≤ Br.length + 1 := by omega
            have hRmem := mem_pfqRIval c hc (fun i => (a.getD i 0).re) (fun j => (b.getD j 0).re)
              Ar Br Ar.length Br.length Zr z.re n rfl rfl hmA hmB hmZ hpq'
            have hle := ival_le_hi hRmem hRhi
            have hlt1 : ((hRD.toRat : ℚ) : ℝ) < 1 := by exact_mod_cast hRlt
            have hR : pfqRatio a.length b.length (fun i => (a.getD i 0).re) (fun j => (b.getD j 0).re) |z.re| n < 1 := by
              rw [← hArLen, ← hBrLen]; linarith
            refine ⟨rfl, not_isPfaffRegime_of_pfqRatio_lt_one a b z n ?_ hR⟩
            intro j hj
            have h1 := hpos j (by omega)
            rw [Nat.zero_add] at h1
            linarith
          · left; exact ite_eq_right hRlt

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
  rcases cpfqCoreBox_not_pfaff_or_top c hc a b z A B XZ (64 + 2 * c.prec) hhA hhB hhZ with
    htop | ⟨hguard, hnp⟩
  · rw [htop]
    exact CBox.mem_top _
  · obtain ⟨hlenA, hmA⟩ := forall2_mem_getD hhA
    obtain ⟨hlenB, hmB⟩ := forall2_mem_getD hhB
    obtain ⟨hpos, hne⟩ := cpfqGuard_ok (fun k => b.getD k 0) B (64 + 2 * c.prec) hmB hguard
    have hb_c : ∀ j : Nat, j < b.length → ∀ m : ℕ, b.getD j 0 ≠ -(m : ℂ) :=
      hb_of_cguard (fun k => b.getD k 0) b.length (64 + 2 * c.prec)
        (fun j hj => by simpa using hpos j (by omega))
        (fun j hj k hk => by simpa using hne j (by omega) k hk)
    rw [hy, Complex.HGFun_coe_list_eq_cpfqComplex a b z hb_c hnp]
    exact cpfqCore_sound c hc a.length b.length
      (fun i => a.getD i 0) (fun j => b.getD j 0)
      A B XZ z (64 + 2 * c.prec) hlenA hlenB hmA hmB hhZ

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
      match pfqPfaffArgs c Ar Br Zr (64 + 2 * c.prec) with
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
            let R := pfqCoreIval c Ar Br Zr (64 + 2 * c.prec)
            match R.lo with
            | some _ => (⟨R, Ival.ofRat c.prec 0⟩ : CBox)
            | none => CBox.top
          else CBox.top
    | _, _, _ =>
      match cpfqPfaffArgs c A B Z (64 + 2 * c.prec) with
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
      (X : CEnc [.list .cplx, .list .cplx, .cplx]) (_hc : c.Valid)
      (_hg : y = applyCurried [.list .cplx, .list .cplx, .cplx] .cplx HGFunL vs)
      (_hh : CEncHolds X ds) (_hag : Agree vs ds),
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
            match pfqPfaffArgs c Ar Br Zr (64 + 2 * c.prec) with
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
                  let R := pfqCoreIval c Ar Br Zr (64 + 2 * c.prec)
                  match R.lo with
                  | some _ => (⟨R, Ival.ofRat c.prec 0⟩ : CBox)
                  | none => CBox.top
                else CBox.top
          | _, _, _ =>
            match cpfqPfaffArgs c A B XZ (64 + 2 * c.prec) with
            | some (A', B', W, P) =>
              CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
            | none =>
              match cpfqKummerArgs c A B XZ (64 + 2 * c.prec) with
              | some (A', B', W, P) =>
                CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
              | none => cpfqCoreBox c A B XZ (64 + 2 * c.prec)
        cases hAr : projectReal A with
        | none =>
          show y ∈ match cpfqPfaffArgs c A B XZ (64 + 2 * c.prec) with
          | some (A', B', W, P) =>
            CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
          | none =>
            match cpfqKummerArgs c A B XZ (64 + 2 * c.prec) with
            | some (A', B', W, P) =>
              CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
            | none => cpfqCoreBox c A B XZ (64 + 2 * c.prec)
          cases hP : cpfqPfaffArgs c A B XZ (64 + 2 * c.prec) with
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
            show y ∈ match cpfqPfaffArgs c A B XZ (64 + 2 * c.prec) with
            | some (A', B', W, P) =>
              CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
            | none =>
              match cpfqKummerArgs c A B XZ (64 + 2 * c.prec) with
              | some (A', B', W, P) =>
                CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
              | none => cpfqCoreBox c A B XZ (64 + 2 * c.prec)
            cases hP : cpfqPfaffArgs c A B XZ (64 + 2 * c.prec) with
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
              show y ∈ match cpfqPfaffArgs c A B XZ (64 + 2 * c.prec) with
              | some (A', B', W, P) =>
                CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
              | none =>
                match cpfqKummerArgs c A B XZ (64 + 2 * c.prec) with
                | some (A', B', W, P) =>
                  CBox.mul c.prec P (cpfqCoreBox c A' B' W (64 + 2 * c.prec))
                | none => cpfqCoreBox c A B XZ (64 + 2 * c.prec)
              cases hP : cpfqPfaffArgs c A B XZ (64 + 2 * c.prec) with
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
              show y ∈ match pfqPfaffArgs c Ar Br Zr (64 + 2 * c.prec) with
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
                    let R := pfqCoreIval c Ar Br Zr (64 + 2 * c.prec)
                    match R.lo with
                    | some _ => (⟨R, Ival.ofRat c.prec 0⟩ : CBox)
                    | none => CBox.top
                  else CBox.top
              cases hP : pfqPfaffArgs c Ar Br Zr (64 + 2 * c.prec) with
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
                    rcases pfqCoreIval_not_pfaff_or_top c hc a b z Ar Br Zr (64 + 2 * c.prec)
                        (by omega) (by omega)
                        (fun i hi => (hmemA i (by omega)).1)
                        (fun i hi => (hmemB i (by omega)).1)
                        hre_z with htop | ⟨_, hnp⟩
                    · show y ∈ (let R := pfqCoreIval c Ar Br Zr (64 + 2 * c.prec)
                        match R.lo with
                        | some _ => (⟨R, Ival.ofRat c.prec 0⟩ : CBox)
                        | none => CBox.top)
                      rw [htop]
                      exact CBox.mem_top _
                    · -- denoted value via the bridge
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
                      have hnp_r : ¬ Complex.IsPfaffRegime
                          (↑((a.map Complex.re).map Complex.ofReal) : Multiset ℂ)
                          (↑((b.map Complex.re).map Complex.ofReal) : Multiset ℂ) (z.re : ℂ) := by
                        rwa [hmap_a, hmap_b, hz_eq]
                      have hbridge := Complex.HGFun_coe_list_eq_pfqReal
                        (a.map Complex.re) (b.map Complex.re) (z.re) hb_br hnp_r
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
                      show y ∈ (let R := pfqCoreIval c Ar Br Zr (64 + 2 * c.prec)
                        match R.lo with
                        | some _ => (⟨R, Ival.ofRat c.prec 0⟩ : CBox)
                        | none => CBox.top)
                      dsimp only
                      cases hRlo : (pfqCoreIval c Ar Br Zr (64 + 2 * c.prec)).lo with
                      | none => exact CBox.mem_top _
                      | some _ => exact CBox.mem_def.mpr ⟨hcore, hyim⟩

@[lynth_cfn] def HGFunLR : CFn [.list .cplx, .list .cplx, .cplx] .cplx :=
  { name := "HGFun",
    fn := fun _ _ _ => (0 : ℂ),
    graph := CFn.graphOf [.list .cplx, .list .cplx, .cplx] .cplx HGFunL,
    exu := CFn.exuOf (tys := [.list .cplx, .list .cplx, .cplx]) .cplx HGFunL,
    ev := HGFunL_ev,
    sound := HGFunL_sound,
    cost := 1500 }


end Lynth.Interval.Fns
