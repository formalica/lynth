import Lynth.Interval.Fns.Zeta
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
  bound; no float simulation needed); tail `|T_n|·R/(1-R)` with `R` the
  uniform later-ratio bound (`pfq_bound_factor.c`, real-line form).
* Per term: `p+q+3` muls + 1 div (no Bernoulli, no special functions).

Analytic identities + tail bound are `sorry`'d here and mirrored in
`/tmp/pfq_thm.lean` (Mathlib-only, for the external prover; the `HGFun`
defs there are exact copies of `Lynth/Hypergeometric.lean`, drop on port).
Shapes are per-`(p,q)` `CFn.manual` entries sharing one core.
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

/-- SORRY (handoff `/tmp/pfq_thm.lean`): term recurrence. -/
theorem pfqTerm_succ (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (k : ℕ)
    (hB : ∀ j : Nat, j < q → b j + (k : ℝ) ≠ 0) :
    pfqTerm p q a b z (k + 1) = pfqTerm p q a b z k
      * ((∏ i ∈ Finset.range p, (a i + (k : ℝ)))
        / (∏ j ∈ Finset.range q, (b j + (k : ℝ))) * z / ((k : ℝ) + 1)) := by
  sorry

/-- SORRY (handoff `/tmp/pfq_thm.lean`): tail bound. -/
theorem pfqTail (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (n : Nat)
    (hpq : p ≤ q + 1)
    (hBpos : ∀ j : Nat, j < q → 0 < b j + (n : ℝ))
    (hBne : ∀ j : Nat, j < q → ∀ k : Nat, k < n → b j + (k : ℝ) ≠ 0)
    (hR : pfqRatio p q a b |z| n < 1) :
    |pfqReal p q a b z - (Finset.range n).sum (fun k => pfqTerm p q a b z k)|
      ≤ |pfqTerm p q a b z n|
        * (pfqRatio p q a b |z| n / (1 - pfqRatio p q a b |z| n)) := by
  sorry

/-- SORRY (handoff `/tmp/pfq_thm.lean`): terminating tops. -/
theorem pfqTerm_exact (p q : Nat) (a b : ℕ → ℝ) (z : ℝ) (m : Nat)
    (i₀ : Nat) (hi₀ : i₀ < p) (hterm : a i₀ = -(m : ℝ)) :
    pfqReal p q a b z = (Finset.range (m + 1)).sum (fun k => pfqTerm p q a b z k) := by
  sorry

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

/-- core evaluator: finite prefix or sum + symmetric tail widening. -/
def pfqCoreIval (c : Ctx) (A B : List Ival) (Z : Ival) (n : Nat) : Ival :=
  match pfqFindTerm A 0 with
  | some (_, m) =>
    pfqFiniteIval c A B A.length B.length Z m
  | none =>
    if A.length > B.length + 1 then Ival.top
    else if pfqGuard B n then
      let res := pfqLoop c A B A.length B.length Z n 0
        (Ival.ofRat c.prec 0) (Ival.ofRat c.prec 1)
      let p := A.length
      let q := B.length
      let W := Ival.mul c.prec (Ival.abs res.2)
        (pfqTailC c (pfqRIval c A B p q (Ival.abs Z)
          (Ival.abs (A.getD q Ival.top)) n))
      match W.hi with
      | some h => Ival.add c.prec res.1 (Ival.ofRats c.prec (-h.toRat) h.toRat)
      | none => Ival.top
    else Ival.top

/-- core soundness (statement; proof via loop invariant + tail/terminating
sorries — filled after the handoff returns). -/
theorem pfqCore_sound (c : Ctx) (hc : c.Valid)
    (p q : Nat) (a b : ℕ → ℝ) (A B : List Ival) (Z : Ival) (z : ℝ) (n : Nat)
    (hlenA : A.length = p) (hlenB : B.length = q)
    (hmA : ∀ i : Nat, i < A.length → a i ∈ A.getD i Ival.top)
    (hmB : ∀ i : Nat, i < B.length → b i ∈ B.getD i Ival.top)
    (hmZ : z ∈ Z) :
    pfqReal p q a b z ∈ pfqCoreIval c A B Z n := by
  sorry


/-- 0F1 mirror (general engine, 2 args). -/
noncomputable def pfq01 (b z : ℝ) : ℝ :=
  pfqReal 0 1 (fun _ => 0) (fun _ => b) z

def pfq01_ev (c : Ctx) : CEnc [.real, .real] → Ival
  | (.cons .real B (.cons .real Z .nil)) =>
    pfqCoreIval c [] [B] Z (64 + 2 * c.prec)

theorem pfq01_sound (c : Ctx) :
    ∀ (vs : CVal [.real, .real]) (ds : CDen [.real, .real]) (y' y : ℝ)
      (X : CEnc [.real, .real]) (hc : c.Valid)
      (hg : y' = applyCurried [.real, .real] .real pfq01 vs)
      (hout : castOut .real y' = y)
      (hh : CEncHolds X ds) (hag : Agree vs ds),
    Ival.Mem (pfq01_ev c X) y := by
  sorry

/-- entries are `CFn.mk` literals (not `CFn.manual`): the real mirror lives
only in `graph`/`exu`/`sound` (`Prop`), while `fn` is a computable dummy
(never applied: denote uses `fn'` from `graph`, eval uses `ev`). This keeps
the entry computable so `evalExprVal` can evaluate it; the registry reads `F`
from `graph`. -/
@[lynth_cfn] def pfq01R : CFn [.real, .real] .real :=
  { name := "pfq01",
    fn := fun _ _ => (0 : ℝ),
    graph := CFn.graphOf [.real, .real] .real pfq01,
    exu := CFn.exuOf (tys := [.real, .real]) .real pfq01,
    ev := pfq01_ev,
    sound := pfq01_sound,
    cost := 1500 }


/-- 1F1 mirror (general engine, 3 args). -/
noncomputable def pfq11 (a b z : ℝ) : ℝ :=
  pfqReal 1 1 (fun _ => a) (fun _ => b) z

def pfq11_ev (c : Ctx) : CEnc [.real, .real, .real] → Ival
  | (.cons .real A (.cons .real B (.cons .real Z .nil))) =>
    pfqCoreIval c [A] [B] Z (64 + 2 * c.prec)

theorem pfq11_sound (c : Ctx) :
    ∀ (vs : CVal [.real, .real, .real]) (ds : CDen [.real, .real, .real]) (y' y : ℝ)
      (X : CEnc [.real, .real, .real]) (hc : c.Valid)
      (hg : y' = applyCurried [.real, .real, .real] .real pfq11 vs)
      (hout : castOut .real y' = y)
      (hh : CEncHolds X ds) (hag : Agree vs ds),
    Ival.Mem (pfq11_ev c X) y := by
  sorry

@[lynth_cfn] def pfq11R : CFn [.real, .real, .real] .real :=
  { name := "pfq11",
    fn := fun _ _ _ => (0 : ℝ),
    graph := CFn.graphOf [.real, .real, .real] .real pfq11,
    exu := CFn.exuOf (tys := [.real, .real, .real]) .real pfq11,
    ev := pfq11_ev,
    sound := pfq11_sound,
    cost := 1500 }


/-- 2F1 mirror (general engine, 4 args). -/
noncomputable def pfq21 (a1 a2 b z : ℝ) : ℝ :=
  pfqReal 2 1 (fun i => if i = 0 then a1 else a2) (fun _ => b) z

def pfq21_ev (c : Ctx) : CEnc [.real, .real, .real, .real] → Ival
  | (.cons .real A1 (.cons .real A2 (.cons .real B (.cons .real Z .nil)))) =>
    pfqCoreIval c [A1, A2] [B] Z (64 + 2 * c.prec)

theorem pfq21_sound (c : Ctx) :
    ∀ (vs : CVal [.real, .real, .real, .real]) (ds : CDen [.real, .real, .real, .real]) (y' y : ℝ)
      (X : CEnc [.real, .real, .real, .real]) (hc : c.Valid)
      (hg : y' = applyCurried [.real, .real, .real, .real] .real pfq21 vs)
      (hout : castOut .real y' = y)
      (hh : CEncHolds X ds) (hag : Agree vs ds),
    Ival.Mem (pfq21_ev c X) y := by
  sorry

@[lynth_cfn] def pfq21R : CFn [.real, .real, .real, .real] .real :=
  { name := "pfq21",
    fn := fun _ _ _ _ => (0 : ℝ),
    graph := CFn.graphOf [.real, .real, .real, .real] .real pfq21,
    exu := CFn.exuOf (tys := [.real, .real, .real, .real]) .real pfq21,
    ev := pfq21_ev,
    sound := pfq21_sound,
    cost := 1500 }


/-- 0F2 mirror (general engine, 3 args). -/
noncomputable def pfq02 (b1 b2 z : ℝ) : ℝ :=
  pfqReal 0 2 (fun _ => 0) (fun j => if j = 0 then b1 else b2) z

def pfq02_ev (c : Ctx) : CEnc [.real, .real, .real] → Ival
  | (.cons .real B1 (.cons .real B2 (.cons .real Z .nil))) =>
    pfqCoreIval c [] [B1, B2] Z (64 + 2 * c.prec)

theorem pfq02_sound (c : Ctx) :
    ∀ (vs : CVal [.real, .real, .real]) (ds : CDen [.real, .real, .real]) (y' y : ℝ)
      (X : CEnc [.real, .real, .real]) (hc : c.Valid)
      (hg : y' = applyCurried [.real, .real, .real] .real pfq02 vs)
      (hout : castOut .real y' = y)
      (hh : CEncHolds X ds) (hag : Agree vs ds),
    Ival.Mem (pfq02_ev c X) y := by
  sorry

@[lynth_cfn] def pfq02R : CFn [.real, .real, .real] .real :=
  { name := "pfq02",
    fn := fun _ _ _ => (0 : ℝ),
    graph := CFn.graphOf [.real, .real, .real] .real pfq02,
    exu := CFn.exuOf (tys := [.real, .real, .real]) .real pfq02,
    ev := pfq02_ev,
    sound := pfq02_sound,
    cost := 1500 }


/-- 1F2 mirror (general engine, 4 args). -/
noncomputable def pfq12 (a b1 b2 z : ℝ) : ℝ :=
  pfqReal 1 2 (fun _ => a) (fun j => if j = 0 then b1 else b2) z

def pfq12_ev (c : Ctx) : CEnc [.real, .real, .real, .real] → Ival
  | (.cons .real A (.cons .real B1 (.cons .real B2 (.cons .real Z .nil)))) =>
    pfqCoreIval c [A] [B1, B2] Z (64 + 2 * c.prec)

theorem pfq12_sound (c : Ctx) :
    ∀ (vs : CVal [.real, .real, .real, .real]) (ds : CDen [.real, .real, .real, .real]) (y' y : ℝ)
      (X : CEnc [.real, .real, .real, .real]) (hc : c.Valid)
      (hg : y' = applyCurried [.real, .real, .real, .real] .real pfq12 vs)
      (hout : castOut .real y' = y)
      (hh : CEncHolds X ds) (hag : Agree vs ds),
    Ival.Mem (pfq12_ev c X) y := by
  sorry

@[lynth_cfn] def pfq12R : CFn [.real, .real, .real, .real] .real :=
  { name := "pfq12",
    fn := fun _ _ _ _ => (0 : ℝ),
    graph := CFn.graphOf [.real, .real, .real, .real] .real pfq12,
    exu := CFn.exuOf (tys := [.real, .real, .real, .real]) .real pfq12,
    ev := pfq12_ev,
    sound := pfq12_sound,
    cost := 1500 }


/-- 2F2 mirror (general engine, 5 args). -/
noncomputable def pfq22 (a1 a2 b1 b2 z : ℝ) : ℝ :=
  pfqReal 2 2 (fun i => if i = 0 then a1 else a2) (fun j => if j = 0 then b1 else b2) z

def pfq22_ev (c : Ctx) : CEnc [.real, .real, .real, .real, .real] → Ival
  | (.cons .real A1 (.cons .real A2 (.cons .real B1 (.cons .real B2 (.cons .real Z .nil))))) =>
    pfqCoreIval c [A1, A2] [B1, B2] Z (64 + 2 * c.prec)

theorem pfq22_sound (c : Ctx) :
    ∀ (vs : CVal [.real, .real, .real, .real, .real]) (ds : CDen [.real, .real, .real, .real, .real]) (y' y : ℝ)
      (X : CEnc [.real, .real, .real, .real, .real]) (hc : c.Valid)
      (hg : y' = applyCurried [.real, .real, .real, .real, .real] .real pfq22 vs)
      (hout : castOut .real y' = y)
      (hh : CEncHolds X ds) (hag : Agree vs ds),
    Ival.Mem (pfq22_ev c X) y := by
  sorry

@[lynth_cfn] def pfq22R : CFn [.real, .real, .real, .real, .real] .real :=
  { name := "pfq22",
    fn := fun _ _ _ _ _ => (0 : ℝ),
    graph := CFn.graphOf [.real, .real, .real, .real, .real] .real pfq22,
    exu := CFn.exuOf (tys := [.real, .real, .real, .real, .real]) .real pfq22,
    ev := pfq22_ev,
    sound := pfq22_sound,
    cost := 1500 }


/-- 3F2 mirror (general engine, 6 args). -/
noncomputable def pfq32 (a1 a2 a3 b1 b2 z : ℝ) : ℝ :=
  pfqReal 3 2 (fun i => if i = 0 then a1 else if i = 1 then a2 else a3) (fun j => if j = 0 then b1 else b2) z

def pfq32_ev (c : Ctx) : CEnc [.real, .real, .real, .real, .real, .real] → Ival
  | (.cons .real A1 (.cons .real A2 (.cons .real A3 (.cons .real B1 (.cons .real B2 (.cons .real Z .nil)))))) =>
    pfqCoreIval c [A1, A2, A3] [B1, B2] Z (64 + 2 * c.prec)

theorem pfq32_sound (c : Ctx) :
    ∀ (vs : CVal [.real, .real, .real, .real, .real, .real]) (ds : CDen [.real, .real, .real, .real, .real, .real]) (y' y : ℝ)
      (X : CEnc [.real, .real, .real, .real, .real, .real]) (hc : c.Valid)
      (hg : y' = applyCurried [.real, .real, .real, .real, .real, .real] .real pfq32 vs)
      (hout : castOut .real y' = y)
      (hh : CEncHolds X ds) (hag : Agree vs ds),
    Ival.Mem (pfq32_ev c X) y := by
  sorry

@[lynth_cfn] def pfq32R : CFn [.real, .real, .real, .real, .real, .real] .real :=
  { name := "pfq32",
    fn := fun _ _ _ _ _ _ => (0 : ℝ),
    graph := CFn.graphOf [.real, .real, .real, .real, .real, .real] .real pfq32,
    exu := CFn.exuOf (tys := [.real, .real, .real, .real, .real, .real]) .real pfq32,
    ev := pfq32_ev,
    sound := pfq32_sound,
    cost := 1500 }


end Lynth.Interval.Fns
