import Lynth.Interval.Core.Expr
import Lynth.Interval.Fns.Arith
import Lynth.Interval.Series.ComplexTails

/-!
# Complex series certificates: family matchers + norm-based enclosures.

Infinite complex sums are certified without complex AIA.  Reified bodies are
matched (by registry `name`) against fixed families:

* exact telescoping (`Complex_tsum_telescoping`, `..._step2n`): the value box
  is the interval evaluation of the closed form;
* geometric majorants (`Complex_factorial_majorant`, `..._selfpow`,
  `..._mersenne`, `..._fib`): `N` partial sums by the generic `sum`
  evaluator plus a norm-disc tail via `Complex_geometric_tail`.

Complex holes are restricted to `ofRealC (lit q)` literals (nat-cast
literals normalize to these during reification); nat holes to `natLit n`.
Shared subterms are matched independently with value-equality guards.
-/

namespace Lynth.Interval.Series

open Lynth.Interval

/-! ### Denotation kit: unfolding equations for reified shapes -/

theorem denote_lit (q : ℚ) (ρ : SEnv) : (Expr.lit q).denote ρ = ((q : ℚ) : ℝ) := rfl

theorem denote_natLit (n : ℕ) (ρ : SEnv) : (Expr.natLit n).denote ρ = n := rfl

theorem denote_var_nat (ρ : SEnv) (i : ℕ) :
    (Expr.var .nat i).denote ρ = ρ.get .nat i := rfl

theorem get_push_nat0 (ρ : SEnv) (k : ℕ) : (ρ.push .nat k).get .nat 0 = k := rfl

/-- unary registry calls denote through their graph -/
theorem denote_ofFn1 {a r : Ty} (f : Fn1 a r) (x : Expr a) (ρ : SEnv) (y : r.Val)
    (hg : f.graph (x.denote ρ) y) :
    (Expr.call (CFn.ofFn1 f) (CArg.cons a x CArg.nil)).denote ρ = y := by
  have hag : Agree (CVal.cons a (x.denote ρ) CVal.nil)
      (Expr.CArg.denoteArgs ρ (CArg.cons a x CArg.nil)) := ⟨rfl, trivial⟩
  exact (Expr.call_eq _ _ _ rfl hag hg).symm

/-- binary registry calls denote through their graph -/
theorem denote_ofFn2 {a b r : Ty} (f : Fn2 a b r) (x : Expr a) (y : Expr b) (ρ : SEnv)
    (z : r.Val) (hg : f.graph (x.denote ρ) (y.denote ρ) z) :
    (Expr.call (CFn.ofFn2 f) (CArg.cons a x (CArg.cons b y CArg.nil))).denote ρ = z := by
  have hag : Agree (CVal.cons a (x.denote ρ) (CVal.cons b (y.denote ρ) CVal.nil))
      (Expr.CArg.denoteArgs ρ (CArg.cons a x (CArg.cons b y CArg.nil))) :=
    ⟨rfl, rfl, trivial⟩
  exact (Expr.call_eq _ _ _ rfl hag hg).symm

theorem denote_divC (x y : Expr .cplx) (ρ : SEnv) :
    (Expr.call (CFn.ofFn2 Fns.divC)
      (CArg.cons .cplx x (CArg.cons .cplx y CArg.nil))).denote ρ
    = x.denote ρ / y.denote ρ :=
  denote_ofFn2 _ _ _ _ _ rfl

theorem denote_mulC (x y : Expr .cplx) (ρ : SEnv) :
    (Expr.call (CFn.ofFn2 Fns.mulC)
      (CArg.cons .cplx x (CArg.cons .cplx y CArg.nil))).denote ρ
    = x.denote ρ * y.denote ρ :=
  denote_ofFn2 _ _ _ _ _ rfl

theorem denote_addC (x y : Expr .cplx) (ρ : SEnv) :
    (Expr.call (CFn.ofFn2 Fns.addC)
      (CArg.cons .cplx x (CArg.cons .cplx y CArg.nil))).denote ρ
    = x.denote ρ + y.denote ρ :=
  denote_ofFn2 _ _ _ _ _ rfl

theorem denote_subC (x y : Expr .cplx) (ρ : SEnv) :
    (Expr.call (CFn.ofFn2 Fns.subC)
      (CArg.cons .cplx x (CArg.cons .cplx y CArg.nil))).denote ρ
    = x.denote ρ - y.denote ρ :=
  denote_ofFn2 _ _ _ _ _ rfl

theorem denote_natCastC (x : Expr .nat) (ρ : SEnv) :
    (Expr.call (CFn.ofFn1 Fns.natCastC) (CArg.cons .nat x CArg.nil)).denote ρ
    = ((x.denote ρ : ℕ) : ℂ) :=
  denote_ofFn1 _ _ _ _ rfl

theorem denote_ofRealC (x : Expr .real) (ρ : SEnv) :
    (Expr.call (CFn.ofFn1 Fns.ofRealC) (CArg.cons .real x CArg.nil)).denote ρ
    = ((x.denote ρ : ℝ) : ℂ) :=
  denote_ofFn1 _ _ _ _ rfl

theorem denote_npowC (x : Expr .cplx) (n : Expr .nat) (ρ : SEnv) :
    (Expr.call (CFn.ofFn2 Fns.npowC)
      (CArg.cons .cplx x (CArg.cons .nat n CArg.nil))).denote ρ
    = x.denote ρ ^ n.denote ρ :=
  denote_ofFn2 _ _ _ _ _ rfl

theorem denote_factorialN (x : Expr .nat) (ρ : SEnv) :
    (Expr.call (CFn.ofFn1 Fns.factorialN) (CArg.cons .nat x CArg.nil)).denote ρ
    = Nat.factorial (x.denote ρ) :=
  denote_ofFn1 _ _ _ _ rfl

theorem denote_fibN (x : Expr .nat) (ρ : SEnv) :
    (Expr.call (CFn.ofFn1 Fns.fibN) (CArg.cons .nat x CArg.nil)).denote ρ
    = Nat.fib (x.denote ρ) :=
  denote_ofFn1 _ _ _ _ rfl

theorem denote_addN (x y : Expr .nat) (ρ : SEnv) :
    (Expr.call (CFn.ofFn2 Fns.addN)
      (CArg.cons .nat x (CArg.cons .nat y CArg.nil))).denote ρ
    = x.denote ρ + y.denote ρ :=
  denote_ofFn2 _ _ _ _ _ rfl

/-- ℂ-valued denotation (avoids `Ty.Val` unfolding mismatches in tactics) -/
noncomputable def denoteC (e : Expr .cplx) (ρ : SEnv) : ℂ := e.denote ρ

/-- ℂ-valued kit: every equation stays inside `ℂ`, so `simp` never faces
`Ty.Val`/`ℂ` mismatches -/
theorem denoteC_divC (x y : Expr .cplx) (ρ : SEnv) :
    denoteC (Expr.call (CFn.ofFn2 Fns.divC)
      (CArg.cons .cplx x (CArg.cons .cplx y CArg.nil))) ρ
    = denoteC x ρ / denoteC y ρ := by
  show (Expr.call (CFn.ofFn2 Fns.divC)
    (CArg.cons .cplx x (CArg.cons .cplx y CArg.nil))).denote ρ
    = x.denote ρ / y.denote ρ
  exact denote_divC x y ρ

theorem denoteC_mulC (x y : Expr .cplx) (ρ : SEnv) :
    denoteC (Expr.call (CFn.ofFn2 Fns.mulC)
      (CArg.cons .cplx x (CArg.cons .cplx y CArg.nil))) ρ
    = denoteC x ρ * denoteC y ρ := by
  show (Expr.call (CFn.ofFn2 Fns.mulC)
    (CArg.cons .cplx x (CArg.cons .cplx y CArg.nil))).denote ρ
    = x.denote ρ * y.denote ρ
  exact denote_mulC x y ρ

theorem denoteC_addC (x y : Expr .cplx) (ρ : SEnv) :
    denoteC (Expr.call (CFn.ofFn2 Fns.addC)
      (CArg.cons .cplx x (CArg.cons .cplx y CArg.nil))) ρ
    = denoteC x ρ + denoteC y ρ := by
  show (Expr.call (CFn.ofFn2 Fns.addC)
    (CArg.cons .cplx x (CArg.cons .cplx y CArg.nil))).denote ρ
    = x.denote ρ + y.denote ρ
  exact denote_addC x y ρ

theorem denoteC_subC (x y : Expr .cplx) (ρ : SEnv) :
    denoteC (Expr.call (CFn.ofFn2 Fns.subC)
      (CArg.cons .cplx x (CArg.cons .cplx y CArg.nil))) ρ
    = denoteC x ρ - denoteC y ρ := by
  show (Expr.call (CFn.ofFn2 Fns.subC)
    (CArg.cons .cplx x (CArg.cons .cplx y CArg.nil))).denote ρ
    = x.denote ρ - y.denote ρ
  exact denote_subC x y ρ

theorem denoteC_npowC (x : Expr .cplx) (n : Expr .nat) (ρ : SEnv) :
    denoteC (Expr.call (CFn.ofFn2 Fns.npowC)
      (CArg.cons .cplx x (CArg.cons .nat n CArg.nil))) ρ
    = denoteC x ρ ^ n.denote ρ := by
  show (Expr.call (CFn.ofFn2 Fns.npowC)
    (CArg.cons .cplx x (CArg.cons .nat n CArg.nil))).denote ρ
    = x.denote ρ ^ n.denote ρ
  exact denote_npowC x n ρ

theorem denoteC_natCastC (x : Expr .nat) (ρ : SEnv) :
    denoteC (Expr.call (CFn.ofFn1 Fns.natCastC) (CArg.cons .nat x CArg.nil)) ρ
    = ((x.denote ρ : ℕ) : ℂ) := by
  show (Expr.call (CFn.ofFn1 Fns.natCastC)
    (CArg.cons .nat x CArg.nil)).denote ρ = ((x.denote ρ : ℕ) : ℂ)
  exact denote_natCastC x ρ

theorem denoteC_ofRealC (x : Expr .real) (ρ : SEnv) :
    denoteC (Expr.call (CFn.ofFn1 Fns.ofRealC) (CArg.cons .real x CArg.nil)) ρ
    = ((x.denote ρ : ℝ) : ℂ) := by
  show (Expr.call (CFn.ofFn1 Fns.ofRealC)
    (CArg.cons .real x CArg.nil)).denote ρ = ((x.denote ρ : ℝ) : ℂ)
  exact denote_ofRealC x ρ

/-! ### Congruence kit for explicit bridge assembly -/

theorem cdiv_congr {a a' b b' : ℂ} (ha : a = a') (hb : b = b') :
    a / b = a' / b' := by rw [ha, hb]

theorem cmul_congr {a a' b b' : ℂ} (ha : a = a') (hb : b = b') :
    a * b = a' * b' := by rw [ha, hb]

theorem cadd_congr {a a' b b' : ℂ} (ha : a = a') (hb : b = b') :
    a + b = a' + b' := by rw [ha, hb]

theorem csub_congr {a a' b b' : ℂ} (ha : a = a') (hb : b = b') :
    a - b = a' - b' := by rw [ha, hb]

theorem cnpow_congr {a a' : ℂ} {m m' : ℕ} (ha : a = a') (hm : m = m') :
    a ^ m = a' ^ m' := by rw [ha, hm]

theorem cnatCast_congr {m m' : ℕ} (h : m = m') :
    ((m : ℕ) : ℂ) = ((m' : ℕ) : ℂ) := by rw [h]

theorem cofReal_congr {x x' : ℝ} (h : x = x') :
    ((x : ℝ) : ℂ) = ((x' : ℝ) : ℂ) := by rw [h]

theorem nadd_congr {a a' b b' : ℕ} (ha : a = a') (hb : b = b') :
    a + b = a' + b' := by rw [ha, hb]

theorem nfact_congr {m m' : ℕ} (h : m = m') :
    Nat.factorial m = Nat.factorial m' := by rw [h]

theorem nfib_congr {m m' : ℕ} (h : m = m') :
    Nat.fib m = Nat.fib m' := by rw [h]

/-! ### Shared pair-witness check -/

/-- point box of a rational pair -/
def pairBox (c : Ctx) (q1 q2 : ℚ) : CBox :=
  ⟨Ival.ofRat c.prec q1, Ival.ofRat c.prec q2⟩

theorem mem_pairBox (c : Ctx) (q1 q2 : ℚ) :
    (((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I) ∈ pairBox c q1 q2 := by
  rw [CBox.mem_def]
  constructor
  · have e : ((((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I)).re = ((q1 : ℚ) : ℝ) := by
      simp
    rw [e]
    exact Ival.mem_ofRat _ _
  · have e : ((((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I)).im = ((q2 : ℚ) : ℝ) := by
      simp
    rw [e]
    exact Ival.mem_ofRat _ _

/-- `‖z - q‖ < tol` from an enclosure of `z` -/
def distCheck (c : Ctx) (B : CBox) (q1 q2 : ℚ) (tol : Expr .real) : Bool :=
  Ival.ltB (CBox.norm c.prec (CBox.sub c.prec B (pairBox c q1 q2))) (tol.eval c {})

theorem distCheck_sound {c : Ctx} (hc : c.Valid) {B : CBox} {z : ℂ} {q1 q2 : ℚ}
    {tol : Expr .real} (hmem : z ∈ B) (h : distCheck c B q1 q2 tol = true) :
    ‖z - (((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I)‖ < tol.denote {} := by
  unfold distCheck at h
  have hmem2 : z - (((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I)
      ∈ CBox.sub c.prec B (pairBox c q1 q2) :=
    CBox.mem_sub hmem (mem_pairBox c q1 q2)
  have hmem3 : ‖z - (((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I)‖
      ∈ CBox.norm c.prec (CBox.sub c.prec B (pairBox c q1 q2)) :=
    CBox.mem_norm hmem2
  exact Ival.lt_of_ltB hmem3 (Expr.eval_sound hc tol IEnv.holds_empty) h

/-- monomorphic division cross-multiplication (no universe polymorphism,
safe for explicit `MetaM` application) -/
theorem div_eq_div_iff_C {a b c d : ℂ} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b = c / d ↔ a * d = c * b :=
  div_eq_div_iff hb hd

/-! ### Family 1: step-1 telescoping `c / ((w + k) * (w + k + 1))` -/

/-- reified shape match; returns the two literal values -/
def matchTele1 (body : Expr .cplx) : Option (ℚ × ℚ) :=
  match body with
  | .call f1 (.cons .cplx C (.cons .cplx D .nil)) =>
    match D with
    | .call f2 (.cons .cplx U (.cons .cplx V .nil)) =>
      match U, V with
      | .call f3 (.cons .cplx W (.cons .cplx Kc .nil)),
        .call f4 (.cons .cplx U2 (.cons .cplx One .nil)) =>
        match U2, Kc with
        | .call f5 (.cons .cplx W2 (.cons .cplx Kc2 .nil)),
          .call gK (.cons .nat (.var .nat 0) .nil) =>
          match Kc2, W, W2, One, C with
          | .call gK2 (.cons .nat (.var .nat 0) .nil),
            .call gW (.cons .real (.lit w1) .nil),
            .call gW2 (.cons .real (.lit w2) .nil),
            .call g1 (.cons .real (.lit q1) .nil),
            .call gC (.cons .real (.lit c0) .nil) =>
            if decide (f1.name = "/ℂ") then
            if decide (f2.name = "*ℂ") then
            if decide (f3.name = "+ℂ") then
            if decide (f4.name = "+ℂ") then
            if decide (f5.name = "+ℂ") then
            if decide (gK.name = "ℕ→ℂ") then
            if decide (gK2.name = "ℕ→ℂ") then
            if decide (gW.name = "ℝ→ℂ") then
            if decide (gW2.name = "ℝ→ℂ") then
            if decide (g1.name = "ℝ→ℂ") then
            if decide (gC.name = "ℝ→ℂ") then
            if decide (q1 = 1) then
            if decide (w1 = w2) then
            if decide (1 ≤ w1) then some (c0, w1)
            else none else none else none else none
            else none else none else none else none
            else none else none else none else none
            else none else none
          | _, _, _, _, _ => none
        | _, _ => none
      | _, _ => none
    | _ => none
  | _ => none

/-- point box of a real literal as a complex number -/
def ptBox (c : Ctx) (q : ℚ) : CBox :=
  ⟨Ival.ofRat c.prec q, Ival.ofRat c.prec 0⟩

theorem mem_ptBox (c : Ctx) (q : ℚ) : ((((q : ℚ) : ℝ) : ℂ)) ∈ ptBox c q := by
  rw [CBox.mem_def]
  refine ⟨?_, ?_⟩
  · have e : (((((q : ℚ) : ℝ) : ℂ))).re = ((q : ℚ) : ℝ) := by simp
    rw [e]
    show ((q : ℚ) : ℝ) ∈ Ival.ofRat c.prec q
    exact Ival.mem_ofRat _ _
  · have e : (((((q : ℚ) : ℝ) : ℂ))).im = 0 := by simp
    rw [e]
    show (0 : ℝ) ∈ Ival.ofRat c.prec 0
    simpa using Ival.mem_ofRat c.prec 0

/-- exact-value enclosure from the closed form -/
def tele1Box (c : Ctx) (c0 w1 : ℚ) : CBox :=
  CBox.div c.prec (ptBox c c0) (ptBox c w1)

/-- the value check for family 1 -/
def tele1Check (c : Ctx) (c0 w1 q1 q2 : ℚ) (tol : Expr .real) : Bool :=
  distCheck c (tele1Box c c0 w1) q1 q2 tol

theorem tele1_sound {c : Ctx} (hc : c.Valid) {f : ℕ → ℂ} {c0 w1 : ℚ}
    {q1 q2 : ℚ} {tol : Expr .real}
    (hbridge : ∀ k : ℕ, f k
      = ((c0 : ℝ) : ℂ) / ((((w1 : ℝ) : ℂ) + ((k : ℕ) : ℂ))
        * ((((w1 : ℝ) : ℂ) + ((k : ℕ) : ℂ)) + 1)))
    (hw : (1 : ℝ) ≤ ((w1 : ℚ) : ℝ))
    (hdist : tele1Check c c0 w1 q1 q2 tol = true) :
    Summable f ∧
      ‖tsum f - ((((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I))‖ < tol.denote {} := by
  have hw' : (1 : ℝ) ≤ (((w1 : ℝ) : ℂ)).re := by simpa using hw
  have hfam := Complex_tsum_telescoping (c := ((c0 : ℝ) : ℂ))
    (w := ((w1 : ℝ) : ℂ)) hw'
  obtain ⟨hs, hv⟩ := hfam
  have heq : f
      = (fun j : ℕ => ((c0 : ℝ) : ℂ) / ((((w1 : ℝ) : ℂ) + ((j : ℕ) : ℂ))
        * ((((w1 : ℝ) : ℂ) + ((j : ℕ) : ℂ)) + 1))) :=
    funext hbridge
  rw [heq]
  refine ⟨hs, ?_⟩
  rw [hv]
  have hmem : ((c0 : ℝ) : ℂ) / ((w1 : ℝ) : ℂ)
      ∈ tele1Box c c0 w1 := by
    unfold tele1Box
    exact CBox.mem_div (mem_ptBox c c0) (mem_ptBox c w1)
  unfold tele1Check at hdist
  exact distCheck_sound hc hmem hdist

/-! ### Family 2: step-2 telescoping `c / ((2*k + b) * ((2*k + b) + 2))` -/

/-- reified shape match (add-doubled `k+k` inner); returns the two literal values -/
def matchTele2n (body : Expr .cplx) : Option (ℚ × ℚ) :=
  match body with
  | .call f1 (.cons .cplx C (.cons .cplx D .nil)) =>
    match D with
    | .call f2 (.cons .cplx F1 (.cons .cplx F2 .nil)) =>
      match F1, F2 with
      | .call f3 (.cons .cplx K2 (.cons .cplx B .nil)),
        .call f4 (.cons .cplx U2 (.cons .cplx Two2 .nil)) =>
        match K2, U2 with
        | .call f5 (.cons .cplx Ka (.cons .cplx Kb .nil)),
          .call f6 (.cons .cplx K2b (.cons .cplx B2 .nil)) =>
          match K2b with
          | .call f7 (.cons .cplx Kc2 (.cons .cplx Kd2 .nil)) =>
            match Ka, Kb, Kc2, Kd2, B, B2, Two2, C with
            | .call gKa (.cons .nat (.var .nat 0) .nil),
              .call gKb (.cons .nat (.var .nat 0) .nil),
              .call gKc (.cons .nat (.var .nat 0) .nil),
              .call gKd (.cons .nat (.var .nat 0) .nil),
              .call gB (.cons .real (.lit b0) .nil),
              .call gB2 (.cons .real (.lit b2) .nil),
              .call gT (.cons .real (.lit q2) .nil),
              .call gC (.cons .real (.lit c0) .nil) =>
              if decide (f1.name = "/ℂ") then
              if decide (f2.name = "*ℂ") then
              if decide (f3.name = "+ℂ") then
              if decide (f4.name = "+ℂ") then
              if decide (f5.name = "+ℂ") then
              if decide (f6.name = "+ℂ") then
              if decide (f7.name = "+ℂ") then
              if decide (gKa.name = "ℕ→ℂ") then
              if decide (gKb.name = "ℕ→ℂ") then
              if decide (gKc.name = "ℕ→ℂ") then
              if decide (gKd.name = "ℕ→ℂ") then
              if decide (gB.name = "ℝ→ℂ") then
              if decide (gB2.name = "ℝ→ℂ") then
              if decide (gT.name = "ℝ→ℂ") then
              if decide (gC.name = "ℝ→ℂ") then
              if decide (q2 = 2) then
              if decide (b2 = b0) then
              if decide (1 ≤ b0) then some (c0, b0)
              else none else none else none else none
              else none else none else none else none
              else none else none else none else none
              else none else none else none else none
              else none else none
            | _, _, _, _, _, _, _, _ => none
          | _ => none
        | _, _ => none
      | _, _ => none
    | _ => none
  | _ => none

/-- exact-value enclosure from the closed form `(c/2)/b` -/
def tele2Box (c : Ctx) (c0 b0 : ℚ) : CBox :=
  CBox.div c.prec
    (CBox.div c.prec (ptBox c c0) (ptBox c 2)) (ptBox c b0)

/-- the value check for family 2 -/
def tele2Check (c : Ctx) (c0 b0 q1 q2 : ℚ) (tol : Expr .real) : Bool :=
  distCheck c (tele2Box c c0 b0) q1 q2 tol

theorem tele2_sound {c : Ctx} (hc : c.Valid) {f : ℕ → ℂ} {c0 b0 : ℚ}
    {q1 q2 : ℚ} {tol : Expr .real}
    (hbridge : ∀ k : ℕ, f k
      = ((c0 : ℝ) : ℂ) / (((2 * ((k : ℕ) : ℂ)) + ((b0 : ℝ) : ℂ)) * (((2 * ((k : ℕ) : ℂ)) + ((b0 : ℝ) : ℂ)) + 2)))
    (hb : (1 : ℝ) ≤ ((b0 : ℚ) : ℝ))
    (hdist : tele2Check c c0 b0 q1 q2 tol = true) :
    Summable f ∧
      ‖tsum f - ((((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I))‖ < tol.denote {} := by
  have hb' : (1 : ℝ) ≤ ((((b0 : ℚ) : ℝ) : ℂ)).re := by simpa using hb
  have hfam := Complex_tsum_telescoping_step2n (c := ((c0 : ℝ) : ℂ))
    (b := ((((b0 : ℚ) : ℝ) : ℂ))) hb'
  obtain ⟨hs, hv⟩ := hfam
  have heq : f
      = (fun j : ℕ => ((c0 : ℝ) : ℂ) / (((2 * ((j : ℕ) : ℂ)) + ((b0 : ℝ) : ℂ)) * (((2 * ((j : ℕ) : ℂ)) + ((b0 : ℝ) : ℂ)) + 2))) :=
    funext hbridge
  rw [heq]
  refine ⟨hs, ?_⟩
  rw [hv]
  have hmem : (((c0 : ℝ) : ℂ) / 2) / ((((b0 : ℚ) : ℝ) : ℂ))
      ∈ tele2Box c c0 b0 := by
    unfold tele2Box
    exact CBox.mem_div
      (CBox.mem_div (mem_ptBox c c0) (by simpa using mem_ptBox c 2))
      (mem_ptBox c b0)
  unfold tele2Check at hdist
  exact distCheck_sound hc hmem hdist

/-! ### Majorant helpers: disc tail + partial sums -/

/-- symmetric disc box of radius `T` (for norm tails) -/
def discBox (c : Ctx) (T : ℚ) : CBox :=
  ⟨Ival.ofRats c.prec (-T) T, Ival.ofRats c.prec (-T) T⟩

theorem mem_discBox {c : Ctx} {z : ℂ} {T : ℚ} (hT : 0 ≤ (T : ℝ))
    (h : ‖z‖ ≤ (T : ℝ)) : z ∈ discBox c T := by
  have hre : |z.re| ≤ (T : ℝ) := le_trans (Complex.abs_re_le_norm z) h
  have him : |z.im| ≤ (T : ℝ) := le_trans (Complex.abs_im_le_norm z) h
  have hTneg : ((-T : ℚ) : ℝ) = -((T : ℚ) : ℝ) := by push_cast; ring
  rw [CBox.mem_def]
  constructor
  · have hlohi := abs_le.1 hre
    exact Ival.mem_ofRats (by rw [hTneg]; exact hlohi.1) hlohi.2
  · have hlohi := abs_le.1 him
    exact Ival.mem_ofRats (by rw [hTneg]; exact hlohi.1) hlohi.2

/-- `1 ≤ k+1` faces as nat `addN`: one side is `var 0`, the other is closed `= 1` -/
def isKPlusOne (e : Expr .nat) : Bool :=
  match e with
  | .call f (.cons .nat a (.cons .nat b .nil)) =>
    if decide (f.name = "+ℕ") then
      match a, b with
      | .var _ 0, .natLit 1 => true
      | .natLit 1, .var _ 0 => true
      | _, _ => false
    else false
  | _ => false

/-- numerator `ofRealC (lit c0)` projection -/
def getC0? (e : Expr .cplx) : Option ℚ :=
  match e with
  | .call g (.cons .real (.lit q) .nil) =>
    if decide (g.name = "ℝ→ℂ") then some q else none
  | _ => none

/-- denominator `natCast (factorial (k+1))` projection; returns unit on match -/
def matchFactDen? (e : Expr .cplx) : Option Unit :=
  match e with
  | .call g (.cons .nat F .nil) =>
    if decide (g.name = "ℕ→ℂ") then
      match F with
      | .call gf (.cons .nat K .nil) =>
        if decide (gf.name = "factorial") then
          if isKPlusOne K then some () else none
        else none
      | _ => none
    else none
  | _ => none

/-- factorial family match: `c0 / (k+1)!`; returns `c0` -/
def matchFact (body : Expr .cplx) : Option ℚ :=
  match body with
  | .call f1 (.cons .cplx C (.cons .cplx D .nil)) =>
    if decide (f1.name = "/ℂ") then
      match getC0? C, matchFactDen? D with
      | some c0, some () => some c0
      | _, _ => none
    else none
  | _ => none

/-- selfpow denominator `((k+1):ℕ):ℂ ^ (k+1)` projection -/
def matchSelfDen? (e : Expr .cplx) : Option Unit :=
  match e with
  | .call npow (.cons .cplx B (.cons .nat E .nil)) =>
    if decide (npow.name = "^ℕℂ") then
      match B with
      | .call gnat (.cons .nat K1 .nil) =>
        if decide (gnat.name = "ℕ→ℂ") then
          if isKPlusOne K1 && isKPlusOne E then some () else none
        else none
      | _ => none
    else none
  | _ => none

/-- selfpow family match: `c0 / ((k+1)^(k+1))`; returns `c0` -/
def matchSelf (body : Expr .cplx) : Option ℚ :=
  match body with
  | .call f1 (.cons .cplx C (.cons .cplx D .nil)) =>
    if decide (f1.name = "/ℂ") then
      match getC0? C, matchSelfDen? D with
      | some c0, some () => some c0
      | _, _ => none
    else none
  | _ => none

/-- mersenne denominator `(2^(k+1) - 1)` projection -/
def matchMersDen? (e : Expr .cplx) : Option Unit :=
  match e with
  | .call sub (.cons .cplx P (.cons .cplx One .nil)) =>
    if decide (sub.name = "-ℂ") then
      match P with
      | .call npow (.cons .cplx B (.cons .nat E .nil)) =>
        if decide (npow.name = "^ℕℂ") then
          match getC0? B, getC0? One with
          | some b, some o =>
            if decide (b = 2) then
              if decide (o = 1) then
                if isKPlusOne E then some () else none
              else none
            else none
          | _, _ => none
        else none
      | _ => none
    else none
  | _ => none

/-- mersenne family match: `c0 / (2^(k+1) - 1)`; returns `c0` -/
def matchMers (body : Expr .cplx) : Option ℚ :=
  match body with
  | .call f1 (.cons .cplx C (.cons .cplx D .nil)) =>
    if decide (f1.name = "/ℂ") then
      match getC0? C, matchMersDen? D with
      | some c0, some () => some c0
      | _, _ => none
    else none
  | _ => none

/-- fib denominator `natCast (fib (k+1))` projection -/
def matchFibDen? (e : Expr .cplx) : Option Unit :=
  match e with
  | .call g (.cons .nat F .nil) =>
    if decide (g.name = "ℕ→ℂ") then
      match F with
      | .call gf (.cons .nat K .nil) =>
        if decide (gf.name = "fib") then
          if isKPlusOne K then some () else none
        else none
      | _ => none
    else none
  | _ => none

/-- fib family match: `c0 / fib(k+1)`; returns `c0` -/
def matchFib (body : Expr .cplx) : Option ℚ :=
  match body with
  | .call f1 (.cons .cplx C (.cons .cplx D .nil)) =>
    if decide (f1.name = "/ℂ") then
      match getC0? C, matchFibDen? D with
      | some c0, some () => some c0
      | _, _ => none
    else none
  | _ => none

/-- factorial tail params for split `N` (with `a = 1`): `M = 1/(N+1)!`, `R = 1/(N+2)` -/
def factM (N : ℕ) : ℚ := 1 / (Nat.factorial (N + 1) : ℚ)
def factR (N : ℕ) : ℚ := 1 / ((N : ℚ) + 2)
def factTub (N : ℕ) : ℚ := factM N / (1 - factR N)

theorem factM_nonneg (N : ℕ) : 0 ≤ ((factM N : ℚ) : ℝ) := by
  unfold factM
  positivity

theorem factR_nonneg (N : ℕ) : 0 ≤ ((factR N : ℚ) : ℝ) := by
  unfold factR
  positivity

theorem factR_lt_one (N : ℕ) : ((factR N : ℚ) : ℝ) < 1 := by
  unfold factR
  have hNeq : (((N : ℚ) + 2 : ℚ) : ℝ) = (N : ℝ) + 2 := by push_cast; ring
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h2 : (0 : ℝ) < (N : ℝ) + 2 := by linarith
  have heq : (((1 : ℚ) / ((N : ℚ) + 2) : ℚ) : ℝ) = 1 / ((N : ℝ) + 2) := by
    push_cast
    ring
  rw [heq, div_lt_one h2]
  linarith

/-- total enclosure: `N` partial sums + disc tail -/
def factEncl (c : Ctx) (body : Expr .cplx) (N : ℕ) : CBox :=
  CBox.add c.prec ((Expr.sum .cplx (.natLit N) body).eval c {}) (discBox c (factTub N))

def factCheck (c : Ctx) (body : Expr .cplx) (N : ℕ) (q1 q2 : ℚ) (tol : Expr .real) : Bool :=
  distCheck c (factEncl c body N) q1 q2 tol

theorem fact_sound {c : Ctx} (hc : c.Valid) {f : ℕ → ℂ} {body : Expr .cplx}
    {N : ℕ} {q1 q2 : ℚ} {tol : Expr .real}
    (hf : ∀ k, f k = body.denote (({} : SEnv).push .nat k))
    (hbridge : ∀ k : ℕ, f k = ((((1 : ℚ)) : ℝ) : ℂ) / ((((Nat.factorial (k + 1) : ℕ)) : ℂ)))
    (hdist : factCheck c body N q1 q2 tol = true) :
    Summable f ∧
      ‖tsum f - ((((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I))‖ < tol.denote {} := by
  have ha : 1 ≤ 1 := le_rfl
  have hmaj := Complex_factorial_majorant (c := ((1 : ℝ) : ℂ)) (a := 1) (N := N) ha
  have hone : (((1 : ℝ)) : ℂ) = (1 : ℂ) := by simp
  have hnorm1 : ‖(((1 : ℝ)) : ℂ)‖ = 1 := by rw [hone, norm_one]
  have htail_bound : ∀ j, ‖f (j + N)‖ ≤ ((factM N : ℚ) : ℝ) * (((factR N : ℚ) : ℝ) ^ j) := by
    intro j
    have hb := hbridge (j + N)
    have e : j + N + 1 = N + j + 1 := by omega
    rw [hb, e]
    have h1 := hmaj j
    rw [hnorm1] at h1
    have hMeq : (1 / (((Nat.factorial (N + 1) : ℕ)) : ℝ))
        = ((factM N : ℚ) : ℝ) := by
      unfold factM
      push_cast
      ring
    have hReq : (1 / (((N : ℝ)) + (((1 : ℕ)) : ℝ) + 1)) = (((factR N : ℚ)) : ℝ) := by
      unfold factR
      have h1N : ((((1 : ℕ)) : ℝ) = (1 : ℝ)) := by push_cast; ring
      rw [h1N]
      push_cast
      ring
    rw [hMeq, hReq] at h1
    have hcast1 : (((((1 : ℚ)) : ℝ)) : ℂ) = (((1 : ℝ)) : ℂ) := by simp
    rw [hcast1]
    exact h1
  have hM0 := factM_nonneg N
  have hR0 := factR_nonneg N
  have hR1 := factR_lt_one N
  obtain ⟨hs_tail, htail_mem⟩ := Complex_geometric_tail hM0 hR0 hR1 N htail_bound
  have hs : Summable f := (summable_nat_add_iff (f := f) N).1 hs_tail
  refine ⟨hs, ?_⟩
  have hsplit := Summable.sum_add_tsum_nat_add (f := f) N hs
  have hpart : (∑ k ∈ Finset.range N, f k)
      ∈ (Expr.sum .cplx (.natLit N) body).eval c {} := by
    have hd : (∑ k ∈ Finset.range N, f k)
        = (Expr.sum .cplx (.natLit N) body).denote {} := by
      have hN : N = (Expr.natLit N).denote ({} : SEnv) := rfl
      exact Expr.sum_eq .cplx (.natLit N) body ({} : SEnv) (f := f) hN hf
    rw [hd]
    have hmem := Expr.eval_sound hc (Expr.sum .cplx (.natLit N) body)
      (ρ := ({} : SEnv)) (σ := {}) IEnv.holds_empty
    simpa [Ty.Mem] using hmem
  have hTnonneg : 0 ≤ (((factTub N : ℚ)) : ℝ) := by
    have hR1' := factR_lt_one N
    have hM0' := factM_nonneg N
    unfold factTub
    have hTub_nn : 0 ≤ ((factM N : ℚ) : ℝ) / (1 - ((factR N : ℚ) : ℝ)) := by
      apply div_nonneg hM0'
      linarith
    have heq : ((((factM N / (1 - factR N) : ℚ))) : ℝ)
        = ((factM N : ℚ) : ℝ) / (1 - ((factR N : ℚ) : ℝ)) := by
      push_cast
      ring
    rwa [heq]
  have htail_in : (∑' j, f (j + N)) ∈ discBox c (factTub N) := by
    apply mem_discBox hTnonneg
    have hle := htail_mem
    have hTub : ((factM N : ℚ) : ℝ) / (1 - ((factR N : ℚ) : ℝ))
        = (((factTub N : ℚ)) : ℝ) := by
      unfold factTub
      push_cast
      ring
    rwa [hTub] at hle
  have htot : (∑ k ∈ Finset.range N, f k) + (∑' j, f (j + N))
      ∈ factEncl c body N := by
    unfold factEncl
    exact CBox.mem_add hpart htail_in
  rw [hsplit] at htot
  unfold factCheck at hdist
  exact distCheck_sound hc htot hdist

/-! ### Selfpow family `1/((k+1)^(k+1))` -/

def selfM (N : ℕ) : ℚ := 1 / ((Nat.pow (N + 1) (N + 1) : ℕ) : ℚ)
def selfR (N : ℕ) : ℚ := 1 / (((N : ℚ) + 1 + 1))
def selfTub (N : ℕ) : ℚ := selfM N / (1 - selfR N)

theorem selfM_nonneg (N : ℕ) : 0 ≤ ((selfM N : ℚ) : ℝ) := by
  unfold selfM; positivity

theorem selfR_nonneg (N : ℕ) : 0 ≤ ((selfR N : ℚ) : ℝ) := by
  unfold selfR; positivity

theorem selfR_lt_one (N : ℕ) : ((selfR N : ℚ) : ℝ) < 1 := by
  unfold selfR
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h2 : (0 : ℝ) < (N : ℝ) + 1 + 1 := by linarith
  have heq : (((1 : ℚ) / ((N : ℚ) + 1 + 1) : ℚ) : ℝ) = 1 / ((N : ℝ) + 1 + 1) := by
    push_cast; ring
  rw [heq, div_lt_one h2]
  linarith

def selfEncl (c : Ctx) (body : Expr .cplx) (N : ℕ) : CBox :=
  CBox.add c.prec ((Expr.sum .cplx (.natLit N) body).eval c {}) (discBox c (selfTub N))

def selfCheck (c : Ctx) (body : Expr .cplx) (N : ℕ) (q1 q2 : ℚ) (tol : Expr .real) : Bool :=
  distCheck c (selfEncl c body N) q1 q2 tol

theorem self_sound {c : Ctx} (hc : c.Valid) {f : ℕ → ℂ} {body : Expr .cplx}
    {N : ℕ} {q1 q2 : ℚ} {tol : Expr .real}
    (hf : ∀ k, f k = body.denote (({} : SEnv).push .nat k))
    (hbridge : ∀ k : ℕ, f k = ((((1 : ℚ)) : ℝ) : ℂ) / (((((k + 1 : ℕ)) : ℂ) ^ (k + 1))))
    (hdist : selfCheck c body N q1 q2 tol = true) :
    Summable f ∧
      ‖tsum f - ((((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I))‖ < tol.denote {} := by
  have ha : 1 ≤ 1 := le_rfl
  have hmaj := Complex_selfpow_majorant (c := ((1 : ℝ) : ℂ)) (a := 1) (N := N) ha
  have hone : (((1 : ℝ)) : ℂ) = (1 : ℂ) := by simp
  have hnorm1 : ‖(((1 : ℝ)) : ℂ)‖ = 1 := by rw [hone, norm_one]
  have htail_bound : ∀ j, ‖f (j + N)‖ ≤ ((selfM N : ℚ) : ℝ) * (((selfR N : ℚ) : ℝ) ^ j) := by
    intro j
    have hb := hbridge (j + N)
    have e1 : j + N + 1 = N + j + 1 := by omega
    rw [hb, e1]
    have h1 := hmaj j
    rw [hnorm1] at h1
    have hcast1 : (((((1 : ℚ)) : ℝ)) : ℂ) = (((1 : ℝ)) : ℂ) := by simp
    rw [hcast1]
    simpa [selfM, selfR, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using h1
  have hM0 := selfM_nonneg N
  have hR0 := selfR_nonneg N
  have hR1 := selfR_lt_one N
  obtain ⟨hs_tail, htail_mem⟩ := Complex_geometric_tail hM0 hR0 hR1 N htail_bound
  have hs : Summable f := (summable_nat_add_iff (f := f) N).1 hs_tail
  refine ⟨hs, ?_⟩
  have hsplit := Summable.sum_add_tsum_nat_add (f := f) N hs
  have hpart : (∑ k ∈ Finset.range N, f k)
      ∈ (Expr.sum .cplx (.natLit N) body).eval c {} := by
    have hd : (∑ k ∈ Finset.range N, f k)
        = (Expr.sum .cplx (.natLit N) body).denote {} := by
      have hN : N = (Expr.natLit N).denote ({} : SEnv) := rfl
      exact Expr.sum_eq .cplx (.natLit N) body ({} : SEnv) (f := f) hN hf
    rw [hd]
    have hmem := Expr.eval_sound hc (Expr.sum .cplx (.natLit N) body)
      (ρ := ({} : SEnv)) (σ := {}) IEnv.holds_empty
    simpa [Ty.Mem] using hmem
  have hTnonneg : 0 ≤ (((selfTub N : ℚ)) : ℝ) := by
    have hR1' := selfR_lt_one N
    have hM0' := selfM_nonneg N
    unfold selfTub
    have hTub_nn : 0 ≤ ((selfM N : ℚ) : ℝ) / (1 - ((selfR N : ℚ) : ℝ)) := by
      apply div_nonneg hM0'; linarith
    have heq : ((((selfM N / (1 - selfR N) : ℚ))) : ℝ)
        = ((selfM N : ℚ) : ℝ) / (1 - ((selfR N : ℚ) : ℝ)) := by
      push_cast; ring
    rwa [heq]
  have htail_in : (∑' j, f (j + N)) ∈ discBox c (selfTub N) := by
    apply mem_discBox hTnonneg
    have hle := htail_mem
    have hTub : ((selfM N : ℚ) : ℝ) / (1 - ((selfR N : ℚ) : ℝ))
        = (((selfTub N : ℚ)) : ℝ) := by
      unfold selfTub; push_cast; ring
    rwa [hTub] at hle
  have htot : (∑ k ∈ Finset.range N, f k) + (∑' j, f (j + N))
      ∈ selfEncl c body N := by
    unfold selfEncl
    exact CBox.mem_add hpart htail_in
  rw [hsplit] at htot
  unfold selfCheck at hdist
  exact distCheck_sound hc htot hdist

/-! ### Mersenne family `1/(2^(k+1)-1)` -/

def mersM (N : ℕ) : ℚ := 2 / ((Nat.pow 2 (N + 1) : ℕ) : ℚ)
def mersR : ℚ := 1 / 2
def mersTub (N : ℕ) : ℚ := mersM N / (1 - mersR)

theorem mersM_nonneg (N : ℕ) : 0 ≤ ((mersM N : ℚ) : ℝ) := by
  unfold mersM; positivity

theorem mersR_nonneg : 0 ≤ ((mersR : ℚ) : ℝ) := by
  unfold mersR; positivity

theorem mersR_lt_one : ((mersR : ℚ) : ℝ) < 1 := by
  unfold mersR; norm_num

def mersEncl (c : Ctx) (body : Expr .cplx) (N : ℕ) : CBox :=
  CBox.add c.prec ((Expr.sum .cplx (.natLit N) body).eval c {}) (discBox c (mersTub N))

def mersCheck (c : Ctx) (body : Expr .cplx) (N : ℕ) (q1 q2 : ℚ) (tol : Expr .real) : Bool :=
  distCheck c (mersEncl c body N) q1 q2 tol

theorem mers_sound {c : Ctx} (hc : c.Valid) {f : ℕ → ℂ} {body : Expr .cplx}
    {N : ℕ} {q1 q2 : ℚ} {tol : Expr .real}
    (hf : ∀ k, f k = body.denote (({} : SEnv).push .nat k))
    (hbridge : ∀ k : ℕ, f k = ((((1 : ℚ)) : ℝ) : ℂ) / (((((2 : ℚ)) : ℝ) : ℂ) ^ (k + 1) - 1))
    (hdist : mersCheck c body N q1 q2 tol = true) :
    Summable f ∧
      ‖tsum f - ((((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I))‖ < tol.denote {} := by
  have hb : (2 : ℝ) ≤ 2 := le_rfl
  have ha : 1 ≤ 1 := le_rfl
  have hmaj := Complex_mersenne_majorant (c := ((1 : ℝ) : ℂ)) (b := 2) (N := N) (a := 1) hb ha
  have hone : (((1 : ℝ)) : ℂ) = (1 : ℂ) := by simp
  have hnorm1 : ‖(((1 : ℝ)) : ℂ)‖ = 1 := by rw [hone, norm_one]
  have htail_bound : ∀ j, ‖f (j + N)‖ ≤ ((mersM N : ℚ) : ℝ) * (((mersR : ℚ) : ℝ) ^ j) := by
    intro j
    have hbj := hbridge (j + N)
    have e : j + N + 1 = N + j + 1 := by omega
    rw [hbj, e]
    have h1 := hmaj j
    rw [hnorm1] at h1
    have hcast1 : (((((1 : ℚ)) : ℝ)) : ℂ) = (((1 : ℝ)) : ℂ) := by simp
    have hcast2 : (((((2 : ℚ)) : ℝ)) : ℂ) = (((2 : ℝ)) : ℂ) := by simp
    rw [hcast1, hcast2]
    simpa [mersM, mersR, Nat.cast_pow] using h1
  have hM0 := mersM_nonneg N
  have hR0 := mersR_nonneg
  have hR1 := mersR_lt_one
  obtain ⟨hs_tail, htail_mem⟩ := Complex_geometric_tail hM0 hR0 hR1 N htail_bound
  have hs : Summable f := (summable_nat_add_iff (f := f) N).1 hs_tail
  refine ⟨hs, ?_⟩
  have hsplit := Summable.sum_add_tsum_nat_add (f := f) N hs
  have hpart : (∑ k ∈ Finset.range N, f k)
      ∈ (Expr.sum .cplx (.natLit N) body).eval c {} := by
    have hd : (∑ k ∈ Finset.range N, f k)
        = (Expr.sum .cplx (.natLit N) body).denote {} := by
      have hN : N = (Expr.natLit N).denote ({} : SEnv) := rfl
      exact Expr.sum_eq .cplx (.natLit N) body ({} : SEnv) (f := f) hN hf
    rw [hd]
    have hmem := Expr.eval_sound hc (Expr.sum .cplx (.natLit N) body)
      (ρ := ({} : SEnv)) (σ := {}) IEnv.holds_empty
    simpa [Ty.Mem] using hmem
  have hTnonneg : 0 ≤ (((mersTub N : ℚ)) : ℝ) := by
    have hM0' := mersM_nonneg N
    unfold mersTub
    have hTub_nn : 0 ≤ ((mersM N : ℚ) : ℝ) / (1 - ((mersR : ℚ) : ℝ)) := by
      apply div_nonneg hM0'
      unfold mersR
      norm_num
    have heq : ((((mersM N / (1 - mersR) : ℚ))) : ℝ)
        = ((mersM N : ℚ) : ℝ) / (1 - ((mersR : ℚ) : ℝ)) := by
      push_cast; ring
    rwa [heq]
  have htail_in : (∑' j, f (j + N)) ∈ discBox c (mersTub N) := by
    apply mem_discBox hTnonneg
    have hle := htail_mem
    have hTub : ((mersM N : ℚ) : ℝ) / (1 - ((mersR : ℚ) : ℝ))
        = (((mersTub N : ℚ)) : ℝ) := by
      unfold mersTub; push_cast; ring
    rwa [hTub] at hle
  have htot : (∑ k ∈ Finset.range N, f k) + (∑' j, f (j + N))
      ∈ mersEncl c body N := by
    unfold mersEncl
    exact CBox.mem_add hpart htail_in
  rw [hsplit] at htot
  unfold mersCheck at hdist
  exact distCheck_sound hc htot hdist

/-! ### Fib family `1/fib(k+1)` -/

def fibM (N : ℕ) : ℚ := 1 / ((Nat.fib (N + 1) : ℕ) : ℚ)
def fibR : ℚ := 2 / 3
def fibTub (N : ℕ) : ℚ := fibM N / (1 - fibR)

theorem fibM_nonneg (N : ℕ) : 0 ≤ ((fibM N : ℚ) : ℝ) := by
  unfold fibM; positivity

theorem fibR_nonneg : 0 ≤ ((fibR : ℚ) : ℝ) := by
  unfold fibR; positivity

theorem fibR_lt_one : ((fibR : ℚ) : ℝ) < 1 := by
  unfold fibR; norm_num

def fibEncl (c : Ctx) (body : Expr .cplx) (N : ℕ) : CBox :=
  CBox.add c.prec ((Expr.sum .cplx (.natLit N) body).eval c {}) (discBox c (fibTub N))

def fibCheck (c : Ctx) (body : Expr .cplx) (N : ℕ) (q1 q2 : ℚ) (tol : Expr .real) : Bool :=
  distCheck c (fibEncl c body N) q1 q2 tol

theorem fib_sound {c : Ctx} (hc : c.Valid) {f : ℕ → ℂ} {body : Expr .cplx}
    {N : ℕ} {q1 q2 : ℚ} {tol : Expr .real} (hN : 1 ≤ N)
    (hf : ∀ k, f k = body.denote (({} : SEnv).push .nat k))
    (hbridge : ∀ k : ℕ, f k = ((((1 : ℚ)) : ℝ) : ℂ) / ((((Nat.fib (k + 1) : ℕ)) : ℂ)))
    (hdist : fibCheck c body N q1 q2 tol = true) :
    Summable f ∧
      ‖tsum f - ((((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I))‖ < tol.denote {} := by
  have hmaj := Complex_fib_majorant (c := ((1 : ℝ) : ℂ)) (N := N) hN
  have hone : (((1 : ℝ)) : ℂ) = (1 : ℂ) := by simp
  have hnorm1 : ‖(((1 : ℝ)) : ℂ)‖ = 1 := by rw [hone, norm_one]
  have htail_bound : ∀ j, ‖f (j + N)‖ ≤ ((fibM N : ℚ) : ℝ) * (((fibR : ℚ) : ℝ) ^ j) := by
    intro j
    have hb := hbridge (j + N)
    have e : j + N + 1 = N + j + 1 := by omega
    rw [hb, e]
    have h1 := hmaj j
    rw [hnorm1] at h1
    have hcast1 : (((((1 : ℚ)) : ℝ)) : ℂ) = (((1 : ℝ)) : ℂ) := by simp
    rw [hcast1]
    simpa [fibM, fibR] using h1
  have hM0 := fibM_nonneg N
  have hR0 := fibR_nonneg
  have hR1 := fibR_lt_one
  obtain ⟨hs_tail, htail_mem⟩ := Complex_geometric_tail hM0 hR0 hR1 N htail_bound
  have hs : Summable f := (summable_nat_add_iff (f := f) N).1 hs_tail
  refine ⟨hs, ?_⟩
  have hsplit := Summable.sum_add_tsum_nat_add (f := f) N hs
  have hpart : (∑ k ∈ Finset.range N, f k)
      ∈ (Expr.sum .cplx (.natLit N) body).eval c {} := by
    have hd : (∑ k ∈ Finset.range N, f k)
        = (Expr.sum .cplx (.natLit N) body).denote {} := by
      have hN : N = (Expr.natLit N).denote ({} : SEnv) := rfl
      exact Expr.sum_eq .cplx (.natLit N) body ({} : SEnv) (f := f) hN hf
    rw [hd]
    have hmem := Expr.eval_sound hc (Expr.sum .cplx (.natLit N) body)
      (ρ := ({} : SEnv)) (σ := {}) IEnv.holds_empty
    simpa [Ty.Mem] using hmem
  have hTnonneg : 0 ≤ (((fibTub N : ℚ)) : ℝ) := by
    have hM0' := fibM_nonneg N
    unfold fibTub
    have hTub_nn : 0 ≤ ((fibM N : ℚ) : ℝ) / (1 - ((fibR : ℚ) : ℝ)) := by
      apply div_nonneg hM0'
      unfold fibR
      norm_num
    have heq : ((((fibM N / (1 - fibR) : ℚ))) : ℝ)
        = ((fibM N : ℚ) : ℝ) / (1 - ((fibR : ℚ) : ℝ)) := by
      push_cast; ring
    rwa [heq]
  have htail_in : (∑' j, f (j + N)) ∈ discBox c (fibTub N) := by
    apply mem_discBox hTnonneg
    have hle := htail_mem
    have hTub : ((fibM N : ℚ) : ℝ) / (1 - ((fibR : ℚ) : ℝ))
        = (((fibTub N : ℚ)) : ℝ) := by
      unfold fibTub; push_cast; ring
    rwa [hTub] at hle
  have htot : (∑ k ∈ Finset.range N, f k) + (∑' j, f (j + N))
      ∈ fibEncl c body N := by
    unfold fibEncl
    exact CBox.mem_add hpart htail_in
  rw [hsplit] at htot
  unfold fibCheck at hdist
  exact distCheck_sound hc htot hdist

/-! ### Divergence families -/

/-- alternating-harmonic shape `(-1)^k/(k+1)` match -/
def matchAltHarm (body : Expr .cplx) : Option Unit :=
  match body with
  | .call f1 (.cons .cplx Num (.cons .cplx Den .nil)) =>
    if decide (f1.name = "/ℂ") then
      match Num with
      | .call npow (.cons .cplx Base (.cons .nat E .nil)) =>
        if decide (npow.name = "^ℕℂ") then
          match getC0? Base with
          | some b =>
            if decide (b = -1) then
              match E with
              | .var _ 0 =>
                match Den with
                | .call add (.cons .cplx Ka (.cons .cplx Kb .nil)) =>
                  if decide (add.name = "+ℂ") then
                    match Ka, Kb with
                    | .call gk (.cons .nat (.var _ 0) .nil),
                      .call g1 (.cons .real (.lit q) .nil) =>
                      if decide (gk.name = "ℕ→ℂ") then
                        if decide (g1.name = "ℝ→ℂ") then
                          if decide (q = 1) then some () else none
                        else none
                      else none
                    | _, _ => none
                  else none
                | _ => none
              | _ => none
            else none
          | _ => none
        else none
      | _ => none
    else none
  | _ => none

theorem altHarm_not_summable_sound {f : ℕ → ℂ}
    (hbridge : ∀ k : ℕ, f k = (((-1 : ℂ) ^ k)) / ((((k : ℕ)) : ℂ) + (((1 : ℕ)) : ℂ))) :
    ¬ Summable f := by
  apply Complex_not_summable_of_harmonic_lower (N := 0) (a := 1)
  intro j
  have hb := hbridge j
  have hnum : ‖((-1 : ℂ) ^ j)‖ = 1 := by simp
  have hden : ‖((((j : ℕ)) : ℂ) + (((1 : ℕ)) : ℂ))‖ = ((j : ℝ) + 1) := by
    have h : ((((j : ℕ)) : ℂ) + (((1 : ℕ)) : ℂ)) = ((((j + 1 : ℕ)) : ℂ)) := by
      push_cast; ring
    rw [h, Complex.norm_natCast]
    push_cast; ring
  have hnorm : ‖f j‖ = 1 * (1 / (((j : ℝ)) + (((0 + 1 : ℕ)) : ℝ))) := by
    rw [hb, norm_div, hnum, hden]
    push_cast; ring
  have e0 : j + 0 = j := by omega
  rw [e0, hnorm]

/-- constant-one shape match -/
def matchConstOne (body : Expr .cplx) : Option Unit :=
  match body with
  | .call g (.cons .real (.lit q) .nil) =>
    if decide (g.name = "ℝ→ℂ") then
      if decide (q = 1) then some () else none
    else none
  | _ => none

theorem const_not_summable_sound {f : ℕ → ℂ}
    (hbridge : ∀ k : ℕ, f k = 1) : ¬ Summable f := by
  apply Complex_not_summable_of_lower_bound (c := 1) (N := 0) (by norm_num)
  intro k _
  rw [hbridge k]
  simp

end Lynth.Interval.Series
