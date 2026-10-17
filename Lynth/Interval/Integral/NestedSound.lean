import Lynth.Interval.Integral.NestedCert
import Lynth.Interval.Integral.Math.NestedAnalysis

/-! Interval-specific proof bridges. Portable analytic and change-of-variable
obligations live in Math/NestedAnalysis. Every Gauss panel explicitly consumes
the same real affine Gauss error theorem as the one-dimensional backend. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl

theorem safeExp_sound {c : Ctx} {X : Ival} {x : ℝ} (hx : x ∈ X) :
    Real.exp x ∈ safeExp c X := by
  -- Monotonicity, expPt enclosures, and Intgrl.exp_negative_nat.
  sorry

/-- Parameter boxes are real in an accurate sample; complex boxes are used
only by analytic bounds and uniform endpoint majorants. -/
def EnvMem (xs : List ℝ) (env : Array Ival) : Prop :=
  xs.length = env.size ∧ ∀ i, i < env.size → xs[i]?.getD 0 ∈ env[i]!

def MemoValid (memo : Memo) : Prop :=
  ∀ e env I, memo[key e env]? = some I → e.scoped env.size = true →
    ∀ xs, EnvMem xs env → e.Converges xs ∧ e.real xs ∈ I

theorem evalWith_sound {c : Ctx} (hc : c.Valid) {memo : Memo} (hm : MemoValid memo)
    {e : Expr} {env : Array Ival} {xs : List ℝ} {I : Ival}
    (hs : e.scoped env.size = true) (hx : EnvMem xs env)
    (h : evalWith c memo e env = some I) : e.Converges xs ∧ e.real xs ∈ I := by
  sorry

theorem coarsePanel_sound {c : Ctx} (hc : c.Valid) {e : Expr}
    {env : Array Ival} {xs : List ℝ} (hx : EnvMem xs env)
    (hs : e.scoped (env.size+1) = true) {a b : Dy} (hab : a.toReal ≤ b.toReal)
    {I : Ival} (h : coarsePanel c e env a b = some I) :
    IntervalIntegrable (fun x => e.real (xs++[x])) MeasureTheory.volume a.toReal b.toReal ∧
      (∫ x in a.toReal..b.toReal, e.real (xs++[x])) ∈ I := by
  sorry

theorem analytic_sound {c : Ctx} (hc : c.Valid) {e : Expr}
    {env : Array Ival} {xs : List ℝ} (hx : EnvMem xs env)
    (hs : e.scoped (env.size+1) = true) {a b ρ M : Dy} (hab : a.toReal < b.toReal)
    (h : analytic c e env a b ρ = some M) :
    1 < ρ.toReal ∧ 0 ≤ M.toReal ∧ ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F ((affine a.toReal b.toReal) '' ellipse ρ.toReal) ∧
      (∀ z ∈ ellipse ρ.toReal, ‖F (affine a.toReal b.toReal z)‖ ≤ M.toReal) ∧
      (∀ x ∈ Set.Ioo a.toReal b.toReal, F x = (e.real (xs++[x]) : ℂ)) := by
  sorry

theorem samples_sound {c : Ctx} (hc : c.Valid) {memo : Memo} (hm : MemoValid memo)
    {e : Expr} {env : Array Ival} {xs : List ℝ} (hx : EnvMem xs env)
    (hs : e.scoped (env.size+1) = true) {a b : Dy}
    {t : NodeTable} {x : Fin t.roots.length → ℝ} (ht : t.check c = true)
    (hn : ∀ i, x i ∈ rootIval (t.roots[i]) ∧
      gaussWeight t.roots.length (x i) ∈ (t.weights c).getD i.val Ival.top)
    {I : Ival} (h : samples c memo e env a b t (t.weights c) = some I) :
    ((b.toReal-a.toReal)/2) * gaussSum x (fun z =>
      e.real (xs++[(a.toReal+b.toReal)/2+(b.toReal-a.toReal)/2*z])) ∈ I := by
  sorry

theorem piece_sound {c : Ctx} (hc : c.Valid) {memo : Memo} (hm : MemoValid memo)
    {e : Expr} {env : Array Ival} {xs : List ℝ} (hx : EnvMem xs env)
    (hs : e.scoped (env.size+1) = true) {tables : Array NodeTable}
    (ht : tables.all (fun t => t.check c) = true) {p : Piece}
    (hab : p.a.toReal ≤ p.b.toReal) {I : Ival}
    (h : piece c memo e env tables (tables.map (fun t => t.weights c)) p = some I) :
    IntervalIntegrable (fun x => e.real (xs++[x])) MeasureTheory.volume p.a.toReal p.b.toReal ∧
      (∫ x in p.a.toReal..p.b.toReal, e.real (xs++[x])) ∈ I := by
  cases hp : p.method with
  | direct => exact coarsePanel_sound hc hx hs hab (by simpa [piece,hp] using h)
  | gauss i ρ =>
    simp only [piece,hp] at h
    split at h
    · simp at h
    · rename_i hlt
      have hab' := Dy.toReal_lt_of_ltB (show Dy.ltB p.a p.b = true by simpa using hlt)
      cases hti : tables[i]? with
      | none => simp [hti] at h
      | some t =>
        have hcheck := (Array.all_eq_true_iff_forall_mem.mp ht) t (Array.mem_of_getElem? hti)
        cases hM : analytic c e env p.a p.b ρ with
        | none => simp [hti,hM] at h
        | some M =>
          cases herr : errorBound c t.roots.length p.a p.b ρ M with
          | none => simp [hti,hM,herr] at h
          | some err =>
            cases hS : samples c memo e env p.a p.b t (t.weights c) with
            | none => simp [hti,hM,herr,hS] at h
            | some S =>
              have heq : Ival.widen c.prec S err = I := by
                simpa [hti,hM,herr,hS] using h
              subst I
              obtain ⟨hρ,hM0,F,hF,hbound,hagree⟩ := analytic_sound hc hx hs hab' hM
              obtain ⟨x,hxg,hmem⟩ := t.sound hc hcheck
              have hn := NodeTable.positive hcheck
              have hg := gauss_error_real_affine hn hxg hab' hρ hM0 hF hbound hagree
              exact ⟨hg.1,Ival.mem_widen (samples_sound hc hm hx hs hcheck hmem hS)
                (hg.2.trans (errorBound_sound hn hab' hρ hM0 herr))⟩

/-- Assembly joins panel proofs, endpoint remainders and substitutions, and
establishes ordinary convergence recursively throughout each real domain. -/
theorem assembly_sound {c : Ctx} (hc : c.Valid) {memo : Memo} (hm : MemoValid memo)
    {tables : Array NodeTable} (ht : tables.all (fun t => t.check c) = true)
    (hpanels : ∀ e env xs, EnvMem xs env → e.scoped (env.size+1) = true →
      ∀ p I, p.a.toReal ≤ p.b.toReal →
        piece c memo e env tables (tables.map (fun t => t.weights c)) p = some I →
        IntervalIntegrable (fun x => e.real (xs++[x])) MeasureTheory.volume p.a.toReal p.b.toReal ∧
          (∫ x in p.a.toReal..p.b.toReal, e.real (xs++[x])) ∈ I)
    {entry : Entry} {I : Ival}
    (h : entryEncl c memo tables (tables.map (fun t => t.weights c)) entry = some I) :
    ∀ xs, EnvMem xs entry.env → entry.expr.Converges xs ∧ entry.expr.real xs ∈ I := by
  sorry

theorem entry_sound {c : Ctx} (hc : c.Valid) {memo : Memo} (hm : MemoValid memo)
    {tables : Array NodeTable} (ht : tables.all (fun t => t.check c) = true)
    {entry : Entry} {I : Ival}
    (h : entryEncl c memo tables (tables.map (fun t => t.weights c)) entry = some I) :
    ∀ xs, EnvMem xs entry.env → entry.expr.Converges xs ∧ entry.expr.real xs ∈ I :=
  assembly_sound hc hm ht (fun _ _ _ hx hs _ _ hab hp => piece_sound hc hm hx hs ht hab hp) h

/-- The remaining induction transfers checked entries through canonical
keys and resizing buckets. Its entry premise retains the panel proof chain. -/
theorem replay_induction {c : Ctx} (hc : c.Valid)
    (hentries : ∀ (memo : Memo) (tables : Array NodeTable), MemoValid memo →
      tables.all (fun t => t.check c) = true → ∀ (entry : Entry) (I : Ival),
      entryEncl c memo tables (tables.map (fun t => t.weights c)) entry = some I →
      ∀ xs, EnvMem xs entry.env → entry.expr.Converges xs ∧ entry.expr.real xs ∈ I)
    {cert : Cert} {memo : Memo} (h : replay c cert = some memo) : MemoValid memo := by
  sorry

theorem replay_sound {c : Ctx} (hc : c.Valid) {cert : Cert} {memo : Memo}
    (h : replay c cert = some memo) : MemoValid memo :=
  replay_induction hc (fun _ _ hm ht _ _ he => entry_sound hc hm ht he) h

theorem enclosure_sound {c : Ctx} (hc : c.Valid) {e : Expr} {cert : Cert} {I : Ival}
    (h : enclosure c e cert = some I) : e.Converges [] ∧ e.real [] ∈ I := by
  unfold enclosure at h
  split at h
  · simp at h
  · rename_i hs
    cases hr : replay c cert with
    | none => simp [hr] at h
    | some memo =>
      cases hv : evalWith c memo e #[] with
      | none => simp [hr,hv] at h
      | some V =>
        have heq : V = I := (show V.isFinite = true ∧ V = I by simpa [hr,hv] using h).2
        subst I
        exact evalWith_sound hc (replay_sound hc hr) (by simpa using hs)
          ⟨rfl,by simp⟩ hv

theorem check_sound {c : Ctx} (hc : c.Valid) {e : Expr} {cert : Cert} {q : ℚ} {T : Term}
    (h : check c e cert q T = true) : e.Converges [] ∧ |e.real []-(q:ℝ)| < T.real 0 := by
  cases hi : enclosure c e cert with
  | none => simp [check,hi] at h
  | some I =>
    have hh := enclosure_sound hc hi
    exact ⟨hh.1,closeCheck_sound hc hh.2 (by simpa [check,hi] using h)⟩

theorem result_of_check {f : ℝ → ℝ} {a b tol : ℝ}
    {e A B : Expr} {T : Term} {c : Ctx} {k : NDomain} {cert : Cert} {q : ℚ}
    (hc : c.Valid) (hf : ∀ x, f x = e.real [x])
    (ha : a = A.real []) (hb : b = B.real []) (htol : tol = T.real 0)
    (h : check c (.integral k A B e) cert q T = true) :
    k.Converges f a b ∧ |k.value f a b-(q:ℝ)| < tol := by
  obtain rfl : f = fun x => e.real [x] := funext hf
  subst a; subst b; subst tol
  have hh := check_sound hc h
  exact ⟨hh.1.2.2.1,hh.2⟩

theorem closedRight {f : ℝ → ℝ} {a tol : ℝ} {q : ℚ}
    (h : NDomain.right.Converges f a 0 ∧ |NDomain.right.value f a 0-(q:ℝ)| < tol) :
    MeasureTheory.IntegrableOn f (Set.Ici a) ∧
      |(∫ x in Set.Ici a, f x)-(q:ℝ)| < tol := by
  exact ⟨(integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr h.1,
    by simpa only [NDomain.right_closed] using h.2⟩

theorem closedLeft {f : ℝ → ℝ} {a tol : ℝ} {q : ℚ}
    (h : NDomain.left.Converges f a 0 ∧ |NDomain.left.value f a 0-(q:ℝ)| < tol) :
    MeasureTheory.IntegrableOn f (Set.Iic a) ∧
      |(∫ x in Set.Iic a, f x)-(q:ℝ)| < tol := by
  exact ⟨(integrableOn_Iic_iff_integrableOn_Iio (by finiteness)).mpr h.1,
    by simpa only [NDomain.left_closed] using h.2⟩

end Lynth.Interval.Integral.Nested
