import Lynth.Interval.Integral.NestedCert
import Lynth.Interval.Integral.NestedPrimitiveProof
import Lynth.Interval.Integral.NestedFormulaProof
import Lynth.Interval.Integral.NestedScaleProof
import Lynth.Interval.Integral.NestedLogEndpointProof
import Lynth.Interval.Integral.NestedMeasurable
import Lynth.Interval.Integral.NestedSemantics
import Lynth.Interval.Integral.NestedMemoProof
import Lynth.Interval.Integral.NestedNormalizationProof
import Lynth.Interval.Integral.Math.NestedAnalysis
import Lynth.Interval.Integral.Math.NestedChange

/-! Interval-specific proof bridges. Portable analytic and change-of-variable
obligations live in Math/NestedAnalysis. Every Gauss panel explicitly consumes
the same real affine Gauss error theorem as the one-dimensional backend. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl Fns

/-- Parameter boxes are real in an accurate sample; complex boxes are used
only by analytic bounds and uniform endpoint majorants. -/
def EnvMem (xs : List ℝ) (env : Array Ival) : Prop :=
  xs.length = env.size ∧ ∀ i, i < env.size → xs[i]?.getD 0 ∈ env[i]!

theorem EnvMem.push {xs : List ℝ} {env : Array Ival} (h : EnvMem xs env)
    {x : ℝ} {X : Ival} (hx : x ∈ X) : EnvMem (xs++[x]) (env.push X) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hb : i < env.size
  · have hs : i < xs.length := h.1 ▸ hb
    simpa [List.getElem?_append, hs, hb, getElem!_pos (env.push X) i hi,
      Array.getElem_push_lt hb] using h.2 i hb
  · have he : i = env.size := by simp only [Array.size_push] at hi; omega
    subst i
    simpa [List.getElem?_append, h.1] using hx

theorem envCheck_sound {env : Array Ival} (h : envCheck env = true) :
    ∃ xs, EnvMem xs env := by
  let pick : Ival → ℝ := fun I =>
    match I.lo,I.hi with
    | some a,_ => a.toReal
    | none,some b => b.toReal
    | none,none => 0
  have hpick : ∀ I ∈ env, pick I ∈ I := by
    intro I hI
    have hh := Array.all_eq_true_iff_forall_mem.mp h I hI
    cases hlo : I.lo with
    | none =>
      cases hhi : I.hi with
      | none => simp [pick,Ival.mem_def,Ival.LoLe,Ival.LeHi,hlo,hhi]
      | some b => simp [pick,Ival.mem_def,Ival.LoLe,Ival.LeHi,hlo,hhi]
    | some a =>
      cases hhi : I.hi with
      | none => simp [pick,Ival.mem_def,Ival.LoLe,Ival.LeHi,hlo,hhi]
      | some b =>
        have hab : a.toReal ≤ b.toReal := Dy.toReal_le_of_leB (by simpa [envCheck,hlo,hhi] using hh)
        simp [pick,Ival.mem_def,Ival.LoLe,Ival.LeHi,hlo,hhi,hab]
  refine ⟨env.toList.map pick,by simp,?_⟩
  intro i hi
  have hh := hpick env[i] (Array.getElem_mem hi)
  simpa [List.getElem?_map,Array.getElem?_toList,Array.getElem?_eq_getElem hi,
    getElem!_pos env i hi] using hh

/-- Erasing unused parameter boxes preserves a semantic assertion once the
original environment admits a parameter assignment. -/
theorem meaning_mask {e : Expr} {env : Array Ival} {I : Ival}
    (henv : ∃ zs, EnvMem zs env)
    (hsource : ∀ zs, EnvMem zs env → e.Converges zs ∧ e.real zs ∈ I)
    {xs : List ℝ} (hx : EnvMem xs (maskEnv e env)) :
    e.Converges xs ∧ e.real xs ∈ I := by
  obtain ⟨zs,hz⟩ := henv
  have hlen : xs.length = env.size := by simpa [maskEnv] using hx.1
  let ys : List ℝ := List.ofFn fun i : Fin env.size =>
    if e.uses i then xs[i.val]?.getD 0 else zs[i.val]?.getD 0
  have hylen : ys.length = env.size := by simp [ys]
  have hy : EnvMem ys env := by
    refine ⟨hylen,?_⟩
    intro i hi
    by_cases hu : e.uses i = true
    · have hh := hx.2 i (by simpa [maskEnv] using hi)
      simpa [ys,maskEnv,hi,hu,getElem!_pos env i hi] using hh
    · have hh := hz.2 i hi
      simpa [ys,hi,hu,getElem!_pos env i hi] using hh
  have hagree : ∀ i, e.uses i = true → xs[i]?.getD 0 = ys[i]?.getD 0 := by
    intro i hu
    by_cases hi : i < env.size
    · simp [ys,hi,hu]
    · have hxs : xs[i]? = none := List.getElem?_eq_none (by omega)
      have hys : ys[i]? = none := List.getElem?_eq_none (by omega)
      simp only [hxs,hys]
  have he := env_getD_eq_of_uses (e := e) (hlen.trans hylen.symm) hagree
  have hh := hsource ys hy
  exact ⟨he.2.mpr hh.1,he.1 ▸ hh.2⟩

theorem meaning_unmask {e : Expr} {env : Array Ival} {I : Ival}
    (hmasked : ∀ ys, EnvMem ys (maskEnv e env) → e.Converges ys ∧ e.real ys ∈ I)
    {xs : List ℝ} (hx : EnvMem xs env) : e.Converges xs ∧ e.real xs ∈ I := by
  let ys : List ℝ := List.ofFn fun i : Fin env.size =>
    if e.uses i then xs[i.val]?.getD 0 else 0
  have hylen : ys.length = env.size := by simp [ys]
  have hy : EnvMem ys (maskEnv e env) := by
    refine ⟨by simp [ys,maskEnv],?_⟩
    intro i hi
    have hib : i < env.size := by simpa [maskEnv] using hi
    by_cases hu : e.uses i = true
    · have hh := hx.2 i hib
      simpa [ys,maskEnv,hi,hib,hu,getElem!_pos env i hib] using hh
    · simpa [ys,maskEnv,hi,hib,hu] using (Ival.mem_zero : (0:ℝ) ∈ Ival.zero)
  have hagree : ∀ i, e.uses i = true → xs[i]?.getD 0 = ys[i]?.getD 0 := by
    intro i hu
    by_cases hi : i < env.size
    · simp [ys,hi,hu]
    · have hxlen := hx.1
      have hxs : xs[i]? = none := List.getElem?_eq_none (by omega)
      have hys : ys[i]? = none := List.getElem?_eq_none (by omega)
      simp only [hxs,hys]
  have he := env_getD_eq_of_uses (e := e) (hx.1.trans hylen.symm) hagree
  have hh := hmasked ys hy
  exact ⟨he.2.mpr hh.1,he.1 ▸ hh.2⟩

def MemoValid (memo : Memo) : Prop :=
  ∀ e env I, memo[key e env]? = some I → e.scoped env.size = true →
    ∀ xs, EnvMem xs env → e.Converges xs ∧ e.real xs ∈ I

/-- The assertion stored at a canonical key covers every original query
represented by that key. -/
def KeyMeaning (k : Key) (I : Ival) : Prop :=
  ∀ e env, key e env = k → e.scoped env.size = true →
    ∀ xs, EnvMem xs env → e.Converges xs ∧ e.real xs ∈ I

theorem keyMeaning_of_source {e : Expr} {env : Array Ival} {I : Ival}
    (hen : envCheck env = true) (hs : e.scoped env.size = true)
    (hsource : ∀ xs, EnvMem xs env → e.Converges xs ∧ e.real xs ∈ I) :
    KeyMeaning (key e env) I := by
  have hcanon : ∀ zs, EnvMem zs env →
      (key e env).expr.Converges zs ∧ (key e env).expr.real zs ∈ I := by
    intro zs hz
    have hh := hsource zs hz
    have hn := normalized_semantics e zs (by simpa only [hz.1] using hs)
    constructor
    · change (normalized env.size e).Converges zs
      rw [← hz.1]
      exact hn.1.mpr hh.1
    · change (normalized env.size e).real zs ∈ I
      rw [← hz.1,hn.2 hh.1]
      exact hh.2
  have hmasked : ∀ zs, EnvMem zs (maskEnv (key e env).expr env) →
      (key e env).expr.Converges zs ∧ (key e env).expr.real zs ∈ I :=
    fun _ hz => meaning_mask (envCheck_sound hen) hcanon hz
  intro q qenv hkey hscope xs hx
  have hqcanon : ∀ zs, EnvMem zs (maskEnv (key q qenv).expr qenv) →
      (key q qenv).expr.Converges zs ∧ (key q qenv).expr.real zs ∈ I := by
    intro zs hz
    have he : (key q qenv).expr = (key e env).expr := congrArg Key.expr hkey
    have he' : maskEnv (key q qenv).expr qenv = maskEnv (key e env).expr env := by
      calc
        _ = (key q qenv).env := (key_env q qenv).symm
        _ = (key e env).env := congrArg Key.env hkey
        _ = _ := key_env e env
    rw [he]
    exact hmasked zs (he' ▸ hz)
  have hq := meaning_unmask hqcanon hx
  have hn := normalized_semantics q xs (by simpa only [hx.1] using hscope)
  have he : (key q qenv).expr = normalized xs.length q := by rw [key_expr,hx.1]
  rw [he] at hq
  have hc := hn.1.mp hq.1
  exact ⟨hc,hn.2 hc ▸ hq.2⟩

theorem memoValid_of_buckets {memo : Memo} (h : BucketsHold KeyMeaning memo.buckets) :
    MemoValid memo := by
  intro e env I hfind hs xs hx
  have hp := bucketsHold_find h
    (fun hab hp => key_beq_sound hab ▸ hp) hfind
  exact hp e env rfl hs xs hx

theorem empty_memo_valid : MemoValid ({} : Memo) := by
  intro e env I h
  simp only [getElem?,Memo.find?,Array.isEmpty_empty,Bool.true_eq_false,
    ↓reduceIte,Option.bind_none,reduceCtorEq] at h

theorem evalWith_sound {c : Ctx} (hc : c.Valid) {memo : Memo} (hm : MemoValid memo)
    {e : Expr} {env : Array Ival} {xs : List ℝ} {I : Ival}
    (hs : e.scoped env.size = true) (hx : EnvMem xs env)
    (h : evalWith c memo e env = some I) : e.Converges xs ∧ e.real xs ∈ I := by
  induction e generalizing I with
  | var i =>
    have hi : i < env.size := by simpa only [NExpr.scoped,decide_eq_true_eq] using hs
    have he : env[i] = I := by simpa only [evalWith,Array.getElem?_eq_getElem hi,
      Option.some.injEq] using h
    exact ⟨trivial,by simpa only [NExpr.real,← he,getElem!_pos env i hi] using hx.2 i hi⟩
  | rat q =>
    have he : Ival.ofRat c.prec q = I := Option.some.inj h
    exact ⟨trivial,he ▸ Ival.mem_ofRat c.prec q⟩
  | pi =>
    have he : c.pi = I := Option.some.inj h
    exact ⟨trivial,he ▸ hc.pi_mem⟩
  | unary op a ih =>
    cases ha : evalWith c memo a env with
    | none => simp [evalWith,ha] at h
    | some A =>
      have he : unaryR c op A = I := by simpa [evalWith,ha] using h
      have hh := ih hs ha
      exact ⟨hh.1,by rw [← he]; exact unaryR_sound hc op hh.2⟩
  | binary op a b iha ihb =>
    have hscope := Bool.and_eq_true_iff.mp hs
    cases ha : evalWith c memo a env with
    | none => simp [evalWith,ha] at h
    | some A =>
      cases hb : evalWith c memo b env with
      | none => simp [evalWith,ha,hb] at h
      | some B =>
        have he : Binary.evalR c op A B = I := by simpa [evalWith,ha,hb] using h
        have hA := iha hscope.1 ha
        have hB := ihb hscope.2 hb
        exact ⟨⟨hA.1,hB.1⟩,by rw [← he]; exact binary_evalR_sound hc op hA.2 hB.2⟩
  | pow a n ih =>
    cases ha : evalWith c memo a env with
    | none => simp [evalWith,ha] at h
    | some A =>
      have he : (if n == 2 then Ival.sq c.prec A else Ival.npow c.prec A n) = I := by
        simpa [evalWith,ha] using h
      have hh := ih hs ha
      refine ⟨hh.1,?_⟩
      rw [← he]
      split
      · rename_i hn
        have hn' : n = 2 := by simpa using hn
        simpa only [NExpr.real,hn'] using Ival.mem_sq (p := c.prec) hh.2
      · exact Ival.mem_npow hh.2 n
  | rpow a q ih =>
    cases ha : evalWith c memo a env with
    | none => simp [evalWith,ha] at h
    | some A =>
      have he : rpowIval c A (Ival.ofRat c.prec q) = I := by simpa [evalWith,ha] using h
      have hh := ih hs ha
      exact ⟨hh.1,by rw [← he]; exact mem_rpowIval hc hh.2 (Ival.mem_ofRat c.prec q)⟩
  | integral k a b f iha ihb ihf =>
    have hfallback : ∀ J, boundR ((NExpr.integral k a b f).size+32) c
        (.integral k a b f) env = some J →
        (NExpr.integral k a b f).Converges xs ∧
          (NExpr.integral k a b f).real xs ∈ J := by
      sorry
    simp only [evalWith] at h
    split at h
    · exact hfallback I h
    · cases hmemo : memo[key (.integral k a b f) env]? with
      | none => exact hfallback I (by simpa [hmemo] using h)
      | some J =>
        have he : J = I := by simpa [hmemo] using h
        subst J
        exact hm (.integral k a b f) env I hmemo hs xs hx

theorem coarsePanel_sound {c : Ctx} (hc : c.Valid) {e : Expr}
    {env : Array Ival} {xs : List ℝ} (hx : EnvMem xs env)
    (hs : e.scoped (env.size+1) = true) {a b : Dy} (hab : a.toReal ≤ b.toReal)
    {I : Ival} (h : coarsePanel c e env a b = some I) :
    IntervalIntegrable (fun x => e.real (xs++[x])) MeasureTheory.volume a.toReal b.toReal ∧
      (∫ x in a.toReal..b.toReal, e.real (xs++[x])) ∈ I := by
  unfold coarsePanel at h
  split at h
  · rename_i heq
    have he : a.toReal = b.toReal := by
      simpa only [Dy.toReal_def] using congrArg (fun q : ℚ => (q:ℝ))
        (show a.toRat = b.toRat by simpa only [dyEq,beq_iff_eq] using heq)
    have hI : Ival.zero = I := by simpa using h
    subst I
    rw [he]
    exact ⟨by simp,by simpa using Ival.mem_zero⟩
  · cases hv : evalWith c {} e (env.push (panelBox a b)) with
    | none => simp [hv] at h
    | some V =>
      have hh : V.isFinite = true ∧
          mulSigned c.prec (Ival.ofRat c.prec (b.toRat-a.toRat)) V = I := by
        simpa [hv] using h
      rw [← hh.2]
      have hpoint : ∀ x ∈ Set.Icc a.toReal b.toReal,
          e.real (xs++[x]) ∈ V := by
        intro x hxI
        have hxbox : x ∈ panelBox a b := by
          exact ⟨fun _ hl => by cases Option.some.inj hl; exact hxI.1,
            fun _ hu => by cases Option.some.inj hu; exact hxI.2⟩
        exact (evalWith_sound hc empty_memo_valid (by simpa using hs)
          (hx.push hxbox) hv).2
      exact integral_mem_product hab (e.measurable_body xs) hh.1
        (by simpa [Dy.toReal_def] using Ival.mem_ofRat c.prec (b.toRat-a.toRat))
        (fun x hxI => hpoint x ⟨hxI.1.le,hxI.2.le⟩)
        ⟨_,hpoint a.toReal ⟨le_rfl,hab⟩⟩
        (fun _ hl _ hv => mem_mulSigned hl hv)

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
  have hwlen : (t.weights c).length = t.roots.length := by
    have hh := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ht).1).2
    simpa only [NodeTable.weights, beq_iff_eq] using hh
  let mid := Ival.ofRat c.prec ((a.toRat+b.toRat)/2)
  let delta := Ival.ofRat c.prec ((b.toRat-a.toRat)/2)
  let evalNode := fun (rw : (Dy × Dy) × Ival) => do
    let X := Ival.add c.prec mid (Ival.mul c.prec delta (rootIval rw.1))
    return mulSigned c.prec rw.2 (← evalWith c memo e (env.push X))
  have heval : ((t.roots.zip (t.weights c)).mapM evalNode).bind
      (fun vals => some (mulSigned c.prec delta (balancedSum c.prec vals))) = some I := h
  cases hv : (t.roots.zip (t.weights c)).mapM evalNode with
  | none => simp [hv] at heval
  | some vals =>
    have hI : mulSigned c.prec delta (balancedSum c.prec vals) = I := by
      simpa only [hv, Option.bind_some, Option.some.injEq] using heval
    subst I
    have hnodes := mapM_some_forall₂ hv
    have hlen : vals.length = t.roots.length := by
      simpa [hwlen] using hnodes.length_eq.symm
    have hmid : (a.toReal+b.toReal)/2 ∈ mid := by
      simpa [mid, Dy.toReal_def] using Ival.mem_ofRat c.prec ((a.toRat+b.toRat)/2)
    have hdelta : (b.toReal-a.toReal)/2 ∈ delta := by
      simpa [delta, Dy.toReal_def] using Ival.mem_ofRat c.prec ((b.toRat-a.toRat)/2)
    let v : Fin t.roots.length → ℝ := fun i => gaussWeight t.roots.length (x i) *
      e.real (xs++[(a.toReal+b.toReal)/2+(b.toReal-a.toReal)/2*x i])
    have hvals : List.Forall₂ (fun (x : ℝ) (I : Ival) => x ∈ I) (List.ofFn v) vals := by
      apply List.forall₂_of_length_eq_of_get
      · simp [hlen]
      · intro i hi hj
        have hir : i < t.roots.length := by simpa using hi
        have hiw : i < (t.weights c).length := by omega
        have hzip : i < (t.roots.zip (t.weights c)).length := by simp [hwlen, hir]
        have hnode := hn ⟨i,hir⟩
        have hweight : gaussWeight t.roots.length (x ⟨i,hir⟩) ∈ (t.weights c)[i] := by
          simpa only [List.getD_eq_getElem _ _ hiw] using hnode.2
        have hpoint := Ival.mem_add (p := c.prec) hmid
          (Ival.mem_mul (p := c.prec) hdelta hnode.1)
        have hget := hnodes.get hzip hj
        simp only [List.get_eq_getElem, List.getElem_zip, evalNode] at hget
        cases hE : evalWith c memo e
            (env.push (Ival.add c.prec mid (Ival.mul c.prec delta (rootIval t.roots[i])))) with
        | none => simp [hE] at hget
        | some E =>
          have hV : mulSigned c.prec (t.weights c)[i] E = vals[i] := by
            simpa [hE] using hget
          have hbound := (evalWith_sound hc hm (by simpa using hs) (hx.push hpoint) hE).2
          have hh := mem_mulSigned (p := c.prec) hweight hbound
          simpa [v,hV] using hh
    have hsum := balancedSum_mem (p := c.prec) hvals
    simpa only [List.sum_ofFn, v, Intgrl.gaussSum] using mem_mulSigned hdelta hsum

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

/-- Whole-line convergence also checks the common endpoint of the two open
half-lines; the endpoint has measure zero but can contain an inner integral. -/
theorem splitEntry_sound {c : Ctx} (hc : c.Valid) {memo : Memo} (hm : MemoValid memo)
    {tables : Array NodeTable} {entry : Entry} {I : Ival}
    (hmethod : entry.method = .split)
    (h : entryEncl c memo tables (tables.map (fun t => t.weights c)) entry = some I) :
    ∀ xs, EnvMem xs entry.env → entry.expr.Converges xs ∧ entry.expr.real xs ∈ I := by
  have hs : entry.expr.scoped entry.env.size = true := by
    by_contra hn
    simp [entryEncl,hn] at h
  cases he : entry.expr <;> try simp [entryEncl,he,hmethod,hs] at h
  case integral kind a b f =>
    have hsc := hs
    simp only [he,NExpr.scoped,Bool.and_eq_true] at hsc
    obtain ⟨⟨hsa,hsb⟩,hsf⟩ := hsc
    cases hA : evalWith c memo a entry.env with
    | none => simp [entryEncl,he,hmethod,hs,hA] at h
    | some A =>
      cases hB : evalWith c memo b entry.env with
      | none => simp [entryEncl,he,hmethod,hs,hA,hB] at h
      | some B =>
        by_cases hk : kind = .whole
        · subst kind
          let anchor := center entry.env.size f
          cases hC : evalWith c memo anchor entry.env with
          | none => simp [entryEncl,he,hmethod,hs,hA,hB,anchor,hC] at h
          | some C =>
            cases hF : evalWith c memo f (entry.env.push C) with
            | none => simp [entryEncl,he,hmethod,hs,hA,hB,anchor,hC,hF] at h
            | some F =>
              cases hR : evalWith c memo (.integral .right anchor (.rat 0) f) entry.env with
              | none => simp [entryEncl,he,hmethod,hs,hA,hB,anchor,hC,hF,hR] at h
              | some R =>
                cases hL : evalWith c memo (.integral .left anchor (.rat 0) f) entry.env with
                | none => simp [entryEncl,he,hmethod,hs,hA,hB,anchor,hC,hF,hR,hL] at h
                | some L =>
                  have hI : Ival.add c.prec R L = I := by
                    simpa [entryEncl,he,hmethod,hs,hA,hB,anchor,hC,hF,hR,hL,
                      NExpr.scoped,hsa,hsb,hsf] using h
                  intro xs hx
                  have ha := evalWith_sound hc hm hsa hx hA
                  have hb := evalWith_sound hc hm hsb hx hB
                  have hanchor := center_properties hsf
                  have hcA := evalWith_sound hc hm hanchor.1 hx hC
                  have hfA := evalWith_sound hc hm (by simpa using hsf) (hx.push hcA.2) hF
                  have hsr : (NExpr.integral .right anchor (.rat 0) f).scoped entry.env.size = true := by
                    simpa only [anchor,NExpr.scoped,hsf,Bool.and_true] using hanchor.1
                  have hsl : (NExpr.integral .left anchor (.rat 0) f).scoped entry.env.size = true := hsr
                  have hr := evalWith_sound hc hm hsr hx hR
                  have hl := evalWith_sound hc hm hsl hx hL
                  have hwhole := whole_split_at hr.1.2.2.1 hl.1.2.2.1
                  refine ⟨⟨ha.1,hb.1,hwhole.1,?_⟩,?_⟩
                  · intro x _
                    rcases lt_trichotomy x (anchor.real xs) with hxlt | hxeq | hxgt
                    · exact hl.1.2.2.2 x hxlt
                    · simpa only [hxeq] using hfA.1
                    · exact hr.1.2.2.2 x hxgt
                  · change (∫ x, f.real (xs++[x])) ∈ I
                    rw [hwhole.2,← hI]
                    exact Ival.mem_add hr.2 hl.2
        · simp [entryEncl,he,hmethod,hs,hA,hB,hk] at h

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
  cases hmethod : entry.method with
  | split => exact splitEntry_sound hc hm hmethod h
  | panels p => sorry

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
  have htransport : ∀ (e : Expr) (env : Array Ival) (I : Ival),
      envCheck env = true → e.scoped env.size = true →
      (∀ xs, EnvMem xs env → e.Converges xs ∧ e.real xs ∈ I) →
      KeyMeaning (key e env) I :=
    fun _ _ _ hen hs he => keyMeaning_of_source hen hs he
  unfold replay at h
  split at h
  · simp at h
  · rename_i ht
    have ht' : cert.tables.all (fun t => t.check c) = true := by simpa using ht
    let step : Entry → (Option Memo × Memo) → Option (ForInStep (Option Memo × Memo)) :=
      fun entry s => if !envCheck entry.env then none else do
        let I ← entryEncl c s.2 cert.tables (cert.tables.map (fun t => t.weights c)) entry
        if !I.isFinite then none else
          some (.yield (none,s.2.insert (key entry.expr entry.env) I))
    let P : (Option Memo × Memo) → Prop := fun s =>
      s.1 = none ∧ BucketsHold KeyMeaning s.2.buckets
    have hinit : P (none,({} : Memo)) := ⟨rfl,by intro bucket hb; simp at hb⟩
    have hstep : ∀ entry ∈ cert.entries.toList, ∀ s out, P s →
        step entry s = some out → P out.value := by
      intro entry _ s out hs hstep
      by_cases hen : envCheck entry.env = true
      · cases he : entryEncl c s.2 cert.tables (cert.tables.map (fun t => t.weights c)) entry with
        | none => simp [step,hen,he] at hstep
        | some I =>
          by_cases hfinite : I.isFinite = true
          · have hout : ForInStep.yield (none,s.2.insert (key entry.expr entry.env) I) = out := by
              simpa [step,hen,he,hfinite] using hstep
            subst out
            have hscope : entry.expr.scoped entry.env.size = true := by
              by_contra hn
              simp [entryEncl,hn] at he
            have hsource := hentries s.2 cert.tables (memoValid_of_buckets hs.2) ht' entry I he
            exact ⟨rfl,bucketsHold_insert hs.2 (htransport entry.expr entry.env I hen hscope hsource)⟩
          · simp [step,hen,he,hfinite] at hstep
      · simp [step,hen] at hstep
    simp only [bind,pure,Option.bind_none] at h
    change ((forIn cert.entries (none,({} : Memo)) step).bind _) = some memo at h
    cases hloop : forIn cert.entries (none,({} : Memo)) step with
    | none => simp only [hloop,Option.bind_none,reduceCtorEq] at h
    | some s =>
      have hloop' : forIn cert.entries.toList (none,({} : Memo)) step = some s := by
        simpa only [Array.forIn_toList] using hloop
      have hs := list_forIn_preserves P step cert.entries.toList hstep hinit hloop'
      have hmemo : s.2 = memo := by
        simpa only [hloop,Option.bind_some,hs.1,Option.some.injEq] using h
      rw [← hmemo]
      exact memoValid_of_buckets hs.2

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
