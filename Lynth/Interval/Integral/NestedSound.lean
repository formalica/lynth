import Lynth.Interval.Integral.NestedCert
import Lynth.Interval.Integral.NestedBoundCSound
import Lynth.Interval.Integral.NestedAnalyticBoundC
import Lynth.Interval.Integral.NestedRealBoundsProof
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

private theorem finite_result_eq {J I : Ival}
    (h : (if J.isFinite then some J else none) = some I) : J = I := by
  split at h
  · exact Option.some.inj h
  · contradiction

set_option maxHeartbeats 800000 in
-- Fuel induction visits the numerical fallback branches as well as the syntax.
theorem boundR_sound_of_complex {c : Ctx} (hc : c.Valid)
    (hcomplex : ∀ fuel (e : Expr) (env : Array CBox) (xs : List ℝ) Z,
      e.scoped env.size = true → xs.length = env.size →
      (∀ i, i < env.size → (xs[i]?.getD 0 : ℂ) ∈ env[i]!) →
      boundC fuel c e env = some Z → e.Converges xs ∧ (e.real xs : ℂ) ∈ Z)
    {fuel : Nat} {e : Expr} {env : Array Ival} {xs : List ℝ} {I : Ival}
    (hs : e.scoped env.size = true) (hx : EnvMem xs env)
    (h : boundR fuel c e env = some I) : e.Converges xs ∧ e.real xs ∈ I := by
  induction fuel generalizing e env xs I with
  | zero => simp [boundR] at h
  | succ fuel ih =>
    cases e with
    | var i =>
      have hi : i < env.size := by simpa [NExpr.scoped] using hs
      have he : env[i] = I := finite_result_eq (by
        simpa only [boundR, Array.getElem?_eq_getElem hi, bind, Option.bind_some] using h)
      exact ⟨trivial, he ▸ (by simpa [NExpr.real, getElem!_pos env i hi] using hx.2 i hi)⟩
    | rat q =>
      have he : Ival.ofRat c.prec q = I := finite_result_eq (by
        simpa only [boundR, bind, Option.bind_some] using h)
      exact ⟨trivial, he ▸ Ival.mem_ofRat c.prec q⟩
    | pi =>
      have he : c.pi = I := finite_result_eq (by
        simpa only [boundR, bind, Option.bind_some] using h)
      exact ⟨trivial, he ▸ hc.pi_mem⟩
    | unary op a =>
      simp only [boundR, bind, Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨A, hA, h⟩ := h
      have he := finite_result_eq h
      have ha := ih (e := a) hs hx hA
      exact ⟨ha.1, he ▸ unaryR_sound hc op ha.2⟩
    | binary op a b =>
      simp only [NExpr.scoped, Bool.and_eq_true] at hs
      simp only [boundR, bind, Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨A, hA, B, hB, h⟩ := h
      have he := finite_result_eq h
      have ha := ih hs.1 hx hA
      have hb := ih hs.2 hx hB
      exact ⟨⟨ha.1, hb.1⟩, he ▸ binary_evalR_sound hc op ha.2 hb.2⟩
    | pow a n =>
      simp only [boundR, bind, Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨A, hA, h⟩ := h
      have he := finite_result_eq h
      have ha := ih (e := a) hs hx hA
      refine ⟨ha.1, he ▸ ?_⟩
      split
      · rename_i hn
        have hn : n = 2 := by simpa using hn
        simpa only [NExpr.real, hn] using Ival.mem_sq (p := c.prec) ha.2
      · exact Ival.mem_npow ha.2 n
    | rpow a q =>
      simp only [boundR, bind, Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨A, hA, h⟩ := h
      have he := finite_result_eq h
      have ha := ih (e := a) hs hx hA
      exact ⟨ha.1, he ▸ mem_rpowIval hc ha.2 (Ival.mem_ofRat c.prec q)⟩
    | integral k a b f =>
      have hscope := hs
      simp only [NExpr.scoped, Bool.and_eq_true] at hs
      obtain ⟨⟨hsa, hsb⟩, hsf⟩ := hs
      simp only [boundR, bind, Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨A, hA, B, hB, h⟩ := h
      have ha := ih hsa hx hA
      have hb := ih hsb hx hB
      let Y : Ival := ⟨A.lo.bind (fun u => B.lo.map (Dy.min u)),
        A.hi.bind (fun u => B.hi.map (Dy.max u))⟩
      let fallback : Option Ival := do
        let Z ← boundC fuel c (.integral k a b f) (env.map CBox.ofReal)
        if Z.re.isFinite then some Z.re else none
      have hfall : ∀ J, fallback = some J →
          (NExpr.integral k a b f).Converges xs ∧ (NExpr.integral k a b f).real xs ∈ J := by
        intro J hj
        simp only [fallback, bind, Option.bind_eq_some_iff] at hj
        obtain ⟨Z, hZ, hj⟩ := hj
        have he := finite_result_eq hj
        have hmem : ∀ i, i < (env.map CBox.ofReal).size →
            (xs[i]?.getD 0 : ℂ) ∈ (env.map CBox.ofReal)[i]! := by
          intro i hi
          have hib : i < env.size := by simpa using hi
          simpa [getElem!_pos (env.map CBox.ofReal) i hi, getElem!_pos env i hib] using CBox.mem_ofReal (hx.2 i hib)
        have hz := hcomplex fuel (.integral k a b f) (env.map CBox.ofReal) xs Z
          (by simpa using hscope) (by simpa using hx.1) hmem hZ
        exact ⟨hz.1, he ▸ hz.2.1⟩
      let tail : Option Ival :=
        if k.finite then
          match boundR fuel c f (env.push Y) with
          | some V =>
            let out := mulSigned c.prec (Ival.sub c.prec B A) V
            if out.isFinite then
              if k == .interval || Ival.leB A B then some out
              else some ⟨out.lo.map (Dy.min Dy.zero), out.hi.map (Dy.max Dy.zero)⟩
            else fallback
          | _ => fallback
        else fallback
      have htail : ∀ J, tail = some J →
          (NExpr.integral k a b f).Converges xs ∧ (NExpr.integral k a b f).real xs ∈ J := by
        intro J hj
        dsimp only [tail] at hj
        split at hj
        · rename_i hk
          cases hv : boundR fuel c f (env.push Y) with
          | none => exact hfall J (by simpa only [hv] using hj)
          | some V =>
            simp only [hv] at hj
            split at hj
            · have hpoint : ∀ x ∈ Set.uIcc (a.real xs) (b.real xs),
                  f.Converges (xs ++ [x]) ∧ f.real (xs ++ [x]) ∈ V := by
                intro x hxI
                exact ih (by simpa using hsf) (hx.push (endpointHull_mem ha.2 hb.2 hxI)) hv
              have hVne : ∃ v : ℝ, v ∈ V := ⟨_, (hpoint (a.real xs) Set.left_mem_uIcc).2⟩
              have hwidth := Ival.mem_sub (p := c.prec) hb.2 ha.2
              have hrange (horder : k ≠ .interval → a.real xs ≤ b.real xs) :=
                finite_integral_range hk ha.1 hb.1 horder (boundR_isFinite hv) hwidth
                  (fun x hxI => hpoint x ⟨hxI.1.le, hxI.2.le⟩) hVne
                  (fun _ hl _ hv => mem_mulSigned (p := c.prec) hl hv)
              split at hj
              · rename_i hor
                have he := Option.some.inj hj
                rw [← he]
                apply hrange
                intro hki
                have ho : Ival.leB A B = true := by simpa [hki] using hor
                exact Ival.le_of_leB ha.2 hb.2 ho
              · rename_i hor
                have hki : k ≠ .interval := by intro he; simp [he] at hor
                have he := Option.some.inj hj
                rw [← he]
                rcases le_total (a.real xs) (b.real xs) with hab | hba
                · have hh := hrange (fun _ => hab)
                  exact ⟨hh.1, hullZero_mem (Or.inr hh.2)⟩
                · have hh := finite_integral_empty (f := f) hk hki ha.1 hb.1 hba
                  exact ⟨hh.1, hullZero_mem (Or.inl hh.2)⟩
            · exact hfall J hj
        · exact hfall J hj
      have hcore : (if k.finite && a == b then some Ival.zero else
        if k.finite && k != .interval && Ival.leB B A then some Ival.zero else
        match formula env.size k a b f with
        | some form => do
          let mut good := true
          for guard in form.nonnegative.toList do
            let G ← boundR fuel c guard env
            good := good && G.nonneg
          if good then boundR fuel c form.value env else tail
        | _ => tail) = some I := by
        convert h using 1
      clear h
      have h := hcore
      split at h
      · rename_i hz
        obtain ⟨hk, hab⟩ : k.finite = true ∧ a = b := by simpa using hz
        have he := Option.some.inj h
        rw [← he]
        have hh := finite_integral_zero_width (f := f) hk ha.1 hb.1 (by rw [hab])
        exact ⟨hh.1, hh.2 ▸ Ival.mem_zero⟩
      · split at h
        · rename_i hz
          obtain ⟨⟨hk, hki⟩, hba⟩ : (k.finite = true ∧ k ≠ .interval) ∧ Ival.leB B A = true := by
            simpa using hz
          have he := Option.some.inj h
          rw [← he]
          have hh := finite_integral_empty (f := f) hk hki ha.1 hb.1 (Ival.le_of_leB hb.2 ha.2 hba)
          exact ⟨hh.1, hh.2 ▸ Ival.mem_zero⟩
        · cases hf : formula env.size k a b f with
          | none => exact htail I (by simpa only [hf] using h)
          | some form =>
            simp only [hf] at h
            have hformscope := formula_scoped hsa hsb hsf hf
            cases hg : form.nonnegative with
            | none =>
              have hv : boundR fuel c form.value env = some I := by simpa [hg] using h
              have hh := ih hformscope.1 hx hv
              have hsem := formula_sound (hx.1 ▸ hsa) (hx.1 ▸ hsb) ha.1 hb.1
                (by simpa [hx.1] using hf) (by simp [hg])
              exact ⟨hsem.1, hsem.2 ▸ hh.2⟩
            | some guard =>
              cases hG : boundR fuel c guard env with
              | none => simp [hg, hG] at h
              | some G =>
                by_cases hnon : G.nonneg = true
                · have hv : boundR fuel c form.value env = some I := by simpa [hg, hG, hnon] using h
                  have hh := ih hformscope.1 hx hv
                  have hgs : guard.scoped env.size = true := hformscope.2 guard (by simp [hg])
                  have hguard := ih hgs hx hG
                  have hsem := formula_sound (hx.1 ▸ hsa) (hx.1 ▸ hsb) ha.1 hb.1
                    (by simpa [hx.1] using hf) (by
                      intro g hgmem
                      have he : g = guard := by simpa [hg] using hgmem.symm
                      subst g
                      exact Ival.nonneg_of hnon hguard.2)
                  exact ⟨hsem.1, hsem.2 ▸ hh.2⟩
                · exact htail I (by simpa [hg, hG, hnon] using h)

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
      intro J hJ
      refine boundR_sound_of_complex hc ?_ hs hx hJ
      intro fuel e boxes ys Z hscope hlength hmem hZ
      exact boundC_real_sound hc hscope hlength hmem hZ
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
  unfold analytic at h
  split at h
  · simp at h
  · rename_i hrho
    have hρ : 1 < ρ.toReal := by
      have ht : Dy.ltB Dy.one ρ = true := by simpa using hrho
      simpa [Dy.toReal_def] using Dy.toReal_lt_of_ltB ht
    cases hZ : boundC (e.size+32) c e
        ((env.map CBox.ofReal).push (ellipseBox c a b ρ)) with
    | none => simp [hZ] at h
    | some Z =>
      have hM : (CBox.norm c.prec Z).hi = some M := by simpa [hZ] using h
      have hext : ∃ F : ℂ → ℂ,
          AnalyticOnNhd ℂ F ((affine a.toReal b.toReal) '' ellipse ρ.toReal) ∧
          (∀ z ∈ ellipse ρ.toReal, F (affine a.toReal b.toReal z) ∈ Z) ∧
          (∀ x ∈ Set.Ioo a.toReal b.toReal, F x = (e.real (xs++[x]) : ℂ)) := by
        exact AnalyticWork.ellipse_extension hc hx.1 hx.2 hs hab hρ hZ
      obtain ⟨F, hF, hbox, hagree⟩ := hext
      have hbound : ∀ z ∈ ellipse ρ.toReal,
          ‖F (affine a.toReal b.toReal z)‖ ≤ M.toReal := by
        intro z hz
        exact (CBox.mem_norm (p := c.prec) (hbox z hz)).2 M hM
      exact ⟨hρ, (norm_nonneg _).trans
        (hbound 0 (real_mem_ellipse hρ (by norm_num))), F, hF, hbound, hagree⟩

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

namespace AssemblyProof
open MeasureTheory Set

lemma boundC_push_sound {c : Ctx} (hc : c.Valid) {e : Expr} {env : Array Ival}
    {xs : List ℝ} (hx : EnvMem xs env) (hs : e.scoped (env.size+1) = true)
    {x : ℝ} {B Z : CBox} {fuel : Nat} (hxB : (x:ℂ) ∈ B)
    (hZ : boundC fuel c e ((env.map CBox.ofReal).push B) = some Z) :
    e.Converges (xs++[x]) ∧ (e.real (xs++[x]):ℂ) ∈ Z := by
  let boxes := (env.map CBox.ofReal).push B
  have hmem : ∀ i < boxes.size, (((xs++[x])[i]?.getD 0:ℝ):ℂ) ∈ boxes[i]! := by
    intro i hi
    by_cases hin : i < env.size
    · have him : i < (env.map CBox.ofReal).size := by simpa using hin
      have hget : boxes[i]! = CBox.ofReal env[i]! := by
        rw [getElem!_pos boxes i hi]
        dsimp only [boxes]
        rw [Array.getElem_push_lt him,Array.getElem_map,getElem!_pos env i hin]
      rw [hget]
      have hi' : i < xs.length := hx.1 ▸ hin
      simpa only [List.getElem?_append,if_pos hi'] using CBox.mem_ofReal (hx.2 i hin)
    · have he : i = env.size := by simp only [boxes,Array.size_push,Array.size_map] at hi; omega
      subst i
      have hget : boxes[env.size]! = B := by
        rw [getElem!_pos boxes env.size hi]
        dsimp only [boxes]
        simpa only [Array.size_map] using (Array.getElem_push_eq (xs := env.map CBox.ofReal) (x := B))
      rw [hget]
      simpa only [List.getElem?_append,hx.1,lt_self_iff_false,↓reduceIte,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some] using hxB
  exact boundC_real_sound hc (by simpa only [boxes,Array.size_push,Array.size_map] using hs)
    (by simp only [List.length_append,List.length_singleton,boxes,Array.size_push,Array.size_map,hx.1]) hmem hZ

lemma piece_converges {c : Ctx} (hc : c.Valid) {memo : Memo} {tables : Array NodeTable}
    {e : Expr} {env : Array Ival} {xs : List ℝ} (hx : EnvMem xs env)
    (hs : e.scoped (env.size+1) = true) {p : Piece} {I : Ival}
    (hab : p.a.toReal < p.b.toReal)
    (h : piece c memo e env tables (tables.map (fun t => t.weights c)) p = some I) :
    ∀ x ∈ Icc p.a.toReal p.b.toReal, e.Converges (xs++[x]) := by
  cases hmethod : p.method with
  | direct =>
    have hh : coarsePanel c e env p.a p.b = some I := by simpa only [piece,hmethod] using h
    unfold coarsePanel at hh
    split at hh
    · rename_i he
      have he' : p.a.toRat = p.b.toRat := by simpa only [dyEq,beq_iff_eq] using he
      have he'' := congrArg (fun q : ℚ => (q:ℝ)) he'
      exact (hab.ne he'').elim
    · cases hv : evalWith c {} e (env.push (panelBox p.a p.b)) with
      | none => simp [hv] at hh
      | some V =>
        intro x hxi
        have hxbox : x ∈ panelBox p.a p.b :=
          ⟨fun _ hl => by cases Option.some.inj hl; exact hxi.1,
            fun _ hu => by cases Option.some.inj hu; exact hxi.2⟩
        exact (evalWith_sound hc empty_memo_valid (by simpa using hs) (hx.push hxbox) hv).1
  | gauss i ρ =>
    simp only [piece,hmethod] at h
    split at h
    · simp at h
    · cases hti : tables[i]? with
      | none => simp [hti] at h
      | some table =>
        cases hM : analytic c e env p.a p.b ρ with
        | none => simp [hti,hM] at h
        | some M =>
          unfold analytic at hM
          split at hM
          · simp at hM
          · rename_i hguard
            have hρ : 1 < ρ.toReal := by
              have hlt : Dy.ltB Dy.one ρ = true := by simpa using hguard
              simpa [Dy.toReal_def] using Dy.toReal_lt_of_ltB hlt
            cases hZ : boundC (e.size+32) c e
                ((env.map CBox.ofReal).push (ellipseBox c p.a p.b ρ)) with
            | none => simp [hZ] at hM
            | some Z =>
              intro x hxi
              obtain ⟨z,hz,he⟩ := real_mem_affine_ellipse hab hρ hxi
              have hxbox : (x:ℂ) ∈ ellipseBox c p.a p.b ρ := he ▸ ellipseBox_mem hρ hz
              exact (boundC_push_sound hc hx hs hxbox hZ).1

lemma panel_convergence {c : Ctx} (hc : c.Valid) {memo : Memo} {tables : Array NodeTable}
    {e : Expr} {env : Array Ival} {xs : List ℝ} (hx : EnvMem xs env)
    (hs : e.scoped (env.size+1) = true) {p : Plan} {vals : List Ival}
    (hp : partitionCheck ⟨p.a,p.b,p.reverse,#[],p.pieces⟩ = true)
    (hvals : p.pieces.mapM (piece c memo e env tables (tables.map (fun t => t.weights c))) = some vals) :
    p.a.toReal ≤ p.b.toReal ∧
      (p.a.toReal < p.b.toReal → ∀ x ∈ Icc p.a.toReal p.b.toReal, e.Converges (xs++[x])) := by
  apply partition_predicate hp
  intro q hq hlt x hxi
  have hh := mapM_some_forall₂ hvals
  obtain ⟨i,hi,hqi⟩ := List.mem_iff_getElem.mp hq
  have hi' : i < p.pieces.length := hi
  have hj : i < vals.length := by have hlen : p.pieces.length = vals.length := hh.length_eq; omega
  have hv := hh.get hi' hj
  simp only [List.get_eq_getElem,hqi] at hv
  exact piece_converges (memo := memo) (tables := tables) hc hx hs hlt hv x hxi

lemma boundR_sound {c : Ctx} (hc : c.Valid) {e : Expr} {env : Array Ival}
    {xs : List ℝ} {fuel : Nat} {V : Ival} (hs : e.scoped env.size = true)
    (hx : EnvMem xs env) (h : boundR fuel c e env = some V) :
    e.Converges xs ∧ e.real xs ∈ V := by
  apply boundR_sound_of_complex hc ?_ hs hx h
  intro fuel e boxes ys Z hscope hlength hmem hZ
  exact boundC_real_sound hc hscope hlength hmem hZ

lemma uncertain_closed {c : Ctx} (hc : c.Valid) {e : Expr} {env : Array Ival}
    {xs : List ℝ} (hx : EnvMem xs env) (hs : e.scoped (env.size+1) = true)
    {J : Ival} {a err : Dy} {x : ℝ} (hxJ : x ∈ J)
    (h : uncertainEndpoint c e env J a = some err) :
    IntervalIntegrable (fun t => e.real (xs++[t])) volume x a.toReal ∧
      |∫ t in x..a.toReal, e.real (xs++[t])| ≤ err.toReal ∧
      (x ≠ a.toReal → ∀ t ∈ uIcc x a.toReal, e.Converges (xs++[t])) := by
  have hb : ∀ V, boundR (e.size+32) c e (env.push (hullPoint J a)) = some V →
      ∀ t ∈ hullPoint J a, e.Converges (xs++[t]) ∧ e.real (xs++[t]) ∈ V := by
    intro V hV t ht
    exact boundR_sound hc (by simpa using hs) (hx.push ht) hV
  have hh := uncertainEndpoint_sound_of_bound hxJ hb h
  refine ⟨hh.1,hh.2.1,?_⟩
  intro hne t ht
  cases hlo : J.lo with
  | none => simp [uncertainEndpoint,hlo] at h
  | some lo =>
    cases hhi : J.hi with
    | none => simp [uncertainEndpoint,hlo,hhi] at h
    | some hi =>
      simp only [uncertainEndpoint,hlo,hhi,Bind.bind,Option.bind_some] at h
      split at h
      · rename_i he
        have he' : lo.toRat = a.toRat ∧ hi.toRat = a.toRat := by
          simpa only [Bool.and_eq_true,dyEq,beq_iff_eq] using he
        have heq : x = a.toReal := le_antisymm
          (by simpa only [Dy.toReal_def,he'.2] using hxJ.2 hi hhi)
          (by simpa only [Dy.toReal_def,he'.1] using hxJ.1 lo hlo)
        exact (hne heq).elim
      · cases hV : boundR (e.size+32) c e (env.push (hullPoint J a)) with
        | none => simp [hV] at h
        | some V => exact (hb V hV t (hullPoint_mem hxJ ht)).1

end AssemblyProof

open MeasureTheory Set in
set_option maxHeartbeats 1600000 in
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
  | panels p =>
    have hs : entry.expr.scoped entry.env.size = true := by
      by_contra hn
      simp [entryEncl,hn] at h
    cases he : entry.expr <;> try simp [entryEncl,he,hmethod,hs] at h
    case integral kind a b f =>
      have hsc : (a.scoped entry.env.size = true ∧ b.scoped entry.env.size = true) ∧
          f.scoped (entry.env.size+1) = true := by
        simpa only [he,NExpr.scoped,Bool.and_eq_true] using hs
      obtain ⟨⟨hsa,hsb⟩,hsf⟩ := hsc
      cases hA : evalWith c memo a entry.env with
      | none => simp [entryEncl,he,hmethod,hs,hA] at h
      | some A =>
        cases hB : evalWith c memo b entry.env with
        | none => simp [entryEncl,he,hmethod,hs,hA,hB] at h
        | some B =>
          have hp : partitionCheck ⟨p.a,p.b,p.reverse,#[],p.pieces⟩ = true := by
            by_contra hn
            simp [entryEncl,he,hmethod,hs,hA,hB,hn] at h
          have hrun := h.2
          simp only [hA,hB,Bind.bind,Option.bind_some,hp,Bool.true_eq_false,↓reduceIte] at hrun
          intro xs hx
          have ha := evalWith_sound hc hm hsa hx hA
          have hb := evalWith_sound hc hm hsb hx hB
          by_cases hident : (p.change == .identity) = true
          · rw [ite_eq_left hident] at hrun
            by_cases hfin : kind.finite = true
            · simp only [hfin,Bool.true_eq_false,↓reduceIte] at hrun
              by_cases hbad : (kind != .interval && (!Ival.leB A B || p.reverse)) = true
              · rw [ite_eq_left hbad] at hrun
                contradiction
              · rw [ite_eq_right hbad] at hrun
                have horder : kind ≠ .interval → Ival.leB A B = true := by
                  intro hki
                  by_contra hn
                  have hkbi : (kind != .interval) = true := by simpa using hki
                  have hnot : (!Ival.leB A B) = true := by simpa using hn
                  exact hbad (by rw [hkbi,hnot]; rfl)
                simp only [Bind.bind,Option.bind_eq_some_iff] at hrun
                obtain ⟨ea,hea,eb,heb,vals,hvals,hout⟩ := hrun
                have hI : Ival.widen c.prec
                    (if p.reverse then Ival.neg (balancedSum c.prec vals) else balancedSum c.prec vals)
                    (Dy.addU c.prec ea eb) = I := Option.some.inj hout
                let a₀ := if p.reverse then p.b else p.a
                let b₀ := if p.reverse then p.a else p.b
                have hcore : IntervalIntegrable (fun x => f.real (xs++[x])) volume p.a.toReal p.b.toReal ∧
                    (∫ x in p.a.toReal..p.b.toReal, f.real (xs++[x])) ∈ balancedSum c.prec vals :=
                  panel_chain_sound (cert := ⟨p.a,p.b,p.reverse,#[],p.pieces⟩) hp
                    (fun q _ hq V hV => hpanels f entry.env xs hx hsf q V hq hV) hvals
                have hconv := AssemblyProof.panel_convergence hc hx hsf hp hvals
                have hleft := AssemblyProof.uncertain_closed hc hx hsf ha.2 hea
                have hright := AssemblyProof.uncertain_closed hc hx hsf hb.2 heb
                have horiented : IntervalIntegrable (fun x => f.real (xs++[x])) volume a₀.toReal b₀.toReal ∧
                    (∫ x in a₀.toReal..b₀.toReal, f.real (xs++[x])) ∈
                      (if p.reverse then Ival.neg (balancedSum c.prec vals) else balancedSum c.prec vals) := by
                  cases hr : p.reverse with
                  | false => simpa only [a₀,b₀,hr,Bool.false_eq_true,↓reduceIte] using hcore
                  | true =>
                    refine ⟨by simpa only [a₀,b₀,hr,↓reduceIte] using hcore.1.symm,?_⟩
                    simp only [a₀,b₀,hr,↓reduceIte]
                    rw [intervalIntegral.integral_symm]
                    exact Ival.mem_neg hcore.2
                have hi := hleft.1.trans (horiented.1.trans hright.1.symm)
                have hdiff : (∫ x in a.real xs..b.real xs, f.real (xs++[x])) -
                    (∫ x in a₀.toReal..b₀.toReal, f.real (xs++[x])) =
                    (∫ x in a.real xs..a₀.toReal, f.real (xs++[x])) -
                      (∫ x in b.real xs..b₀.toReal, f.real (xs++[x])) := by
                  rw [← intervalIntegral.integral_add_adjacent_intervals hleft.1 (horiented.1.trans hright.1.symm),
                    ← intervalIntegral.integral_add_adjacent_intervals horiented.1 hright.1.symm,
                    intervalIntegral.integral_symm b₀.toReal (b.real xs)]
                  ring
                have hbound : |(∫ x in a.real xs..b.real xs, f.real (xs++[x])) -
                    (∫ x in a₀.toReal..b₀.toReal, f.real (xs++[x]))| ≤ (Dy.addU c.prec ea eb).toReal := by
                  rw [hdiff]
                  apply ((abs_sub _ _).trans (add_le_add hleft.2.1 hright.2.1)).trans
                  simpa only [Dy.toReal_def,Rat.cast_add] using (Rat.cast_mono (K := ℝ) (Dy.le_addU c.prec ea eb))
                have hnum : (∫ x in a.real xs..b.real xs, f.real (xs++[x])) ∈ I := by
                  rw [← hI]
                  exact Ival.mem_widen horiented.2 hbound
                have hPcore : a₀.toReal ≠ b₀.toReal → ∀ x ∈ uIcc a₀.toReal b₀.toReal,
                    f.Converges (xs++[x]) := by
                  intro hne x hxi
                  have hne' : p.a.toReal ≠ p.b.toReal := by
                    intro heq
                    apply hne
                    cases hr : p.reverse <;> simp only [a₀,b₀,hr,Bool.false_eq_true,↓reduceIte,heq]
                  apply hconv.2 (lt_of_le_of_ne hconv.1 hne') x
                  cases hr : p.reverse <;>
                    simpa only [a₀,b₀,hr,Bool.false_eq_true,↓reduceIte,uIcc_of_le hconv.1,uIcc_of_ge hconv.1] using hxi
                have hPright : b₀.toReal ≠ b.real xs → ∀ x ∈ uIcc b₀.toReal (b.real xs),
                    f.Converges (xs++[x]) := by
                  intro hne x hxi
                  exact hright.2.2 (Ne.symm hne) x (by rwa [uIcc_comm] at hxi)
                have hP : ∀ x ∈ uIoo (a.real xs) (b.real xs), f.Converges (xs++[x]) := by
                  have hh := nondegenerate_predicate_trans
                    (nondegenerate_predicate_trans hleft.2.2 hPcore) hPright
                  intro x hxi
                  have hne : a.real xs ≠ b.real xs := by intro heq; simp [heq] at hxi
                  exact hh hne x ⟨hxi.1.le,hxi.2.le⟩
                have hsem : (NExpr.integral kind a b f).Converges xs ∧
                    (NExpr.integral kind a b f).real xs = ∫ x in a.real xs..b.real xs, f.real (xs++[x]) := by
                  by_cases hki : kind = .interval
                  · subst kind
                    exact ⟨⟨ha.1,hb.1,hi,hP⟩,rfl⟩
                  · have hab := Ival.le_of_leB ha.2 hb.2 (horder hki)
                    have hd := finite_domain_of_interval hfin hab hi
                    refine ⟨⟨ha.1,hb.1,hd.1,?_⟩,hd.2⟩
                    cases kind <;> simp only [NDomain.finite,Bool.false_eq_true] at hfin
                    all_goals simpa only [uIoo_of_le hab] using hP
                exact ⟨hsem.1,hsem.2.symm ▸ hnum⟩
            · simp [hfin] at hrun
          · rw [ite_eq_right hident] at hrun
            let allowed : Bool := match p.change with
              | .power m _ => kind.finite && 1 ≤ m && m ≤ 16
              | _ => p.change == (if kind.finite then Change.affine else
                  if kind == .right then Change.right else Change.left)
            let finish : Option Ival :=
              if (kind.finite && kind != .interval && !Ival.leB A B) = true then none else
                if dyEq p.a p.left = false ∨ dyEq p.b (Dy.one.sub p.right) = false then none else
                  if Dy.leB Dy.zero p.left = false ∨ Dy.leB Dy.zero p.right = false then none else do
                    let E := transformed entry.env.size p.change a b f
                    let l ← (if dyEq p.left Dy.zero then some Dy.zero else
                      endpointBound c E (entry.env.map CBox.ofReal) p.left false p.decay)
                    let r ← (if dyEq p.right Dy.zero then some Dy.zero else
                      endpointBound c E (entry.env.map CBox.ofReal) p.right true p.decay)
                    let vals ← p.pieces.mapM (piece c memo E entry.env tables (tables.map (fun t => t.weights c)))
                    return Ival.widen c.prec (balancedSum c.prec vals) (Dy.addU c.prec l r)
            have hrun' : (if (kind == .whole || !allowed || p.reverse) = true then none else finish) = some I := by
              dsimp only [allowed,finish,Bind.bind]
              convert hrun using 1 <;> congr!
            clear hrun
            have hrun := hrun'
            by_cases hguard : (kind == .whole || !allowed || p.reverse) = true
            · rw [ite_eq_left hguard] at hrun
              contradiction
            · rw [ite_eq_right hguard] at hrun
              dsimp only [finish] at hrun
              have hg : (kind == .whole) = false ∧ allowed = true ∧ p.reverse = false := by
                have hh := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hguard)
                have hh' := Bool.or_eq_false_iff.mp hh.1
                exact ⟨hh'.1,by simpa using hh'.2,hh.2⟩
              have hnotwhole : kind ≠ .whole := by simpa using hg.1
              have hhow : p.change.Admissible kind := by
                cases hch : p.change with
                | identity => exact (hident (by rw [hch]; rfl)).elim
                | power m r =>
                  have hh : kind.finite = true ∧ 1 ≤ m ∧ m ≤ 16 := by
                    simpa only [allowed,hch,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hg.2.1
                  exact ⟨hh.1,by omega⟩
                | affine | right | left =>
                  all_goals
                    cases hk : kind <;> try rfl
                    all_goals
                      first
                      | exact (hnotwhole hk).elim
                      | have hh := hg.2.1
                        simp only [allowed,hch,hk,NDomain.finite,↓reduceIte] at hh
                        change false = true at hh
                        cases hh
              by_cases horderGuard : (kind.finite && kind != .interval && !Ival.leB A B) = true
              · rw [ite_eq_left horderGuard] at hrun
                contradiction
              · rw [ite_eq_right horderGuard] at hrun
                have horder : kind.finite = true → kind ≠ .interval → Ival.leB A B = true := by
                  intro hfin hki
                  by_contra hn
                  have hkbi : (kind != .interval) = true := by simpa using hki
                  have hnot : (!Ival.leB A B) = true := by simpa using hn
                  exact horderGuard (by rw [hfin,hkbi,hnot]; rfl)
                by_cases hanchors : dyEq p.a p.left = false ∨ dyEq p.b (Dy.one.sub p.right) = false
                · rw [ite_eq_left hanchors] at hrun
                  contradiction
                · rw [ite_eq_right hanchors] at hrun
                  have hanchors' : dyEq p.a p.left = true ∧ dyEq p.b (Dy.one.sub p.right) = true := by
                    exact ⟨Bool.eq_true_of_not_eq_false (fun h => hanchors (Or.inl h)),
                      Bool.eq_true_of_not_eq_false (fun h => hanchors (Or.inr h))⟩
                  have hpa : p.a.toReal = p.left.toReal := by
                    have hh : p.a.toRat = p.left.toRat := by simpa only [dyEq,beq_iff_eq] using hanchors'.1
                    exact congrArg (fun q : ℚ => (q:ℝ)) hh
                  have hpb : p.b.toReal = 1-p.right.toReal := by
                    have hh : p.b.toRat = (Dy.one.sub p.right).toRat := by simpa only [dyEq,beq_iff_eq] using hanchors'.2
                    have hh' := congrArg (fun q : ℚ => (q:ℝ)) hh
                    simpa [Dy.toReal_def,Vendor.Dyadic.sub,sub_eq_add_neg] using hh'
                  by_cases hpositive : Dy.leB Dy.zero p.left = false ∨ Dy.leB Dy.zero p.right = false
                  · rw [ite_eq_left hpositive] at hrun
                    contradiction
                  · rw [ite_eq_right hpositive] at hrun
                    have hpos : Dy.leB Dy.zero p.left = true ∧ Dy.leB Dy.zero p.right = true := by
                      exact ⟨Bool.eq_true_of_not_eq_false (fun h => hpositive (Or.inl h)),
                        Bool.eq_true_of_not_eq_false (fun h => hpositive (Or.inr h))⟩
                    have hleft0 : 0 ≤ p.left.toReal := by simpa [Dy.toReal_def] using Dy.toReal_le_of_leB hpos.1
                    have hright0 : 0 ≤ p.right.toReal := by simpa [Dy.toReal_def] using Dy.toReal_le_of_leB hpos.2
                    let E := transformed entry.env.size p.change a b f
                    have hsE : E.scoped (entry.env.size+1) = true := transformed_scoped hsa hsb hsf
                    simp only [Bind.bind,Option.bind_eq_some_iff] at hrun
                    obtain ⟨L,hL,R,hR,vals,hvals,hout⟩ := hrun
                    have hI : Ival.widen c.prec (balancedSum c.prec vals) (Dy.addU c.prec L R) = I := Option.some.inj hout
                    have htail (d : Dy) (right : Bool) (r : Dy)
                        (hd : 0 ≤ d.toReal)
                        (htail : (if dyEq d Dy.zero then some Dy.zero else
                          endpointBound c E (entry.env.map CBox.ofReal) d right p.decay) = some r) :
                        IntervalIntegrable (fun u => E.real (xs++[if right then 1-u else u])) volume 0 d.toReal ∧
                          |∫ u in (0:ℝ)..d.toReal, E.real (xs++[if right then 1-u else u])| ≤ r.toReal ∧
                          ∀ u ∈ Ioc (0:ℝ) d.toReal, E.Converges (xs++[if right then 1-u else u]) := by
                      split at htail
                      · rename_i hz
                        have hz' : d.toReal = 0 := by
                          have hh : d.toRat = Dy.zero.toRat := by simpa only [dyEq,beq_iff_eq] using hz
                          simpa [Dy.toReal_def] using congrArg (fun q : ℚ => (q:ℝ)) hh
                        have hr : Dy.zero = r := Option.some.inj htail
                        subst r
                        simp [hz',Dy.toReal_def]
                      · let path : ParameterPath Unit Set.univ (entry.env.map CBox.ofReal).size :=
                          ⟨fun _ => xs,fun _ _ => by simpa only [Array.size_map] using hx.1,
                            fun _ _ => continuousOn_const⟩
                        have hmem : ∀ q ∈ Set.univ, ∀ i < (entry.env.map CBox.ofReal).size,
                            (((path.val q)[i]?.getD 0:ℝ):ℂ) ∈ (entry.env.map CBox.ofReal)[i]! := by
                          intro q _ i hi
                          have hi' : i < entry.env.size := by simpa using hi
                          rw [getElem!_pos (entry.env.map CBox.ofReal) i hi,Array.getElem_map]
                          simpa only [getElem!_pos entry.env i hi'] using CBox.mem_ofReal (hx.2 i hi')
                        have hh := endpointBound_real_sound hc (by simpa using hsE) htail path hmem
                        exact hh.2.2.2 () (Set.mem_univ ())
                    have hl := htail p.left false L hleft0 hL
                    have hr := htail p.right true R hright0 hR
                    simp only [Bool.false_eq_true,↓reduceIte] at hl hr
                    have hcore : IntervalIntegrable (fun x => E.real (xs++[x])) volume p.a.toReal p.b.toReal ∧
                        (∫ x in p.a.toReal..p.b.toReal, E.real (xs++[x])) ∈ balancedSum c.prec vals :=
                      panel_chain_sound (cert := ⟨p.a,p.b,p.reverse,#[],p.pieces⟩) hp
                        (fun q _ hq V hV => hpanels E entry.env xs hx hsE q V hq hV) hvals
                    have hconv := AssemblyProof.panel_convergence hc hx hsE hp hvals
                    have hmid : IntervalIntegrable (fun x => E.real (xs++[x])) volume p.left.toReal (1-p.right.toReal) ∧
                        (∫ x in p.left.toReal..(1-p.right.toReal), E.real (xs++[x])) ∈ balancedSum c.prec vals := by
                      simpa only [hpa,hpb] using hcore
                    have hrightEq : (∫ u in (0:ℝ)..p.right.toReal, E.real (xs++[1-u])) =
                        ∫ u in (1-p.right.toReal)..(1:ℝ), E.real (xs++[u]) := by
                      simpa only [sub_zero] using (intervalIntegral.integral_comp_sub_left
                        (f := fun u => E.real (xs++[u])) (a := 0) (b := p.right.toReal) 1)
                    have hright : IntervalIntegrable (fun u => E.real (xs++[u])) volume (1-p.right.toReal) 1 := by
                      simpa only [sub_sub_cancel,sub_zero] using (hr.1.comp_sub_left 1).symm
                    have hfull := real_integral_widen (c := c) hl.1 hmid.1 hright hl.2.1
                      (by simpa only [hrightEq] using hr.2.1) (CBox.mem_ofReal hmid.2)
                    have hcan : (NExpr.integral .interval (.rat 0) (.rat 1) E).Converges xs := by
                      refine ⟨trivial,trivial,?_,?_⟩
                      · simpa only [NDomain.Converges,NExpr.real,Rat.cast_zero,Rat.cast_one] using hfull.1
                      · intro u hu
                        have hu' : u ∈ Ioo (0:ℝ) 1 := by
                          simpa only [NExpr.real,Rat.cast_zero,Rat.cast_one,uIoo_of_le zero_le_one] using hu
                        by_cases hul : u ≤ p.left.toReal
                        · exact hl.2.2 u ⟨hu'.1,hul⟩
                        · by_cases hur : 1-p.right.toReal ≤ u
                          · have hh := hr.2.2 (1-u) ⟨by linarith [hu'.2],by linarith⟩
                            simpa only [sub_sub_cancel] using hh
                          · have hlt : p.a.toReal < p.b.toReal := by
                              rw [hpa,hpb]
                              exact (lt_of_not_ge hul).trans (lt_of_not_ge hur)
                            apply hconv.2 hlt u
                            rw [hpa,hpb]
                            exact ⟨(lt_of_not_ge hul).le,(lt_of_not_ge hur).le⟩
                    have hsem := transformed_integral_transport hhow
                      (by simpa only [hx.1] using hsa) (by simpa only [hx.1] using hsb)
                      (by simpa only [hx.1] using hsf) ha.1 hb.1
                      (fun hfin hki => Ival.le_of_leB ha.2 hb.2 (horder hfin hki))
                      (by simpa only [E,hx.1] using hcan)
                    refine ⟨hsem.1,?_⟩
                    have hval : (NExpr.integral kind a b f).real xs =
                        ∫ u in (0:ℝ)..1, E.real (xs++[u]) := by
                      simpa only [E,hx.1,NExpr.real,NDomain.value,Rat.cast_zero,Rat.cast_one] using hsem.2
                    rw [hval,← hI]
                    exact hfull.2.1

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
