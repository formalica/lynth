module

public import Init.Control.Basic
public import Init.Control.Do
public import Init.Control.Id
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.List.Control
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Lynth.Interval.Core.Ctx
public import Lynth.Interval.Integral.Eval
public import Lynth.Interval.Integral.Math.Integrand
public import Lynth.Interval.Integral.Powers
public import Lynth.Interval.Num.Ival
import all Lynth.Interval.Integral.Eval

/-! Local common-subexpression evaluation. Entries are scoped to one input
box; no numerical result is reused at another quadrature point. -/

namespace Lynth.Interval.Integral

open Intgrl

public abbrev EvalCache := List (Term × Ival)

@[expose] public def cacheLookup (e : Term) : EvalCache → Option Ival
  | [] => none
  | (a,V)::rest => if a = e then some V else cacheLookup e rest

def CacheSound (s : EvalCache) (x : ℝ) : Prop :=
  ∀ a V, (a,V) ∈ s → a.real x ∈ V

theorem cacheLookup_sound {e : Term} {s : EvalCache} {x : ℝ} {V : Ival}
    (hs : CacheSound s x) (h : cacheLookup e s = some V) : e.real x ∈ V := by
  induction s with
  | nil => simp [cacheLookup] at h
  | cons p s ih =>
    rcases p with ⟨a,W⟩
    unfold cacheLookup at h
    split at h
    · rename_i he
      have hae : a = e := he
      have hWV : W = V := Option.some.inj h
      subst a W
      exact hs e V (by simp)
    · exact ih (fun a V ha => hs a V (by simp [ha])) h

theorem cacheSound_cons {s : EvalCache} {x : ℝ} {e : Term} {V : Ival}
    (hs : CacheSound s x) (h : e.real x ∈ V) : CacheSound ((e,V)::s) x := by
  intro a W ha
  rcases List.mem_cons.mp ha with he | ht
  · cases he; exact h
  · exact hs a W ht

@[expose] public def evalCached (c : Ctx) (e : Term) (X : Ival) (s : EvalCache) : Ival × EvalCache :=
  match cacheLookup e s with
  | some V => (V,s)
  | none =>
    let (V,s) := match e with
      | .var => (X,s)
      | .rat q => (Ival.ofRat c.prec q,s)
      | .pi => (c.pi,s)
      | .unary op a =>
        let (V,s) := evalCached c a X s
        (Unary.evalR c op V,s)
      | .binary op a b =>
        let (V,s) := evalCached c a X s
        if op = .sub ∧ b = .unary .floor a then (fractionalIval c V,s) else
          let (W,s) := evalCached c b X s
          (Binary.evalR c op V W,s)
      | .pow a n =>
        let (V,s) := evalCached c a X s
        (naturalPowerR c.prec V n,s)
      | .rpow a q =>
        let (V,s) := evalCached c a X s
        (rationalPowerR c V q,s)
    (V,(e,V)::s)

theorem evalCached_sound {c : Ctx} (hc : c.Valid) (e : Term)
    {x : ℝ} {X : Ival} (hx : x ∈ X) (s : EvalCache) (hs : CacheSound s x) :
    e.real x ∈ (evalCached c e X s).1 ∧ CacheSound (evalCached c e X s).2 x := by
  induction e generalizing s with
  | var | rat q | pi =>
    unfold evalCached
    cases h : cacheLookup _ s with
    | some V => exact ⟨cacheLookup_sound hs h,hs⟩
    | none =>
      simp only
      first
      | exact ⟨hx,cacheSound_cons hs hx⟩
      | exact ⟨Ival.mem_ofRat _ _,cacheSound_cons hs (Ival.mem_ofRat _ _)⟩
      | exact ⟨hc.pi_mem,cacheSound_cons hs hc.pi_mem⟩
  | unary op a ih =>
    unfold evalCached
    cases h : cacheLookup (.unary op a) s with
    | some V => exact ⟨cacheLookup_sound hs h,hs⟩
    | none =>
      have hh := ih s hs
      have hv := unary_evalR_sound hc op hh.1
      exact ⟨hv,cacheSound_cons hh.2 hv⟩
  | binary op a b ha hb =>
    unfold evalCached
    cases h : cacheLookup (.binary op a b) s with
    | some V => exact ⟨cacheLookup_sound hs h,hs⟩
    | none =>
      have hA := ha s hs
      dsimp only
      split
      · rename_i hfrac
        obtain ⟨rfl,rfl⟩ := hfrac
        have hv := mem_fractionalIval (c := c) hA.1
        exact ⟨hv,cacheSound_cons hA.2 hv⟩
      · have hB := hb _ hA.2
        have hv := binary_evalR_sound hc op hA.1 hB.1
        exact ⟨hv,cacheSound_cons hB.2 hv⟩
  | pow a n ih =>
    unfold evalCached
    cases h : cacheLookup (.pow a n) s with
    | some V => exact ⟨cacheLookup_sound hs h,hs⟩
    | none =>
      have hh := ih s hs
      have hv := mem_naturalPowerR (p := c.prec) hh.1 n
      exact ⟨hv,cacheSound_cons hh.2 hv⟩
  | rpow a q ih =>
    unfold evalCached
    cases h : cacheLookup (.rpow a q) s with
    | some V => exact ⟨cacheLookup_sound hs h,hs⟩
    | none =>
      have hh := ih s hs
      have hv := mem_rationalPowerR hc hh.1 q
      exact ⟨hv,cacheSound_cons hh.2 hv⟩

/-- Select caching only for an expression containing a repeated expensive
subexpression. The common small integrands retain their direct evaluator. -/
@[expose] public def expensiveTerms : Term → List Term
  | .unary op a =>
    let rest := expensiveTerms a
    match op with
    | .exp | .sin | .cos | .log | .sqrt | .sinh | .cosh | .atan
    | .erf | .si | .eta | .airyAi => .unary op a :: rest
    | _ => rest
  | .binary _ a b => expensiveTerms a ++ expensiveTerms b
  | .pow a _ => expensiveTerms a
  | .rpow a q => .rpow a q :: expensiveTerms a
  | _ => []

@[expose] public def needsMemo (e : Term) : Bool := Id.run do
  let mut seen : List Term := []
  for t in expensiveTerms e do
    if seen.contains t then return true
    seen := t::seen
  return false

@[expose] public def prepareEval (c : Ctx) (e : Term) : Ival → Ival :=
  if needsMemo e then fun X => (evalCached c e X []).1 else evalR c e

theorem prepareEval_sound {c : Ctx} (hc : c.Valid) (e : Term)
    {x : ℝ} {X : Ival} (hx : x ∈ X) : e.real x ∈ prepareEval c e X := by
  unfold prepareEval
  split
  · exact (evalCached_sound hc e hx [] (by intro a V h; simp at h)).1
  · exact evalR_sound hc e hx

end Lynth.Interval.Integral
