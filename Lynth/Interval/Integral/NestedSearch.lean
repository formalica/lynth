module

public import Lynth.Interval.Core.Ctx
public import Lynth.Interval.Integral.Math.NestedSyntax
public import Lynth.Interval.Integral.NestedCert

import all Lynth.Interval.Integral.NestedCert

/-! Untrusted adaptive Petras search. Only real quadrature samples recurse;
complex range queries use NestedBounds and the shared Legendre table pool. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl

structure State where
  pool : SearchState := {}
  memo : Memo := {}
  entries : Array Entry := #[]
  remaining : Nat := 16384
  deriving Inhabited

abbrev SearchM := StateT State Option

def spend : SearchM Unit := do
  let s ← get
  if s.remaining == 0 then failure
  set {s with remaining := s.remaining-1}

def remember (c : Ctx) (entry : Entry) : SearchM Ival := do
  let s ← get
  let I ← entryEncl c s.memo s.pool.tables s.pool.weights entry
  if !I.isFinite then failure
  set {s with
    memo := s.memo.insert (key entry.expr entry.env) I
    entries := s.entries.push entry}
  return I

def rule (c : Ctx) (e : Expr) (env : Array Ival) (w : WorkPiece)
    (tol : Dy) : Option (Nat × Dy) := Id.run do
  let mut best := none
  for ρ in rhoSteps do
    let some M := analytic c e env w.a w.b ρ | continue
    for n in degreeSteps do
      if n > min 512 (c.prec/2+60) then break
      if let some (m,_) := best then
        if n ≥ m then break
      let some err := errorBound c n w.a w.b ρ M | continue
      if Dy.ltB err tol then
        best := some (n,ρ)
        break
  return best

def work (c : Ctx) (e : Expr) (env : Array Ival) (a b : Dy) (depth : Nat) : WorkPiece :=
  let coarse := coarsePanel c e env a b
  ⟨a,b,depth,coarse,coarse.map intervalWidth |>.getD (1.0/0.0),none⟩

/-- Accurate values are demanded only on narrow real boxes. The tolerance is
an absolute local target; final acceptance always uses replayed interval widths. -/
partial def evaluate (c : Ctx) (e : Expr) (env : Array Ival) (tol : ℚ) : SearchM Ival := do
  match e with
  | .var i => env[i]?
  | .rat q => return Ival.ofRat c.prec q
  | .pi => return c.pi
  | .unary op a => return unaryR c op (← evaluate c a env (tol/16))
  | .binary op a b =>
    return Binary.evalR c op (← evaluate c a env (tol/16)) (← evaluate c b env (tol/16))
  | .pow a n =>
    let A ← evaluate c a env (tol/16)
    return if n == 2 then Ival.sq c.prec A else Ival.npow c.prec A n
  | .rpow a q => return Fns.rpowIval c (← evaluate c a env (tol/16)) (Ival.ofRat c.prec q)
  | .integral k a b f =>
    spend
    if let some I := (← get).memo[key e env]? then
      if fits c.prec I (Dy.ofRatD c.prec tol) then return I
    if let some I := boundR (e.size+32) c e env then
      if fits c.prec I (Dy.ofRatD c.prec tol) then return I
    -- Avoid spending the subdivision budget below the working precision.
    if tol < (show Dy from ⟨1,8-(c.prec:Int)⟩).toRat then failure
    let _ ← evaluate c a env (tol/64)
    let _ ← evaluate c b env (tol/64)
    let env := (key e env).env
    if k == .whole then
      let anchor := center env.size f
      let _ ← evaluate c (.integral .right anchor (.rat 0) f) env (tol/8)
      let _ ← evaluate c (.integral .left anchor (.rat 0) f) env (tol/8)
      remember c ⟨e,env,.split⟩
    else do
      let s ← get
      let A ← evalWith c s.memo a env
      let B ← evalWith c s.memo b env
      let mut plan : Option Plan := none
      -- Keep finite intervals in their original real coordinates when regular.
      if k.finite then
        let am ← A.mid
        let bm ← B.mid
        let rev := Dy.ltB bm am
        if k != .interval && rev then failure
        let l := if rev then bm else am
        let r := if rev then am else bm
        if (uncertainEndpoint c f env A am).isSome &&
            (uncertainEndpoint c f env B bm).isSome then
          if (coarsePanel c f env l r).isSome then
            plan := some ⟨.identity,l,r,rev,Dy.zero,Dy.zero,2,[]⟩
      let mut E := f
      if plan.isNone then
        let how := if k.finite then Change.affine else
          if k == .right then Change.right else Change.left
        E := transformed env.size how a b f
        -- A regular endpoint needs no truncation. Singular endpoints require
        -- a compositional, uniform power/log/decay remainder certificate.
        let regularL := (boundR (E.size+32) c E (env.push (Ival.ofRats c.prec 0 (1/16)))).isSome
        let regularR := (boundR (E.size+32) c E (env.push (Ival.ofRats c.prec (15/16) 1))).isSome
        for decay in [2,4,8,16,32] do
          for bits in [4,8,16,32,64,128,256] do
            let δ : Dy := ⟨1,-(bits:Int)⟩
            let dl := if regularL then Dy.zero else δ
            let dr := if regularR then Dy.zero else δ
            let el := if regularL then some Dy.zero else
              endpointBound c E (env.map CBox.ofReal) dl false decay
            let er := if regularR then some Dy.zero else
              endpointBound c E (env.map CBox.ofReal) dr true decay
            if let (some l,some r) := (el,er) then
              if Dy.ltB (Dy.addU c.prec l r) (Dy.ofRatD c.prec (tol/32)) then
                plan := some ⟨how,dl,Dy.one.sub dr,false,dl,dr,decay,[]⟩
                break
          if plan.isSome then break
      -- Prefer a smooth power substitution to a long sequence of tiny
      -- panels for algebraic endpoint singularities, when it removes them.
      if k.finite && plan.isSome && plan.any (fun p => p.change != .identity) then
        let mut found := false
        for m in [2,4,8] do
          for right in [false,true] do
            let how := Change.power m right
            let F := transformed env.size how a b f
            if (boundR (F.size+32) c F (env.push (Ival.ofRats c.prec 0 1))).isSome then
              E := F
              plan := some ⟨how,Dy.zero,Dy.one,false,Dy.zero,Dy.zero,2,[]⟩
              found := true
              break
          if found then break
      let p ← plan
      if dyEq p.a p.b then
        return ← remember c ⟨e,env,.panels {p with pieces := [⟨p.a,p.b,.direct⟩]}⟩
      let length := p.b.toRat-p.a.toRat
      let mut heap := heapPush #[] (work c E env p.a p.b 0)
      let mut pieces : List Piece := []
      while !heap.isEmpty do
        spend
        let some (w,tail) := heapPop heap | failure
        heap := tail
        let localTol := Dy.ofRatD c.prec (max (tol/(16*16384))
          (tol*(w.b.toRat-w.a.toRat)/length/8))
        if let some I := w.coarse then
          if fits c.prec I localTol then
            pieces := ⟨w.a,w.b,.direct⟩ :: pieces
            continue
        if let some (n,ρ) := rule c E env w localTol then
          let s ← get
          if let some (i,pool) := tableFor c n s.pool then
            set {s with pool := pool}
            let t := pool.tables[i]!
            let mid := Ival.ofRat c.prec ((w.a.toRat+w.b.toRat)/2)
            let delta := Ival.ofRat c.prec ((w.b.toRat-w.a.toRat)/2)
            for r in t.roots do
              let X := Ival.add c.prec mid (Ival.mul c.prec delta (rootIval r))
              let _ ← evaluate c E (env.push X)
                (localTol.toRat/(64*(1+|length|)))
            let s ← get
            let candidate : Piece := ⟨w.a,w.b,.gauss i ρ⟩
            if let some I := piece c s.memo E env s.pool.tables s.pool.weights candidate then
              if fits c.prec I localTol then
                pieces := candidate :: pieces
                continue
        if w.depth ≥ 192 then failure
        let mid := Dy.scale2 (w.a.add w.b) (-1)
        if dyEq mid w.a || dyEq mid w.b then failure
        heap := heapPush heap (work c E env w.a mid (w.depth+1))
        heap := heapPush heap (work c E env mid w.b (w.depth+1))
      let p := {p with pieces := pieces.mergeSort (fun a b => Dy.leB a.a b.a)}
      remember c ⟨e,env,.panels p⟩

public def search (c : Ctx) (e : Expr) (tol : ℚ) : Option Cert := do
  if !e.scoped 0 || tol ≤ 0 then none else do
    let (_,s) ← (evaluate c e #[] (tol/4)).run {}
    return ⟨s.pool.tables,s.entries⟩

end Lynth.Interval.Integral.Nested
