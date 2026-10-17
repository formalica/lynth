import Lynth.Interval.Integral.Cert

/-! Untrusted native Petras search. Only the final partition is replayed. -/

namespace Lynth.Interval.Integral

open Intgrl

structure SearchCfg where
  maxPieces : Nat := 16384
  maxDepth : Nat := 192
  maxDegree : Nat := 512
deriving Inhabited

structure WorkPiece where
  a : Dy
  b : Dy
  depth : Nat
  coarse : Option Ival
  priority : Float
deriving Inhabited

def intervalWidth (I : Ival) : Float :=
  match I.width with | some d => d.toFloat.abs | none => 1.0 / 0.0

def heapPush (heap : Array WorkPiece) (w : WorkPiece) : Array WorkPiece := Id.run do
  let mut heap := heap.push w
  let mut i := heap.size - 1
  while i > 0 do
    let j := (i-1)/2
    if heap[j]!.priority ≥ heap[i]!.priority then break
    heap := heap.swapIfInBounds i j
    i := j
  return heap

def heapPop (heap : Array WorkPiece) : Option (WorkPiece × Array WorkPiece) := Id.run do
  if heap.isEmpty then return none
  let head := heap[0]!
  let mut heap := (heap.set! 0 heap.back!).pop
  let mut i := 0
  while 2*i+1 < heap.size do
    let left := 2*i+1
    let right := left+1
    let j := if right < heap.size && heap[right]!.priority > heap[left]!.priority then right else left
    if heap[i]!.priority ≥ heap[j]!.priority then break
    heap := heap.swapIfInBounds i j
    i := j
  return some (head, heap)

def degreeSteps : List Nat :=
  [1,2,4,6,8,12,16,22,32,46,64,90,128,182,256,362,512,724,1024,1448,2048]

def rhoSteps : List Dy := [Dy.ofNat 2, Dy.ofNat 4, Dy.ofNat 8, Dy.ofNat 16]

def fits (p : Nat) (I : Ival) (tol : Dy) : Bool :=
  match I.width with
  | some w => Dy.ltB w (Dy.scale2 tol 1)
  | none => false

structure SearchState where
  tables : Array NodeTable := #[]
  weights : Array (List Ival) := #[]
  bad : List Nat := []
deriving Inhabited

def tableFor (c : Ctx) (n : Nat) (s : SearchState) : Option (Nat × SearchState) := do
  if s.bad.contains n then none else
    match s.tables.findIdx? (fun t => t.roots.length == n) with
    | some i => some (i,s)
    | none => do
      let t ← generateNodes c n
      if t.check c then
        let next := {s with
          tables := s.tables.push t
          weights := s.weights.push (t.weights c)}
        some (s.tables.size, next)
      else none

def chooseRule (c : Ctx) (e : Term) (w : WorkPiece)
    (tol : Dy) (degreeLimit : Nat) : Option (Nat × Dy) := Id.run do
  let mut best : Option (Nat × Dy) := none
  for ρ in rhoSteps do
    let some M := analyticBound c e w.a w.b ρ | continue
    for n in degreeSteps do
      if n > degreeLimit then break
      if let some (m,_) := best then
        if n ≥ m then break
      let some err := errorBound c n w.a w.b ρ M | continue
      if Dy.ltB err tol then
        best := some (n,ρ)
        break
  return best

def workPiece (c : Ctx) (e : Term) (a b : Dy) (depth : Nat) : WorkPiece :=
  let coarse := directPanel c e a b
  ⟨a,b,depth,coarse, coarse.map intervalWidth |>.getD (1.0/0.0)⟩

/-- Absolute tolerance search. Local budgets sum to at most 3*tol/16; the
final checker still tests the complete enclosure against the requested q. -/
def searchFinite (c : Ctx) (e A B : Term) (kind : Region) (tol : ℚ)
    (cfg : SearchCfg := {}) : Option Certificate := Id.run do
  let AI := evalR c A Ival.zero
  let BI := evalR c B Ival.zero
  let (some am, some bm) := (AI.mid, BI.mid) | return none
  let reverse := Dy.ltB bm am
  let a := if reverse then bm else am
  let b := if reverse then am else bm
  if dyEq a b then
    return some ⟨a,b,reverse, #[], [⟨a,b,.direct⟩]⟩
  if kind != .interval && reverse then return none
  let length := b.toRat - a.toRat
  let mut heap := heapPush #[] (workPiece c e a b 0)
  let mut state : SearchState := {}
  let mut pieces : List Piece := []
  let degreeLimit := min cfg.maxDegree (c.prec/2+60)
  for _ in [0:cfg.maxPieces] do
    let some (w, tail) := heapPop heap | break
    heap := tail
    let localTol := Dy.ofRatD c.prec (max (tol / (16 * cfg.maxPieces))
      (tol * (w.b.toRat-w.a.toRat) / length / 8))
    if let some I := w.coarse then
      if fits c.prec I localTol then
        pieces := ⟨w.a,w.b,.direct⟩ :: pieces
        continue
    if let some (n,ρ) := chooseRule c e w localTol degreeLimit then
      match tableFor c n state with
      | some (i,s) =>
        state := s
        let t := state.tables[i]!
        if let some I := gaussPanel c e w.a w.b ρ t state.weights[i]! then
          if fits c.prec I localTol then
            pieces := ⟨w.a,w.b,.gauss i ρ⟩ :: pieces
            continue
      | none => state := {state with bad := n :: state.bad}
    if w.depth ≥ cfg.maxDepth then return none
    let mid := Dy.scale2 (w.a.add w.b) (-1)
    -- For floor(x), place cuts at jumps. Analytic specialization ignores
    -- endpoint values, which do not affect a Lebesgue integral.
    let jump := Dy.ofInt (Fns.Dy.floor mid)
    let mid := if e == .unary .floor .var &&
        Dy.ltB w.a jump && Dy.ltB jump w.b then jump else mid
    if dyEq mid w.a || dyEq mid w.b then return none
    heap := heapPush heap (workPiece c e w.a mid (w.depth+1))
    heap := heapPush heap (workPiece c e mid w.b (w.depth+1))
  if !heap.isEmpty then return none
  return some ⟨a,b,reverse,state.tables,
    pieces.mergeSort (fun p q => Dy.leB p.a q.a)⟩

end Lynth.Interval.Integral
