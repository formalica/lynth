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
  specialized : Option Term := none
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

def rhoSteps : List Dy := [⟨1,1⟩,⟨1,2⟩,⟨1,3⟩,⟨1,4⟩]

def fits (p : Nat) (I : Ival) (tol : Dy) : Bool :=
  match I.width with
  | some w => Dy.ltB w (Dy.scale2 tol 1)
  | none => false

structure SearchState where
  tables : Array NodeTable := #[]
  weights : Array (List Ival) := #[]
  bad : List Nat := []
  reused : List Nat := []
deriving Inhabited

def reusableTable (n : Nat) (s : SearchState) : Option Nat := Id.run do
  let mut best : Option Nat := none
  for i in [0:s.tables.size] do
    let m := s.tables[i]!.roots.length
    if n < m && m ≤ 2*n then
      if best.isNone || m < s.tables[best.getD 0]!.roots.length then best := some i
  return best

/-- Reuse a nearby higher-order rule for the first eight requests. A repeated
degree gets its own table, keeping long runs from paying for extra samples. -/
def tableFor (c : Ctx) (n : Nat) (s : SearchState) (reuse : Bool := false) :
    Option (Nat × SearchState) := do
  if s.bad.contains n then none else
    match s.tables.findIdx? (fun t => t.roots.length == n) with
    | some i => some (i,s)
    | none => do
      if reuse && (s.reused.filter (· == n)).length < 8 then
        if let some i := reusableTable n s then return (i,{s with reused := n::s.reused})
      let t ← generateNodes c n
      if t.check c then
        let next := {s with
          tables := s.tables.push t
          weights := s.weights.push (t.weights c)}
        some (s.tables.size, next)
      else none

/-- Untrusted search data; the final checker recomputes the analytic bound
and error. Keeping the chosen error avoids repeating them while sampling. -/
structure ChosenRule where
  degree : Nat
  rho : Dy
  error : Dy

def chooseRule (c : Ctx) (w : WorkPiece)
    (tol : Dy) (degreeLimit : Nat) : Option ChosenRule := Id.run do
  let some ext := w.specialized | return none
  let mut best : Option ChosenRule := none
  for ρ in rhoSteps do
    let some M := analyticBoundSpecialized c ext w.a w.b ρ | continue
    let binary := (binaryRho ρ).map fun k => (k,binaryErrorBase c w.a w.b M k)
    for n in degreeSteps do
      if n > degreeLimit then break
      if let some rule := best then
        if n ≥ rule.degree then break
      let some err := (match binary with
        | some (k,base) => some (binaryError base k n)
        | none => errorBound c n w.a w.b ρ M) | continue
      if Dy.ltB err tol then
        best := some ⟨n,ρ,err⟩
        break
  return best

def workPiece (c : Ctx) (e : Term) (a b : Dy) (depth : Nat) : WorkPiece :=
  let ext := specialize c (panelBox a b) e
  let coarse := (oscillatoryPanel c e a b).orElse fun _ =>
    directPanelSpecialized c (ext.getD e) a b
  ⟨a,b,depth,coarse, coarse.map intervalWidth |>.getD (1.0/0.0),ext⟩

def hasExpFloor : Term → Bool
  | .unary .floor (.unary .exp .var) => true
  | .unary _ a | .pow a _ | .rpow a _ => hasExpFloor a
  | .binary _ a b => hasExpFloor a || hasExpFloor b
  | _ => false

/-- An untrusted split hint around a jump of floor(exp x). Both sides and
the narrow intervening band are replayed by the ordinary panel checker. -/
def expJumpCuts (c : Ctx) (a b : Dy) : Option (Dy × Dy) := do
  let V := fastExpIval c (panelBox a b)
  let (some lo,some hi) := (V.lo,V.hi) | none
  let ka := Fns.Dy.floor lo
  let kb := Fns.Dy.floor hi
  if ka ≥ kb then none else do
    let k := (ka+kb+1)/2
    if k ≤ 0 then none else do
      let L := Fns.logPt c (c.prec+8) (Dy.ofInt k)
      let (some l,some h) := (L.lo,L.hi) | none
      let margin : Dy := ⟨1,-(c.prec : Int)+16⟩
      let l := Dy.subD c.prec l margin
      let h := Dy.addU c.prec h margin
      if Dy.ltB a l && Dy.ltB l h && Dy.ltB h b then some (l,h) else none

/-- Absolute tolerance search. Share the unused enclosure-width budget among
pending panels, retaining the original length-based target as a lower bound.
The final checker independently tests the complete enclosure and endpoints. -/
def searchFiniteEstimate (c : Ctx) (e A B : Term) (kind : Region) (tol : ℚ)
    (cfg : SearchCfg := {}) : Option (Certificate × Ival) := Id.run do
  let AI := evalR c A Ival.zero
  let BI := evalR c B Ival.zero
  let (some am, some bm) := (AI.mid, BI.mid) | return none
  let reverse := Dy.ltB bm am
  let a := if reverse then bm else am
  let b := if reverse then am else bm
  if dyEq a b then
    -- Distinct uncertain endpoints can have the same rounded midpoint.
    -- Their endpoint allowances must still guide the precision retry.
    let some ea := endpointError c e AI a | return none
    let some eb := endpointError c e BI b | return none
    return some (⟨a,b,reverse, #[], [⟨a,b,.direct⟩]⟩,
      Ival.widen c.prec Ival.zero (Dy.addU c.prec ea eb))
  if kind != .interval && reverse then return none
  let length := b.toRat - a.toRat
  let expJumps := hasExpFloor e
  let mut heap := heapPush #[] (workPiece c e a b 0)
  let mut state : SearchState := {}
  let mut pieces : List Piece := []
  let mut estimates : List Ival := []
  let mut acceptedWidth := Dy.zero
  let degreeLimit := min cfg.maxDegree (c.prec/2+60)
  for _ in [0:cfg.maxPieces] do
    let some (w, tail) := heapPop heap | break
    heap := tail
    let originalTol := max (tol / (16 * cfg.maxPieces))
      (tol * (w.b.toRat-w.a.toRat) / length / 8)
    let sharedTol := (tol/4 - acceptedWidth.toRat) / (4 * (heap.size+1))
    let localTol := Dy.ofRatD c.prec (max originalTol sharedTol)
    if let some I := w.coarse then
      if fits c.prec I localTol then
        pieces := ⟨w.a,w.b,.direct⟩ :: pieces
        estimates := I :: estimates
        acceptedWidth := Dy.addU c.prec acceptedWidth (I.width.getD Dy.zero)
        continue
    if let some rule := chooseRule c w localTol degreeLimit then
      match tableFor c rule.degree state true with
      | some (i,s) =>
        state := s
        let t := state.tables[i]!
        let I := Ival.widen c.prec
          (gaussSamples c e w.a w.b t state.weights[i]!) rule.error
        if fits c.prec I localTol then
          pieces := ⟨w.a,w.b,.gauss i rule.rho⟩ :: pieces
          estimates := I :: estimates
          acceptedWidth := Dy.addU c.prec acceptedWidth (I.width.getD Dy.zero)
          continue
      | none => state := {state with bad := rule.degree :: state.bad}
    if w.depth ≥ cfg.maxDepth then return none
    if expJumps then
      if let some (l,h) := expJumpCuts c w.a w.b then
        heap := heapPush heap (workPiece c e w.a l (w.depth+1))
        heap := heapPush heap (workPiece c e l h (w.depth+1))
        heap := heapPush heap (workPiece c e h w.b (w.depth+1))
        continue
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
  let estimate := balancedSum c.prec estimates
  let estimate := if reverse then Ival.neg estimate else estimate
  let some ea := endpointError c e AI (if reverse then b else a) | return none
  let some eb := endpointError c e BI (if reverse then a else b) | return none
  return some (⟨a,b,reverse,state.tables,
    pieces.mergeSort (fun p q => Dy.leB p.a q.a)⟩,
    Ival.widen c.prec estimate (Dy.addU c.prec ea eb))

/-- Compatibility entry point. Estimates are only witness-selection hints;
the authoritative checker independently replays the returned partition. -/
def searchFinite (c : Ctx) (e A B : Term) (kind : Region) (tol : ℚ)
    (cfg : SearchCfg := {}) : Option Certificate :=
  (searchFiniteEstimate c e A B kind tol cfg).map Prod.fst

end Lynth.Interval.Integral
