import Lynth.Interval.Integral.NestedBounds

/-! A postordered certificate DAG. Samples may use only previously replayed
subintegrals. The table pool is shared by every level of quadrature. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl

/-- Evaluate arithmetic accurately, using checked subintegrals at real boxes.
A missing subintegral may only use the independent coarse range evaluator. -/
def evalWith (c : Ctx) (memo : Memo) : Expr → Array Ival → Option Ival
  | .var i,env => env[i]?
  | .rat q,_ => some (Ival.ofRat c.prec q)
  | .pi,_ => some c.pi
  | .unary op a,env => do return unaryR c op (← evalWith c memo a env)
  | .binary op a b,env => do
    return Binary.evalR c op (← evalWith c memo a env) (← evalWith c memo b env)
  | .pow a n,env => do
    let A ← evalWith c memo a env
    return if n == 2 then Ival.sq c.prec A else Ival.npow c.prec A n
  | .rpow a q,env => do return Fns.rpowIval c (← evalWith c memo a env) (Ival.ofRat c.prec q)
  | e,env =>
    if memo.isEmpty then boundR (e.size+32) c e env
    else memo[key e env]? <|> boundR (e.size+32) c e env

structure Plan where
  change : Change := .identity
  a : Dy
  b : Dy
  reverse : Bool := false
  left : Dy := Dy.zero
  right : Dy := Dy.zero
  decay : Nat := 2
  pieces : List Piece
  deriving Repr, Inhabited

inductive EntryMethod where
  | panels (plan : Plan)
  | split
  deriving Repr, Inhabited

structure Entry where
  expr : Expr
  env : Array Ival
  method : EntryMethod
  deriving Repr, Inhabited

structure Cert where
  tables : Array NodeTable := #[]
  entries : Array Entry := #[]
  deriving Repr, Inhabited

def coarsePanel (c : Ctx) (e : Expr) (env : Array Ival) (a b : Dy) : Option Ival := do
  if dyEq a b then return Ival.zero
  let V ← evalWith c {} e (env.push (panelBox a b))
  if !V.isFinite then return ← none
  return mulSigned c.prec (Ival.ofRat c.prec (b.toRat-a.toRat)) V

def analytic (c : Ctx) (e : Expr) (env : Array Ival) (a b ρ : Dy) : Option Dy := do
  if !Dy.ltB Dy.one ρ then none else do
    let Z ← boundC (e.size+32) c e ((env.map CBox.ofReal).push (ellipseBox c a b ρ))
    (CBox.norm c.prec Z).hi

def samples (c : Ctx) (memo : Memo) (e : Expr) (env : Array Ival)
    (a b : Dy) (t : NodeTable) (weights : List Ival) : Option Ival := do
  let mid := Ival.ofRat c.prec ((a.toRat+b.toRat)/2)
  let delta := Ival.ofRat c.prec ((b.toRat-a.toRat)/2)
  let vals ← (t.roots.zip weights).mapM fun (r,w) => do
    let X := Ival.add c.prec mid (Ival.mul c.prec delta (rootIval r))
    return mulSigned c.prec w (← evalWith c memo e (env.push X))
  return mulSigned c.prec delta (balancedSum c.prec vals)

def piece (c : Ctx) (memo : Memo) (e : Expr) (env : Array Ival)
    (tables : Array NodeTable) (weights : Array (List Ival)) (p : Piece) : Option Ival := do
  match p.method with
  | .direct => coarsePanel c e env p.a p.b
  | .gauss i ρ =>
    if !Dy.ltB p.a p.b then none else do
      let t ← tables[i]?
      let M ← analytic c e env p.a p.b ρ
      let err ← errorBound c t.roots.length p.a p.b ρ M
      return Ival.widen c.prec (← samples c memo e env p.a p.b t (← weights[i]?)) err

def uncertainEndpoint (c : Ctx) (e : Expr) (env : Array Ival)
    (I : Ival) (anchor : Dy) : Option Dy := do
  let a ← I.lo
  let b ← I.hi
  if dyEq a anchor && dyEq b anchor then return Dy.zero
  let V ← boundR (e.size+32) c e (env.push (hullPoint I anchor))
  (Ival.mul c.prec (Ival.abs (Ival.sub c.prec I (Ival.pt anchor))) (Ival.abs V)).hi

def entryEncl (c : Ctx) (memo : Memo) (tables : Array NodeTable)
    (weights : Array (List Ival)) (entry : Entry) : Option Ival := do
  let e := entry.expr
  let env := entry.env
  if !e.scoped env.size then return ← none
  let .integral k a b f := e | return ← none
  let A ← evalWith c memo a env
  let B ← evalWith c memo b env
  match entry.method with
  | .split =>
    if k != .whole then none else do
      let anchor := center env.size f
      -- The half-lines exclude their common endpoint. Recursive convergence
      -- of an inner integral at that point must be checked separately.
      let C ← evalWith c memo anchor env
      let _ ← evalWith c memo f (env.push C)
      let R ← evalWith c memo (.integral .right anchor (.rat 0) f) env
      let L ← evalWith c memo (.integral .left anchor (.rat 0) f) env
      return Ival.add c.prec R L
  | .panels p =>
    let cert : Certificate := ⟨p.a,p.b,p.reverse,#[],p.pieces⟩
    if !partitionCheck cert then return ← none
    if p.change == .identity then
      if !k.finite then return ← none
      if k != .interval && (!Ival.leB A B || p.reverse) then return ← none
      let ea ← uncertainEndpoint c f env A (if p.reverse then p.b else p.a)
      let eb ← uncertainEndpoint c f env B (if p.reverse then p.a else p.b)
      let vals ← p.pieces.mapM (piece c memo f env tables weights)
      let S := balancedSum c.prec vals
      return Ival.widen c.prec (if p.reverse then Ival.neg S else S) (Dy.addU c.prec ea eb)
    else
      let expected := if k.finite then Change.affine else
        if k == .right then Change.right else Change.left
      let allowed := match p.change with
        | .power m _ => k.finite && 1 ≤ m && m ≤ 16
        | _ => p.change == expected
      if k == .whole || !allowed || p.reverse then return ← none
      if k.finite && k != .interval && !Ival.leB A B then return ← none
      if !dyEq p.a p.left || !dyEq p.b (Dy.one.sub p.right) then return ← none
      if !Dy.leB Dy.zero p.left || !Dy.leB Dy.zero p.right then return ← none
      let E := transformed env.size p.change a b f
      let tail (d : Dy) (right : Bool) : Option Dy :=
        if dyEq d Dy.zero then some Dy.zero else
          endpointBound c E (env.map CBox.ofReal) d right p.decay
      let l ← tail p.left false
      let r ← tail p.right true
      let vals ← p.pieces.mapM (piece c memo E env tables weights)
      return Ival.widen c.prec (balancedSum c.prec vals) (Dy.addU c.prec l r)

/-- Every stored environment admits a real parameter assignment. This keeps
canonical memo reuse meaningful even when unused slots are erased. -/
def envCheck (env : Array Ival) : Bool := env.all fun I =>
  match I.lo,I.hi with
  | some a,some b => Dy.leB a b
  | _,_ => true

def replay (c : Ctx) (cert : Cert) : Option Memo := do
  if !cert.tables.all (fun t => t.check c) then none else do
    let weights := cert.tables.map (fun t => t.weights c)
    let mut memo : Memo := {}
    for entry in cert.entries do
      if !envCheck entry.env then return ← none
      let I ← entryEncl c memo cert.tables weights entry
      if !I.isFinite then return ← none
      memo := memo.insert (key entry.expr entry.env) I
    return memo

def enclosure (c : Ctx) (e : Expr) (cert : Cert) : Option Ival := do
  if !e.scoped 0 then none else do
    let memo ← replay c cert
    let I ← evalWith c memo e #[]
    if I.isFinite then some I else none

def check (c : Ctx) (e : Expr) (cert : Cert) (q : ℚ) (tol : Term) : Bool :=
  match enclosure c e cert with
  | some I => closeCheck c I q tol
  | none => false

end Lynth.Interval.Integral.Nested
