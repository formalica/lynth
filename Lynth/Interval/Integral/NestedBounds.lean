import Lynth.Interval.Integral.NestedExpr

/-! Cheap uniform complex bounds and endpoint majorants. There is no complex
quadrature here. The distinguished endpoint variable is real and positive;
all remaining parameters may range over complex boxes. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl Fns

private def unit : Ival := Ival.ofRats 64 0 1

/-- Avoid constructing astronomically small dyadic exponents in generic
improper transforms. Since exp(-k) ≤ 2^(-k), this is an enclosure, not flush
-to-zero arithmetic. Positive overflows produce an unbounded range. -/
def safeExp (c : Ctx) (X : Ival) : Ival := Id.run do
  let k := 16*c.prec+1024
  let lower := (Dy.ofNat k).neg
  let tiny : Dy := ⟨1,-(k:Int)⟩
  let some hi := X.hi | return ⟨some Dy.zero,none⟩
  if !Dy.leB hi (Dy.ofNat 16384) then return ⟨some Dy.zero,none⟩
  if Dy.leB hi lower then return ⟨some Dy.zero,some tiny⟩
  let upper := (expPt (c.prec+8) hi).hi
  let lo := match X.lo with
    | some a => if Dy.leB lower a then (expPt (c.prec+8) a).lo else some Dy.zero
    | none => some Dy.zero
  return ⟨lo,upper⟩

def unaryR (c : Ctx) (op : Unary) (X : Ival) : Ival :=
  match op with
  | .exp => safeExp c X
  | .sinh | .cosh =>
    if Ival.leB (Ival.abs X) (Ival.ofRat c.prec 16384) then Unary.evalR c op X
    else Ival.top
  | _ => Unary.evalR c op X

def squareC (p : Nat) (Z : CBox) : CBox :=
  ⟨Ival.sub p (Ival.sq p Z.re) (Ival.sq p Z.im),
   Ival.mul p (Ival.ofRat p 2) (Ival.mul p Z.re Z.im)⟩

def powC (p : Nat) (Z : CBox) (n : Nat) : CBox :=
  if n == 2 then squareC p Z else CBox.npow p Z n

def unaryC (c : Ctx) (op : Unary) (Z : CBox) : Option CBox := do
  let V ← match op with
    | .exp => do
      let E := safeExp c Z.re
      let r ← E.hi
      if exactPoint Z.im 0 then some (CBox.ofReal E) else
        some ⟨⟨some r.neg,some r⟩,⟨some r.neg,some r⟩⟩
    | .inv => if (CBox.normSq c.prec Z).pos then some (CBox.inv c.prec Z) else none
    | .log =>
      if Z.re.negv then some (logBox c (CBox.neg Z))
      else if Z.re.pos then some (logBox c Z) else none
    | .sqrt =>
      if Z.re.nonpos then some (CBox.ofReal Ival.zero)
      else if Z.re.pos then some (sqrtBox c Z) else none
    | .abs =>
      if Z.re.nonneg then some Z else if Z.re.nonpos then some (CBox.neg Z) else none
    | .floor =>
      let F := intFloorIval Z.re
      if let (some a,some b) := (F.lo,F.hi) then
        if dyEq a b then some (CBox.ofReal (Ival.pt a)) else none
      else none
    | .atan =>
      if Ival.ltB (Ival.abs Z.im) Ival.one then some (Unary.evalC c .atan Z) else none
    | _ => some (Unary.evalC c op Z)
  if V.isFinite then some V else none

def binaryC (c : Ctx) (op : Binary) (A B : CBox) : Option CBox := do
  let V ← match op with
    | .div => if (CBox.normSq c.prec B).pos then some (CBox.div c.prec A B) else none
    | .max =>
      if Ival.leB A.re B.re then some B else if Ival.leB B.re A.re then some A else none
    | .min =>
      if Ival.leB A.re B.re then some A else if Ival.leB B.re A.re then some B else none
    | _ => some (Binary.evalC c op A B)
  if V.isFinite then some V else none

def rationalPowerC (c : Ctx) (Z : CBox) (q : ℚ) : Option CBox := do
  if !Z.re.pos then none else do
    let V ← unaryC c .exp (CBox.mul c.prec (logBox c Z) (CBox.ofReal (Ival.ofRat c.prec q)))
    if V.isFinite then some V else none

/-- Enclosure of f(t)/(t^power*(1+|log t|)^logs), for 0<t≤δ≤1.
A finite coefficient box and analytic arithmetic establish a uniform bound
in the other (possibly complex) parameters. -/
structure Scale where
  power : ℚ := 0
  logs : Nat := 0
  coeff : CBox
  deriving Repr, Inhabited

def scaleConst (Z : CBox) : Scale := ⟨0,0,Z⟩
def scaleZero : Scale := scaleConst (CBox.ofReal Ival.zero)

def boxZero (Z : CBox) : Bool := exactPoint Z.re 0 && exactPoint Z.im 0

def boxRadius (c : Ctx) (Z : CBox) : Option Dy := (CBox.norm c.prec Z).hi

def symmetricBox (r : Dy) : CBox :=
  ⟨⟨some r.neg,some r⟩,⟨some r.neg,some r⟩⟩

def factor (c : Ctx) (δ : Dy) (q : ℚ) : Option CBox := do
  if q == 0 then return CBox.ofReal Ival.one
  if q < 0 then none else do
    let I := rpowIval c (Ival.pt δ) (Ival.ofRat c.prec q)
    let h ← I.hi
    return CBox.ofReal ⟨some Dy.zero,some h⟩

def scaleAdd (c : Ctx) (δ : Dy) (A B : Scale) (subtract := false) : Option Scale := do
  let B := if subtract then {B with coeff := CBox.neg B.coeff} else B
  if boxZero A.coeff then return B
  if boxZero B.coeff then return A
  let q := min A.power B.power
  let m := max A.logs B.logs
  let fa ← factor c δ (A.power-q)
  let fb ← factor c δ (B.power-q)
  let fa := if A.logs < m then CBox.mul c.prec fa (CBox.ofReal unit) else fa
  let fb := if B.logs < m then CBox.mul c.prec fb (CBox.ofReal unit) else fb
  return ⟨q,m,CBox.add c.prec (CBox.mul c.prec fa A.coeff) (CBox.mul c.prec fb B.coeff)⟩

def scaleMul (c : Ctx) (A B : Scale) : Scale :=
  ⟨A.power+B.power,A.logs+B.logs,CBox.mul c.prec A.coeff B.coeff⟩

def scaleDiv (c : Ctx) (A B : Scale) : Option Scale := do
  if B.logs != 0 || !(CBox.normSq c.prec B.coeff).pos then none else
    return ⟨A.power-B.power,A.logs,CBox.div c.prec A.coeff B.coeff⟩

def scalePow (c : Ctx) (A : Scale) (n : Nat) : Scale :=
  ⟨A.power*n,A.logs*n,powC c.prec A.coeff n⟩

/-- Forget endpoint dependence only when a finite uniform coefficient bound
can be obtained. A logarithm is absorbed into half a positive power. -/
def collapse (c : Ctx) (δ : Dy) (A : Scale) : Option CBox := do
  if boxZero A.coeff then return CBox.ofReal Ival.zero
  if A.power < 0 || (A.power == 0 && A.logs != 0) then none else do
    if A.logs == 0 then return CBox.mul c.prec A.coeff (← factor c δ A.power)
    let ε := A.power/2
    let C : ℚ := (2:ℚ)^A.logs * (1 + (A.logs.factorial : ℚ) / ε^A.logs)
    let V ← factor c δ ε
    return CBox.mul c.prec A.coeff (CBox.mul c.prec (CBox.ofReal (Ival.ofRat c.prec C)) V)

/-- The normalized coefficient is enclosed, not guessed from samples. -/
def scaleUnary (c : Ctx) (δ : Dy) (decay : Nat) (op : Unary) (A : Scale) : Option Scale := do
  match op with
  | .neg => return {A with coeff := CBox.neg A.coeff}
  | .inv => scaleDiv c (scaleConst (CBox.ofReal Ival.one)) A
  | .sqrt => do
    let V ← unaryC c .sqrt A.coeff
    if A.logs == 0 then return ⟨A.power/2,0,V⟩
    return ⟨A.power/2,(A.logs+1)/2,CBox.mul c.prec (CBox.ofReal (Ival.ofRats 64 0 1)) V⟩
  | .log => do
    let V ← unaryC c .log A.coeff
    let r ← boxRadius c V
    let s := Ival.add c.prec (Ival.ofRat c.prec |A.power|) (Ival.pt r)
    let s := if A.logs == 0 then s else Ival.add c.prec s (Ival.ofRat c.prec A.logs)
    let h ← s.hi
    return ⟨0,1,symmetricBox h⟩
  | .exp =>
    if A.logs != 0 then none else
    if A.power < 0 then do
      let some hi := A.coeff.re.hi | none
      if !Dy.isPos hi.neg || decay == 0 then none else do
        let C := Ival.div c.prec (Ival.ofRat c.prec decay.factorial)
          (Ival.npow c.prec (Ival.pt hi.neg) decay)
        let h ← C.hi
        let Z := if exactPoint A.coeff.im 0 then
            CBox.ofReal ⟨some Dy.zero,some h⟩ else symmetricBox h
        return ⟨(-A.power)*decay,0,Z⟩
    else do
      let V ← unaryC c .exp (← collapse c δ A)
      return scaleConst V
  | .sin | .cos =>
    if (A.power < 0 || A.logs != 0) && exactPoint A.coeff.im 0 then
      return scaleConst (CBox.ofReal (Ival.ofRats c.prec (-1) 1))
    else return scaleConst (← unaryC c op (← collapse c δ A))
  | .abs =>
    if A.coeff.re.nonneg then return A
    else if A.coeff.re.nonpos then return {A with coeff := CBox.neg A.coeff}
    else none
  | _ => return scaleConst (← unaryC c op (← collapse c δ A))

def scaleGuard (c : Ctx) (δ : Dy) (V : Scale) (strict : Bool) : Bool :=
  if strict then V.coeff.re.pos else V.coeff.re.nonneg

/-- Recognize the distinguished positive real endpoint variable. -/
def endpointVar (A : Scale) : Bool :=
  A.power == 1 && A.logs == 0 && exactPoint A.coeff.re 1 && exactPoint A.coeff.im 0

/-- log(t)/(1-log(t)) = -1 + 1/(1-log(t)). Keeping the sign and
separation from zero permits further logarithms and square roots. -/
def logEndpointScale (c : Ctx) (δ : Dy) : Option Scale := do
  if !δ.isPos || !Dy.leB δ (Dy.ofRatD 64 (1/2)) then none else do
    let L := Ival.sub c.prec Ival.one (unaryR c .log (Ival.pt δ))
    let h ← (Ival.inv c.prec L).hi
    let U : Ival := ⟨some Dy.zero,some h⟩
    return ⟨0,1,CBox.ofReal (Ival.add c.prec (Ival.ofRat c.prec (-1)) U)⟩

/-- A first-order endpoint envelope for log(1-t), without quadrature
or a Taylor integration algorithm. -/
def logOneMinusEndpointScale (c : Ctx) (δ : Dy) : Option Scale := do
  if !δ.isPos || !Dy.leB δ (Dy.ofRatD 64 (1/2)) then none else do
    let h ← (Ival.inv c.prec (Ival.sub c.prec Ival.one (Ival.pt δ))).hi
    return ⟨1,0,CBox.ofReal ⟨some h.neg,some Dy.one.neg⟩⟩

/-- A supplied formula is used only after its domain guard is established.
The zero-width case is handled separately, before looking at singular kernels. -/
def scaled : Nat → Ctx → Dy → Nat → Expr → Array Scale → Option Scale
  | 0,_,_,_,_,_ => none
  | fuel+1,c,δ,decay,e,env => do
    match e with
    | .var i => env[i]?
    | .rat q => return scaleConst (CBox.ofReal (Ival.ofRat c.prec q))
    | .pi => return scaleConst (CBox.ofReal c.pi)
    | .unary .log (.var i) =>
      let A ← env[i]?
      if endpointVar A then logEndpointScale c δ else scaleUnary c δ decay .log A
    | .unary .log (.binary .sub (.rat 1) (.var i)) =>
      let A ← env[i]?
      if endpointVar A then logOneMinusEndpointScale c δ else
        scaleUnary c δ decay .log (← scaled fuel c δ decay (.binary .sub (.rat 1) (.var i)) env)
    | .unary .log (.rat q) =>
      return scaleConst (CBox.ofReal (unaryR c .log (Ival.ofRat c.prec q)))
    | .unary op a => scaleUnary c δ decay op (← scaled fuel c δ decay a env)
    | .binary op a b =>
      let A ← scaled fuel c δ decay a env
      let B ← scaled fuel c δ decay b env
      match op with
      | .add => scaleAdd c δ A B
      | .sub => scaleAdd c δ A B true
      | .mul => return scaleMul c A B
      | .div => scaleDiv c A B
      | _ => return scaleConst (← binaryC c op (← collapse c δ A) (← collapse c δ B))
    | .pow a n => return scalePow c (← scaled fuel c δ decay a env) n
    | .rpow a q =>
      let A ← scaled fuel c δ decay a env
      if A.logs != 0 then none else
        return ⟨A.power*q,0,← rationalPowerC c A.coeff q⟩
    | .integral k a b f =>
      let A ← scaled fuel c δ decay a env
      let B ← scaled fuel c δ decay b env
      if k.finite && a == b then return scaleZero
      if let some form := formula env.size k a b f then
        let mut good := true
        for guard in form.nonnegative.toList do
          let G ← scaled fuel c δ decay guard env
          good := good && scaleGuard c δ G false
        if good then return ← scaled fuel c δ decay form.value env
      if !k.finite then none else do
        let W ← scaleAdd c δ B A true
        -- Set integrals require a uniform nonnegative oriented width.
        if k != .interval && !W.coeff.re.nonneg then none else do
          let Y ← scaleAdd c δ A (scaleMul c W (scaleConst (CBox.ofReal unit)))
          let V ← scaled fuel c δ decay f (env.push Y)
          return scaleMul c W V

/-- Explicit integral of t^a (1+|log t|)^m on (0,δ), bounded by an
expanded log moment. The endpoint classifier insists on a>-1. -/
def endpointErrorBound (c : Ctx) (δ : Dy) (A : Scale) : Option Dy := do
  if A.power ≤ -1 then none else do
    let k := A.power+1
    let r ← boxRadius c A.coeff
    let L := Ival.sub c.prec Ival.one (logIval c (Ival.pt δ))
    let mut sum := Ival.zero
    for j in [0:A.logs+1] do
      let coeff : ℚ := (A.logs.factorial : ℚ) / j.factorial / k^(A.logs-j+1)
      sum := Ival.add c.prec sum (Ival.mul c.prec (Ival.ofRat c.prec coeff)
        (Ival.npow c.prec L j))
    let D := rpowIval c (Ival.pt δ) (Ival.ofRat c.prec k)
    (Ival.mul c.prec (Ival.pt r) (Ival.mul c.prec D sum)).hi

def endpointBound (c : Ctx) (e : Expr) (env : Array CBox) (δ : Dy)
    (right : Bool) (decay : Nat) : Option Dy := do
  if !Dy.isPos δ || !Dy.leB δ (Dy.ofRatD 64 (1/2)) then none else do
    let E := endpointExpr env.size right e
    let senv := env.map scaleConst |>.push ⟨1,0,CBox.ofReal Ival.one⟩
    let V ← scaled (E.size+32) c δ decay E senv
    endpointErrorBound c δ V

/-- Complex bound queries use only coarse finite enclosures and uniform
endpoint envelopes. They never run inner adaptive quadrature. -/
def boundC : Nat → Ctx → Expr → Array CBox → Option CBox
  | 0,_,_,_ => none
  | fuel+1,c,e,env => do
    match e with
    | .var i => env[i]?
    | .rat q => return CBox.ofReal (Ival.ofRat c.prec q)
    | .pi => return CBox.ofReal c.pi
    | .unary op a => unaryC c op (← boundC fuel c a env)
    | .binary .div a (.pow b n) =>
      let A ← boundC fuel c a env
      let B ← unaryC c .inv (← boundC fuel c b env)
      binaryC c .mul A (powC c.prec B n)
    | .binary op a b => binaryC c op (← boundC fuel c a env) (← boundC fuel c b env)
    | .pow a n =>
      let V := powC c.prec (← boundC fuel c a env) n
      if V.isFinite then some V else none
    | .rpow a q => rationalPowerC c (← boundC fuel c a env) q
    | .integral k a b f =>
      let A ← boundC fuel c a env
      let B ← boundC fuel c b env
      if k.finite && (a == b || (sameIval A.re B.re && exactPoint A.im 0 &&
          exactPoint B.im 0 && (A.re.width.map (fun w => w.mantissa == 0)).getD false)) then
        return CBox.ofReal Ival.zero
      if let some form := formula env.size k a b f then
        let mut good := true
        for guard in form.nonnegative.toList do
          let G ← boundC fuel c guard env
          good := good && G.re.nonneg
        if good then return ← boundC fuel c form.value env
      if k == .whole then
        let anchor := center env.size f
        -- Recursive convergence includes the split point, although its
        -- contribution to the outer integral has measure zero.
        let C ← boundC fuel c anchor env
        let _ ← boundC fuel c f (env.push C)
        let r ← boundC fuel c (.integral .right anchor (.rat 0) f) env
        let l ← boundC fuel c (.integral .left anchor (.rat 0) f) env
        return CBox.add c.prec r l
      if k.finite then
        if k != .interval && !Ival.leB A.re B.re then return ← none
        let W := CBox.sub c.prec B A
        let Y := CBox.add c.prec A (CBox.mul c.prec W (CBox.ofReal unit))
        if let some V := boundC fuel c f (env.push Y) then
          let out := CBox.mul c.prec W V
          if out.isFinite then return out
      let change := if k.finite then Change.affine else
        if k == .right then Change.right else Change.left
      let E := transformed env.size change a b f
      for bits in [4,8,16,32] do
        let δ : Dy := ⟨1,-(bits:Int)⟩
        let T := Ival.ofRats c.prec δ.toRat (1-δ.toRat)
        if let some V := boundC fuel c E (env.push (CBox.ofReal T)) then
          for decay in [2,4,8,16] do
            let some left := endpointBound c E env δ false decay | continue
            let some right := endpointBound c E env δ true decay | continue
            let mid := CBox.mul c.prec (CBox.ofReal
              (Ival.ofRat c.prec (1-2*δ.toRat))) V
            let err := Dy.addU c.prec left right
            return ⟨Ival.widen c.prec mid.re err,Ival.widen c.prec mid.im err⟩
      none

/-- Coarse real range, allowing nonsmooth real primitives. Recursive
integrals still have to supply a finite convergence bound. -/
def boundR : Nat → Ctx → Expr → Array Ival → Option Ival
  | 0,_,_,_ => none
  | fuel+1,c,e,env => do
    let V ← match e with
      | .var i => env[i]?
      | .rat q => some (Ival.ofRat c.prec q)
      | .pi => some c.pi
      | .unary op a => some (unaryR c op (← boundR fuel c a env))
      | .binary op a b => some (Binary.evalR c op (← boundR fuel c a env) (← boundR fuel c b env))
      | .pow a n =>
        let A ← boundR fuel c a env
        some (if n == 2 then Ival.sq c.prec A else Ival.npow c.prec A n)
      | .rpow a q => some (rpowIval c (← boundR fuel c a env) (Ival.ofRat c.prec q))
      | .integral k a b f =>
        let A ← boundR fuel c a env
        let B ← boundR fuel c b env
        if k.finite && a == b then return Ival.zero
        if k.finite && k != .interval && Ival.leB B A then return Ival.zero
        if let some form := formula env.size k a b f then
          let mut good := true
          for guard in form.nonnegative.toList do
            let G ← boundR fuel c guard env
            good := good && G.nonneg
          if good then return ← boundR fuel c form.value env
        if k.finite then
          let Y : Ival := ⟨(A.lo.bind fun x => B.lo.map (Dy.min x)),
                            (A.hi.bind fun x => B.hi.map (Dy.max x))⟩
          if let some V := boundR fuel c f (env.push Y) then
            let W := Ival.sub c.prec B A
            let out := mulSigned c.prec W V
            if out.isFinite then
              if k == .interval || Ival.leB A B then return out
              else return ⟨out.lo.map (Dy.min Dy.zero),out.hi.map (Dy.max Dy.zero)⟩
        let out ← boundC fuel c e (env.map CBox.ofReal)
        some out.re
    if V.isFinite then some V else none

end Lynth.Interval.Integral.Nested
