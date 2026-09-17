

/-!
Tableau Simplex for `≤` systems over `Rat`, à la Dutertre–de Moura
(the algorithm behind Z3's `LRA` theory solver over `src/math/lp`).

Each `∑ cᵢxᵢ + c₀ ≤ 0` gets a slack `s ≥ 0` with row
`s = Σ(-cᵢ)xᵢ + (-c₀)`; originals are unbounded nonbasic vars.
`check` repairs bound-violating basic vars by pivoting, returning a
model on success. UNSAT answers carry no Farkas certificate yet
(`Fourier.solve` is the certifying oracle); the two cores are
differential-tested against each other.
-/
namespace Lynth.Arith.Simplex

/-- Variable id. -/
abbrev Var := Nat

/-- Bounds; `none` = infinite. -/
structure Bounds where
  lo : Option Rat
  hi : Option Rat
  deriving Repr, DecidableEq, Inhabited

/-- Tableau row for a basic var: `x = Σ coeffs[j]·xⱼ + const`
(coeffs indexed by var id, dense). `combo` is the lineage over the
`m` initial equations (for UNSAT explanations); pivot algebra mirrors
coefficient algebra exactly (`new = (-1/a)·old`,
`other += f·new`). -/
structure Row where
  coeffs : Array Rat
  const : Rat
  combo : List Rat
  deriving Repr, DecidableEq, Inhabited

/-- Coefficient lookup with zero default. -/
def coeff (r : Row) (j : Var) : Rat :=
  if h : j < r.coeffs.size then r.coeffs[j] else 0

/-- Simplex state. Bounds are attached to variables (stable across
pivots); `assign` holds nonbasic values. -/
structure State where
  basic : Array Var
  nonbasic : Array Var
  rows : Array Row
  bounds : Array Bounds
  assign : Array Rat
  deriving Repr

/-- Value of variable `v` (nonbasic: `assign`; basic: row evaluation). -/
def value (s : State) (v : Var) : Rat :=
  match s.basic.findIdx? (· == v) with
  | some i =>
    let r := s.rows[i]!
    let sup := List.range s.assign.size
    sup.foldl (fun acc j => acc + coeff r j * s.assign[j]!) 0 + r.const
  | none => s.assign.getD v 0

/-- Bound violation of a variable: `true` iff out of bounds. -/
def violates (s : State) (v : Var) : Bool :=
  let b := s.bounds.getD v { lo := none, hi := none }
  let x := value s v
  match b.lo with
  | some l => if x < l then true else match b.hi with
    | some u => u < x
    | none => false
  | none => match b.hi with
    | some u => u < x
    | none => false

/-- Direction of violation (needs raising / lowering). -/
inductive Dir where
  | below | above
  deriving Repr, DecidableEq

/-- Violation direction, if any. -/
def violDir (s : State) (v : Var) : Option Dir :=
  let b := s.bounds.getD v { lo := none, hi := none }
  let x := value s v
  match b.lo with
  | some l => if x < l then some .below else match b.hi with
    | some u => if u < x then some .above else none
    | none => none
  | none => match b.hi with
    | some u => if u < x then some .above else none
    | none => none

/-- Room to raise / lower a nonbasic variable. -/
def canRaise (s : State) (v : Var) : Bool :=
  match (s.bounds.getD v { lo := none, hi := none }).hi with
  | some u => value s v < u
  | none => true

def canLower (s : State) (v : Var) : Bool :=
  match (s.bounds.getD v { lo := none, hi := none }).lo with
  | some l => l < value s v
  | none => true

/-- Scale a lineage combo. -/
def scaleCombo (c : List Rat) (k : Rat) : List Rat :=
  c.map (· * k)

/-- Add two lineage combos (padded). -/
def addCombo (c d : List Rat) : List Rat :=
  let n := Nat.max c.length d.length
  let pad (l : List Rat) : List Rat := l ++ List.replicate (n - l.length) 0
  List.zipWith (· + ·) (pad c) (pad d)

/-- Pivot row `i` (basic `xi`) with nonbasic `xj`: rewrite so `xj`
becomes basic. `a = row.coeffs[xj]` must be nonzero. `w` is the full
tableau width (originals + slacks); rows must never be narrowed. -/
def pivot (s : State) (i : Nat) (xj : Var) (w : Nat) : State :=
  let r := s.rows[i]!
  let a := coeff r xj
  -- new row for xj (dense over all vars)
  let newRow : Row :=
    { coeffs := (List.range w).toArray.map fun k =>
        if k == xj then 0
        else if k == s.basic[i]! then 1 / a
        else -(coeff r k) / a,
      const := -(r.const) / a,
      combo := scaleCombo r.combo (-1 / a) }
  -- substitute xj in the other rows
  let rows' := s.rows.mapIdx fun k srow =>
    if k == i then newRow
    else
      let f := coeff srow xj
      let nc := addCombo srow.combo
        (scaleCombo newRow.combo f)
      { coeffs := (List.range w).toArray.map fun m =>
          if m == xj then 0
          else coeff srow m + f * (if m == s.basic[i]! then 1 / a
            else if m == xj then 0
            else -(coeff r m) / a),
        const := srow.const + f * (-(r.const) / a),
        combo := nc }
  let xi := s.basic[i]!
  { s with
    rows := rows',
    basic := s.basic.set! i xj,
    nonbasic := s.nonbasic.map fun v => if v == xj then xi else v }

/-- One repair step: fix basic var `xi` (row `i`) via nonbasic `xj`.
Returns the updated state (assignment bumped, tableau pivoted). -/
def repair (s : State) (i : Nat) (xi xj : Var) (w : Nat) : State :=
  let r := s.rows[i]!
  let a := coeff r xj
  let need := match violDir s xi with
    | some .below =>
      match (s.bounds.getD xi { lo := none, hi := none }).lo with
      | some l => l - value s xi
      | none => 0
    | _ =>
      match (s.bounds.getD xi { lo := none, hi := none }).hi with
      | some u => u - value s xi
      | none => 0
  -- bump xj so xi moves by `need`: δ = need / a
  let d := need / a
  let assign' := s.assign.setIfInBounds xj (s.assign.getD xj 0 + d)
  pivot { s with assign := assign' } i xj w

/-- Smallest element of a var list (`none` if empty). -/
def minVar : List Var → Option Var
  | [] => none
  | v :: vs => some (vs.foldl (fun acc w => if w < acc then w else acc) v)

/-- Find a repair pair: smallest basic violator + smallest eligible
nonbasic var (Bland's rule on fixed var ids — required to rule out
cycling). Returns `(rowIdx, xi, xj, isUnsat)`. -/
def findRepair (s : State) : Option (Nat × Var × Var × Bool) :=
  -- returns (rowIdx, xi, xj, isUnsat)
  match minVar (s.basic.toList.filter fun xi => violates s xi) with
  | none => none
  | some xi =>
    let i := (s.basic.findIdx? (· == xi)).getD 0
    let r := s.rows[i]!
    let dir := violDir s xi
    let cands := s.nonbasic.toList.filter fun xj =>
      let a := coeff r xj
      match dir with
      | some .below => (0 < a && canRaise s xj) || (a < 0 && canLower s xj)
      | some .above => (a < 0 && canRaise s xj) || (0 < a && canLower s xj)
      | none => false
    match minVar cands with
    | none => some (i, xi, 0, true)
    | some xj => some (i, xi, xj, false)

/-- UNSAT explanation: lineage over the initial equations plus the
conflicting bound situation. The checker (`Explain.checkExplanation`)
re-derives everything; see there for the soundness argument. -/
structure DdMExplanation where
  combo : List Rat
  xi : Nat
  below : Bool
  bound : Rat
  beta : List Rat
  basic : List Nat
  nonbasic : List Nat
  deriving Repr, DecidableEq

/-- Check outcome: model, refutation with explanation, or unknown. -/
inductive CheckOut where
  | sat : List Rat → CheckOut
  | unsat : DdMExplanation → CheckOut
  | unknown : CheckOut
  deriving Repr, DecidableEq

/-- Full assignment (nonbasic as-is, basic evaluated). -/
def fullAssign (s : State) (total : Nat) : List Rat :=
  (List.range total).map fun v => value s v

/-- Check loop: model on SAT, explanation on UNSAT, unknown on fuel
exhaustion (never conflated). -/
def check : State → Nat → Nat → Nat → CheckOut
  | _, _, _, 0 => .unknown
  | s, n, w, fuel + 1 =>
    match findRepair s with
    | none =>
      -- all basic vars within bounds: read off the model
      .sat ((List.range n).map fun v => value s v)
    | some (i, xi, _, true) =>
      let total := n + s.rows.size
      let r := s.rows[i]!
      let dir := violDir s xi
      let bnd := match dir with
        | some .below =>
          match (s.bounds.getD xi { lo := none, hi := none }).lo with
          | some l => l
          | none => 0
        | _ =>
          match (s.bounds.getD xi { lo := none, hi := none }).hi with
          | some u => u
          | none => 0
      let expl : DdMExplanation :=
        { combo := r.combo, xi := xi,
          below := dir != some .above, bound := bnd,
          beta := fullAssign s total,
          basic := s.basic.toList, nonbasic := s.nonbasic.toList }
      CheckOut.unsat expl
    | some (i, xi, xj, false) => check (repair s i xi xj w) n w fuel

/-- Build the initial state from `∑ coeffs·x + const ≤ 0` constraints
over `n` original variables. Slack rows start with unit lineage. -/
def init (sys : List (List Rat × Rat)) (n : Nat) : State :=
  let m := sys.length
  let total := n + m
  let bounds : Array Bounds :=
    (List.range total).toArray.map fun v =>
      if n ≤ v then { lo := some 0, hi := none } else { lo := none, hi := none }
  let rows : Array Row := (sys.zipIdx.map fun ((cs, c0), k) =>
    { coeffs := (List.range total).toArray.map fun j =>
        if j < n then -(cs.getD j 0) else 0,
      const := -c0,
      combo := (List.range m).map fun t => if t == k then 1 else 0 }).toArray
  { basic := (List.range m).toArray.map (· + n),
    nonbasic := (List.range n).toArray,
    rows, bounds,
    assign := Array.replicate total 0 }

/-- Top-level: model on SAT, explanation on UNSAT, unknown on fuel. -/
def solve (sys : List (List Rat × Rat)) (fuel : Nat := 1024) : CheckOut :=
  let n := sys.foldl (fun m (cs, _) => Nat.max m cs.length) 0
  check (init sys n) n (n + sys.length) fuel

/-- Model checker: every constraint satisfied. -/
def checkModel (sys : List (List Rat × Rat)) (model : List Rat) : Bool :=
  sys.all fun (cs, c0) =>
    decide ((cs.zipIdx.foldl (fun acc (c, i) => acc + c * model.getD i 0) 0 + c0) ≤ 0)

end Lynth.Arith.Simplex
