import Lynth.FinSearch.Syntax
import Lynth.Sat.Solver
import Lynth.Sat.Cdcl
import Batteries.Data.HashMap
import Batteries.Lean.HashSet

/-!
CNF encoding of `FProp`: one-hot booleans per finite variable plus
Tseitin gates (same pattern as `Lynth.BV` gates, specialized here to
keep the arithmetic-free core dependency-light).

Every finite variable `a` of cardinality `c` gets booleans
`x[a][v]` (`v < c`) with exactly-one constraints. Terms evaluate to
bit-lists; propositions to truth literals. `exactK` uses naive subset
clauses (capped — widths stay tiny in practice).
-/
namespace Lynth.FinSearch.Encode

open Lynth.FinSearch
open Lynth.Sat

/-- Encoder state: fresh vars, clauses, one-hot table, sealed rows,
literal cache. -/
structure EState where
  next : Nat
  clauses : CNF
  onehot : Std.HashMap (Nat × Nat) Nat
  sealed : Std.HashSet (Nat × Nat)
  /-- Canonical Tseitin vars per `(card, value)` literal (literals
  denote constants, so all occurrences share one vector instead of
  allocating fresh vars + units per occurrence). -/
  litcache : Std.HashMap (Nat × Nat) (List Lit)
  /-- One SAT var per opaque theory `atom` id (shared across
  occurrences, like `litcache`). -/
  atomvars : Std.HashMap Nat Lit := {}

abbrev EncodeM := StateM EState

/-- Fresh SAT variable (1-based literal). -/
def freshLit : EncodeM Lit := do
  let s ← get
  set { s with next := s.next + 1 }
  pure (Int.ofNat s.next)

/-- Emit a clause (accumulated reversed; `runEncode` reverses once —
appending per-clause would be quadratic). -/
def emit (cl : Clause) : EncodeM Unit := do
  let s ← get
  set { s with clauses := cl :: s.clauses }

/-- SAT var for one-hot bit `(a, w)`, allocating on first use. -/
def hotVar (a w : Nat) : EncodeM Nat := do
  let s ← get
  match s.onehot[(a, w)]? with
  | some v => pure v
  | none =>
    let v := s.next
    set { s with next := v + 1, onehot := s.onehot.insert (a, w) v }
    pure v

/-- Ensure the one-hot row for variable `a` of cardinality `c`;
assert exactly-one the first time the row completes. -/
def ensureRow (a c : Nat) : EncodeM (List Nat) := do
  let vars ← List.range c |>.mapM fun w => hotVar a w
  let s ← get
  if s.sealed.contains (a, c) then pure vars
  else
    set { s with sealed := s.sealed.insert (a, c) }
    emit (vars.map Int.ofNat)
    for x in vars do
      for y in vars do
        if x < y then emit [-Int.ofNat x, -Int.ofNat y] else pure ()
    pure vars

/-- Term to one-hot bit literals (index = value). Literals share
one canonical vector per `(card, value)` (see `litcache`). -/
def termBits (t : FTerm) : EncodeM (List Lit) := do
  match t with
  | .lit c v =>
    let v := v % c
    let s ← get
    match s.litcache[(c, v)]? with
    | some bs => pure bs
    | none =>
      let bs ← List.range c |>.mapM fun w => do
        let t ← freshLit
        if w == v then emit [t] else emit [-t]
        pure t
      modify fun s => { s with litcache := s.litcache.insert (c, v) bs }
      pure bs
  | .var c a => do
    let vars ← ensureRow a c
    pure (vars.map Int.ofNat)

/-- Tseitin AND/OR/NOT. -/
def gAnd (xs : List Lit) : EncodeM Lit := do
  let o ← freshLit
  for x in xs do emit [-o, x]
  emit ([o] ++ xs.map (-·))
  pure o

def gOr (xs : List Lit) : EncodeM Lit := do
  let o ← freshLit
  for x in xs do emit [-x, o]
  emit ([-o] ++ xs)
  pure o

def gNot (x : Lit) : EncodeM Lit := do
  let o ← freshLit
  emit [-o, -x]; emit [o, x]
  pure o

/-- Equality indicator over one-hot bit lists (same length). -/
def eqBits (as bs : List Lit) : EncodeM Lit := do
  -- eq ⟺ ∨_i (a_i ∧ b_i); one-hot makes the disjuncts exclusive
  let mut disj : List Lit := []
  for (x, y) in as.zip bs do
    let t ← freshLit
    emit [-t, x]; emit [-t, y]; emit [t, -x, -y]
    disj := disj ++ [t]
  gOr disj

/-- Strict less-than over one-hot lists: `a<b ⟺ ∨_i (a_i ∧ ∨_{j>i} b_j)`. -/
def ltBits (as bs : List Lit) : EncodeM Lit := do
  let n := as.length
  let mut disj : List Lit := []
  for i in List.range n do
    let ai := as.getD i 0
    let higher := (List.range n).filter fun j => i < j
    let bj := higher.map fun j => bs.getD j 0
    let anyHigher ← gOr bj
    let t ← freshLit
    emit [-t, ai]; emit [-t, anyHigher]; emit [t, -ai, -anyHigher]
    disj := disj ++ [t]
  gOr disj

/-- All `k`-subsets (order-preserving). -/
def combos : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (combos k xs |>.map (x :: ·)) ++ combos (k + 1) xs

/-- Forced-true literal. -/
def truLit : EncodeM Lit := do
  let t ← freshLit
  emit [t]
  pure t

/-- Exactly-`k`-true via naive subset clauses (capped by caller):
at-most-`k` (every `k+1`-subset has a false member) and at-least-`k`
(every `n-k+1`-subset has a true member). Over-count (`n < k`) is
impossible: force false. -/
def exactKNaive (bs : List Lit) (k : Nat) : EncodeM Lit := do
  if bs.length < k then
    let t ← freshLit
    emit [-t]
    pure t
  else
    let atMost ←
      if k < bs.length then
        gAnd (← (combos (k + 1) bs).mapM fun combo =>
          gOr (combo.map (-·)))
      else pure (← truLit)
    let atLeast ←
      if 0 < k then
        gAnd (← (combos (bs.length - k + 1) bs).mapM fun combo =>
          gOr combo)
      else pure (← truLit)
    gAnd [atMost, atLeast]

/-- Proposition to truth literal. -/
def propBit : FProp → EncodeM Lit
  | .tru => do
    let t ← freshLit
    emit [t]
    pure t
  | .fls => do
    let t ← freshLit
    emit [-t]
    pure t
  | .eq a b => do
    eqBits (← termBits a) (← termBits b)
  | .ne a b => do
    gNot (← eqBits (← termBits a) (← termBits b))
  | .distinct ts => do
    let bss ← ts.mapM termBits
    let mut conj : List Lit := []
    for i in List.range bss.length do
      for j in List.range bss.length do
        if i < j then
          -- pairwise differing bit (XOR per position, OR them)
          let mut dd : List Lit := []
          let pairs := (bss.getD i []).zip (bss.getD j [])
          for (x, y) in pairs do
            let t ← freshLit
            emit [-t, x, y]; emit [-t, -x, -y]; emit [t, -x, y]; emit [t, x, -y]
            dd := dd ++ [t]
          let od ← gOr dd
          conj := conj ++ [od]
        else pure ()
    gAnd conj
  | .lt a b => do
    ltBits (← termBits a) (← termBits b)
  | .le a b => do
    -- a ≤ b ⟺ a < b ∨ a = b
    let l ← ltBits (← termBits a) (← termBits b)
    let as ← termBits a
    let bs ← termBits b
    let e ← eqBits as bs
    gOr [l, e]
  | .and ps => do
    gAnd (← ps.mapM propBit)
  | .or ps => do
    gOr (← ps.mapM propBit)
  | .not p => do
    gNot (← propBit p)
  | .exactK ps k => do
    let bs ← ps.mapM propBit
    exactKNaive bs k
  | .atom i => do
    let s ← get
    match s.atomvars[i]? with
    | some l => pure l
    | none =>
      let l ← freshLit
      modify fun s => { s with atomvars := s.atomvars.insert i l }
      pure l

/-- Boolean simplifier: constant folding (`and`/`or` with `tru`/`fls`,
double negation, singleton collapse). ite-distribution produces many
constant leaves; without this each becomes a Tseitin gate + unit
clauses that bloat the CNF and confuse branching. Semantics
preserved by Boolean identities; the kernel re-verifies anyway. -/
def simpProp : FProp → FProp
  | .and ps =>
    let qs := (ps.map simpProp).filter fun | .tru => false | _ => true
    if qs.any fun | .fls => true | _ => false then .fls
    else match qs with
      | [] => .tru
      | [q] => q
      | _ => .and qs
  | .or ps =>
    let qs := (ps.map simpProp).filter fun | .fls => false | _ => true
    if qs.any fun | .tru => true | _ => false then .tru
    else match qs with
      | [] => .fls
      | [q] => q
      | _ => .or qs
  | .not p =>
    match simpProp p with
    | .tru => .fls
    | .fls => .tru
    | .not q => q
    | q => .not q
  | p => p

/-- Run the encoder on a top-level proposition (asserted true).
Returns clauses + var map + symbolic-var count, or `none` over
limits. One-hot variables are pre-allocated contiguously as
`1..K` (so the solver can restrict branching to them and never
waste decisions on Tseitin gates); gate variables come after.
`extraCells` pre-allocates one-hot rows for cells hidden inside
opaque theory atoms (their rows would otherwise be missing from
the map the lazy loop uses to build blocking clauses). -/
def runEncode (p : FProp) (maxVars : Nat := 8192)
    (extraCells : List (Nat × Nat) := []) :
    Option (CNF × List ((Nat × Nat) × Nat) × Nat) :=
  -- simplify first (constant folding over ite-distribution debris;
  -- can only shrink: every rewrite is a Boolean identity)
  let p := simpProp p
  -- dedupe via hash set (`List.eraseDups` is quadratic and chokes
  -- past ~100k pairs from symbolic list computation); sorted for a
  -- deterministic variable numbering
  let seen : Std.HashSet (Nat × Nat) :=
    ((collectCells p) ++ extraCells).foldl (fun s x => s.insert x) ∅
  let pairs := (seen.toList.toArray.qsort fun x y =>
    decide (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2))).toList
  let (onehot, next) := pairs.foldl (fun (oh, n) (a, c) =>
    ((List.range c).foldl (fun oh w => oh.insert (a, w) (n + w)) oh, n + c))
    (∅, 1)
  let (_, s) := StateT.run (do
    -- seal the theory-atom rows up front: nothing in the base
    -- proposition may mention them, so without this their
    -- exactly-one constraints would never be emitted and decoded
    -- values for those cells would be garbage
    for (a, c) in extraCells do
      let _ ← ensureRow a c
    let t ← propBit p; emit [t])
    { next := next, clauses := [], onehot := onehot, sealed := ∅, litcache := ∅ }
  if s.next > maxVars then none
  else some (s.clauses.reverse, s.onehot.toList, next - 1)

/-- Validity oracle: `true` iff `p` holds under all assignments. -/
def checkValid (p : FProp) (fuel : Nat := 20000) : Bool :=
  -- validity of p ⟺ UNSAT of ¬p
  match runEncode (.not p) with
  | none => false
  | some (cnf, _, _) =>
    match Cdcl.cdclSolve cnf fuel with
    | { result := some .unsat, .. } => true
    | _ => false

end Lynth.FinSearch.Encode
