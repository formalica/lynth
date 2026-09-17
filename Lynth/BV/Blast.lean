import Lynth.Sat.Syntax
import Lynth.Sat.Solver
import Lynth.Sat.Cdcl

/-!
Bit-blasting core: word-level terms to CNF.

`BvTerm` is the procedure's internal language for fixed-width
bitvectors (cf. Z3's bit-blaster feeding `sat_solver`). Bitwise ops
lower directly; addition becomes a ripple-carry adder; (dis)equality
goals become validity queries answered by the CDCL core. Allocation is
deterministic and the atom→variable map is returned, so differential
tests can rebuild models. Reconstruction of user goals goes through
kernel-checked `bv_decide`; this module is the traced oracle.
-/
namespace Lynth.BV

open Lynth.Sat

/-- Reified fixed-width bitvector term. -/
inductive BvTerm where
  | const : Nat → Nat → BvTerm
  | var : Nat → Nat → BvTerm
  | and : BvTerm → BvTerm → BvTerm
  | or : BvTerm → BvTerm → BvTerm
  | xor : BvTerm → BvTerm → BvTerm
  | not : BvTerm → BvTerm
  | add : BvTerm → BvTerm → BvTerm
  deriving Repr, DecidableEq

/-- Width of a term. -/
def width : BvTerm → Nat
  | .const w _ => w
  | .var w _ => w
  | .and a _ => width a
  | .or a _ => width a
  | .xor a _ => width a
  | .not a => width a
  | .add a _ => width a

/-- Reference evaluation (`assign` maps atom id to value). -/
def eval (t : BvTerm) (assign : Nat → Nat) : Nat :=
  match t with
  | .const w v => v % 2 ^ w
  | .var w a => assign a % 2 ^ w
  | .and a b =>
    let w := width a
    Nat.land (eval a assign) (eval b assign) % 2 ^ w
  | .or a b =>
    let w := width a
    Nat.lor (eval a assign) (eval b assign) % 2 ^ w
  | .xor a b =>
    let w := width a
    Nat.xor (eval a assign) (eval b assign) % 2 ^ w
  | .not a =>
    let w := width a
    Nat.xor (eval a assign) (2 ^ w - 1)
  | .add a b =>
    let w := width a
    (eval a assign + eval b assign) % 2 ^ w

/-- Blast state: next fresh SAT var, clauses, atom-bit map. -/
structure BState where
  next : Nat
  clauses : CNF
  vmap : List ((Nat × Nat) × Nat)

abbrev BlastM := StateM BState

/-- Fresh SAT variable (1-based literal). -/
def freshLit : BlastM Lit := do
  let s ← get
  set { s with next := s.next + 1 }
  pure (Int.ofNat s.next)

/-- Emit a clause. -/
def emit (cl : Clause) : BlastM Unit := do
  let s ← get
  set { s with clauses := s.clauses ++ [cl] }

/-- SAT var for `(atom, bit)`, allocating on first use. -/
def atomVar (a bit : Nat) : BlastM Nat := do
  let s ← get
  match s.vmap.find? fun ((x, y), _) => x == a && y == bit with
  | some (_, v) => pure v
  | none =>
    let v := s.next
    set { s with next := v + 1, vmap := ((a, bit), v) :: s.vmap }
    pure v

/-- Tseitin AND/OR/XOR/NOT gates. -/
def gateAnd (x y : Lit) : BlastM Lit := do
  let o ← freshLit
  emit [-o, x]; emit [-o, y]; emit [o, -x, -y]
  pure o

def gateOr (x y : Lit) : BlastM Lit := do
  let o ← freshLit
  emit [-x, o]; emit [-y, o]; emit [-o, x, y]
  pure o

def gateXor (x y : Lit) : BlastM Lit := do
  let o ← freshLit
  emit [-o, x, y]; emit [-o, -x, -y]; emit [-x, y, o]; emit [x, -y, o]
  pure o

def gateNot (x : Lit) : BlastM Lit := do
  let o ← freshLit
  emit [-o, -x]; emit [o, x]
  pure o

/-- Blast a term to LSB-first bit literals. -/
def blastTerm : BvTerm → BlastM (List Lit)
  | .const w v => do
    List.range w |>.mapM fun i => do
      let t ← freshLit
      -- constant bit
      if (v / 2 ^ i) % 2 == 1 then emit [t] else emit [-t]
      pure t
  | .var w a => do
    List.range w |>.mapM fun i => do
      pure (Int.ofNat (← atomVar a i))
  | .and a b => do
    let as ← blastTerm a
    let bs ← blastTerm b
    (as.zip bs).mapM fun p => gateAnd p.1 p.2
  | .or a b => do
    let as ← blastTerm a
    let bs ← blastTerm b
    (as.zip bs).mapM fun p => gateOr p.1 p.2
  | .xor a b => do
    let as ← blastTerm a
    let bs ← blastTerm b
    (as.zip bs).mapM fun p => gateXor p.1 p.2
  | .not a => do
    (← blastTerm a).mapM gateNot
  | .add a b => do
    let as ← blastTerm a
    let bs ← blastTerm b
    -- ripple-carry adder; `falseV` is a forced-false variable
    let falseV ← freshLit
    emit [-falseV]
    let mut carry : Lit := falseV
    let mut out : List Lit := []
    for (x, y) in as.zip bs do
      let s1 ← gateXor x y
      let s ← gateXor s1 carry
      let t1 ← gateAnd x y
      let t2 ← gateAnd x carry
      let t3 ← gateAnd y carry
      -- carry' = t1 ∨ t2 ∨ t3
      let c' ← freshLit
      emit [-t1, c']; emit [-t2, c']; emit [-t3, c']
      emit [-c', t1, t2, t3]
      out := out ++ [s]
      carry := c'
    pure out

/-- Assert `t1 ≠ t2` (for validity queries of `t1 = t2`). -/
def blastNeq (t1 t2 : BvTerm) : BlastM Unit := do
  let as ← blastTerm t1
  let bs ← blastTerm t2
  let mut disj : List Lit := []
  for (x, y) in as.zip bs do
    let d ← gateXor x y
    disj := disj ++ [d]
  -- nonempty disjunction (widths match at well-typed goals)
  match disj with
  | [] => emit []
  | _ => emit disj

/-- Assert `t1 = t2` bitwise (for validity queries of `t1 ≠ t2`). -/
def blastEqConj (t1 t2 : BvTerm) : BlastM Unit := do
  let as ← blastTerm t1
  let bs ← blastTerm t2
  for (x, y) in as.zip bs do
    emit [-x, y]
    emit [x, -y]

/-- Run the blast; `none` when over limits. Returns clauses + var map. -/
def runBlast (act : BlastM Unit) (maxVars : Nat := 8192) :
    Option (CNF × List ((Nat × Nat) × Nat)) :=
  let (_, s) := StateT.run act { next := 1, clauses := [], vmap := [] }
  if s.next > maxVars then none else some (s.clauses, s.vmap)

/-- Validity oracle for equations: `true` iff `t1 = t2` holds
(CDCL proves UNSAT of the negated equation). -/
def checkValidEq (t1 t2 : BvTerm) (fuel : Nat := 10000) : Bool :=
  if width t1 != width t2 then false
  else match runBlast (blastNeq t1 t2) with
  | none => false
  | some (cnf, _) =>
    match Cdcl.cdclSolve cnf fuel with
    | { result := some .unsat, .. } => true
    | _ => false

/-- Validity oracle for disequations: `true` iff `t1 ≠ t2` holds. -/
def checkValidNe (t1 t2 : BvTerm) (fuel : Nat := 10000) : Bool :=
  if width t1 != width t2 then false
  else match runBlast (blastEqConj t1 t2) with
  | none => false
  | some (cnf, _) =>
    match Cdcl.cdclSolve cnf fuel with
    | { result := some .unsat, .. } => true
    | _ => false

end Lynth.BV
