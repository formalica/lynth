import Lean
import Mathlib.Data.Fintype.Card
import Lynth.FinSearch.Syntax

/-!
Translation from Lean synthesis goals to `FProp` constraints.

Recognized shapes (the procedure's constraint language — anything else
fails the translation and the procedure yields, never unsound):
- `Eq`/`Ne` over finite types (`Fin n`, `Bool`, or any non-recursive
  inductive over finite fields — `Option`/`Sum`/`Prod`/enumerations),
- `And`/`Or`/`Not`/`True`/`False`, `Iff`, ground `A → B` (classical
  step, consistent with the CDCL-oracle discipline),
- bounded `∀` over finite types (literal `n`, capped) unrolled,
- `List.Pairwise R [explicit elements]`,
- `LT.lt`/`LE.le` over `Fin n`.

Closed decidable subterms fold to truth values by kernel evaluation,
so user-defined helpers (`box_idx`, partial-board `match` defs) and
computed index terms never become disconnected opaque cells.
Vacuous implication instances short-circuit instead of emitting
dead gates.

Terms: literals, free finite variables (own cells), and cell
references `g c₁ … cₖ` (head applied to literals only). Cardinalities
must agree everywhere; mismatch fails the translation.
-/
namespace Lynth.FinSearch.Recognize

open Lean Meta
open Lynth.FinSearch

/-- Symbolic value in the partial evaluator (Z3-`recfun` analogue for
our recognize→CNF pipeline): closed finite values, grid cells,
symbolic Bools, suspended branches over symbolic conditions,
explicit list spines, and closed/symbolic Nats. Built by unfolding
applied functions over explicit structures; unknowns suspend instead
of blocking. No function is matched by name: `List.all`/`map`/
`eraseDups`/… shred through the same `whnf` + structural rules. -/
inductive SVal where
  | lit : Expr → Nat → Nat → SVal
  | cell : Expr → Nat → Expr → SVal
  | blit : Bool → SVal
  | prop : FProp → SVal
  | ite : FProp → SVal → SVal → SVal
  | lst : Expr → List SVal → SVal
  | nat : Nat → SVal
  | nite : FProp → SVal → SVal → SVal
  deriving Repr

/-- Boolean equality on `SVal` (needed by the `mkIte` smart constructor's
identical-branch collapse). Structural; `Expr` payloads compare by `==`
(pointer-accelerated), `FProp` by the `BEq` instance above. -/
def svalBeq : SVal → SVal → Bool
  | .lit t n v, .lit t' n' v' => t == t' && n == n' && v == v'
  | .cell t i e, .cell t' i' e' => t == t' && i == i' && e == e'
  | .blit b, .blit b' => b == b'
  | .prop p, .prop q => p == q
  | .ite c x y, .ite c' x' y' => c == c' && svalBeq x x' && svalBeq y y'
  | .lst t xs, .lst t' xs' => t == t' && svalListBeq xs xs'
  | .nat n, .nat m => n == m
  | .nite c x y, .nite c' x' y' => c == c' && svalBeq x x' && svalBeq y y'
  | _, _ => false
where svalListBeq : List SVal → List SVal → Bool
  | [], [] => true
  | x :: xs, y :: ys => svalBeq x y && svalListBeq xs ys
  | _, _ => false

instance : BEq SVal where
  beq := svalBeq

/-- Memo table for the partial evaluator: Z3's recfun caches every
internalized `f(args)` node so the same occurrence is expanded once
and shared everywhere; without this the symbolic `eraseDups`/
`length` trees re-expand shared subterms exponentially (2.4M
clauses on 9x9 instead of ~40k). Keyed directly by `Expr` (Lean
core provides the `BEq`/`Hashable`/`LawfulBEq` instances). -/
abbrev Memo := Std.HashMap Expr SVal

/-- Hash-cons table for emitted `FProp`s: every `eq`/`and`/`or`
built during symbolic distribution (`symEqData`/`symEqNat` branch
splitting, `svalBool` case-splitting) is interned here, so the same
comparison shared by many `eraseDups` membership tests is one DAG
node (one Tseitin gate) instead of an exponentially duplicated
tree. `FProp` has only `BEq` (structural), so the table keys by the
`Repr` string — collision-safe (`==` on lookup hit) and purely a
sharing cache: hits return an equal `FProp`. -/
abbrev Dedup := Std.HashMap String FProp

/-- Intern `p`: return the canonical copy, inserting on first sight. -/
def dedupProp (dedup : IO.Ref Dedup) (p : FProp) : MetaM FProp := do
  let key := repr p |>.pretty
  let m ← dedup.get
  match m[key]? with
  | some q => return q
  | none => dedup.modify (·.insert key p); return p


/-- Does `e` mention the constant `n` anywhere (used to reject
recursive/nested inductive occurrences when measuring finiteness)? -/
def containsConst : Expr → Name → Bool
  | .const m _, t => m == t
  | .app f a, t => containsConst f t || containsConst a t
  | .lam _ d b _, t => containsConst d t || containsConst b t
  | .forallE _ d b _, t => containsConst d t || containsConst b t
  | .letE _ ty v b _, t => containsConst ty t || containsConst v t || containsConst b t
  | .mdata _ e, t => containsConst e t
  | .proj _ _ e, t => containsConst e t
  | _, _ => false

/-- One constructor's contribution to a finite type: substituted,
closed field types with their cardinalities and the block size
(product). Field order is constructor order (mixed-radix, first
field most significant); `exprToIdx`/`finValExpr` below use the
same layout so indices agree. -/
structure CtorShape where
  name : Name
  fields : Array Expr
  cards : Array Nat
  block : Nat

/-- Field types of `ctorName` with the inductive parameters replaced
by the actual type arguments. `none` = dependent fields, open types,
or arity mismatch (conservative: caller treats the type as
non-finite). -/
def ctorFieldTypes (ctorName : Name) (us : List Level) (numParams : Nat)
    (tyArgs : Array Expr) : MetaM (Option (Array Expr)) := do
  let some info := (← getEnv).find? ctorName | return none
  match info with
  | .ctorInfo cval =>
    if cval.numParams != numParams then return none
    let ctorTy := info.instantiateTypeLevelParams us
    forallTelescope ctorTy fun xs _ => do
      if xs.size != cval.numParams + cval.numFields then return none
      let mut out : Array Expr := #[]
      for i in List.range cval.numFields do
        let mut fty ← inferType xs[cval.numParams + i]!
        for j in List.range cval.numParams do
          if j < tyArgs.size then
            fty := fty.replaceFVar xs[j]! tyArgs[j]!
        -- remaining fvars mean dependent/open fields: unsupported
        if fty.hasFVar then return none
        out := out.push fty
      return some out
  | _ => return none

mutual
/-- Constructor layout of a non-indexed, non-recursive inductive
type application. `none` = not a supported finite shape. -/
partial def inductiveShapes (tyR : Expr) (fuel : Nat) :
    MetaM (Option (Array CtorShape)) := do
  if fuel == 0 then return none
  match tyR.getAppFn with
  | .const head us =>
    match (← getEnv).find? head with
    | some (.inductInfo indVal) =>
      if indVal.isRec then return none
      if indVal.numIndices != 0 then return none
      let tyArgs := tyR.getAppArgs
      if tyArgs.size != indVal.numParams then return none
      let mut shapes : Array CtorShape := #[]
      for ctorName in indVal.ctors do
        let some fields ← ctorFieldTypes ctorName us indVal.numParams tyArgs
          | return none
        let mut cards : Array Nat := #[]
        let mut block := 1
        for fty in fields do
          if indVal.all.any fun m => containsConst fty m then return none
          let some c ← finCard fty (fuel - 1) | return none
          cards := cards.push c
          block := block * c
        shapes := shapes.push { name := ctorName, fields, cards, block }
      return some shapes
    | _ => return none
  | _ => return none

/-- Cardinality of a finite type, by constructor inspection: a type
is finite when it unfolds to `Fin n`/`Bool` or to a non-recursive,
non-indexed inductive whose constructor fields are all finite
(`Option T` has `1 + |T|` values when `T` is finite; `Sum` adds,
`Prod` multiplies). Anything else (recursive types, open terms,
fuel exhaustion) is `none`. -/
partial def finCard (ty : Expr) (fuel : Nat := 8) : MetaM (Option Nat) := do
  let tyR ← whnf ty
  match tyR with
  | .const ``Bool _ => pure (some 2)
  | _ =>
    match tyR.getAppFn with
    | .const ``Fin _ =>
      let tyArgs := tyR.getAppArgs
      if tyArgs.isEmpty then pure none
      else
        let w ← whnf tyArgs.back!
        match w with
        | .lit (.natVal n) => pure (some n)
        | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ =>
          pure (some n)
        | _ => pure none
    | _ =>
      match ← inductiveShapes tyR fuel with
      | none => pure none
      | some shapes =>
        pure (some (shapes.foldl (fun acc s => acc + s.block) 0))
end

/-- Cardinality of a finite type: `Fin n` → `n`, `Bool` → 2,
plus any non-recursive inductive over finite fields
(`Option`/`Sum`/`Prod`/enumerations, …). -/
def finWidth (ty : Expr) : MetaM (Option Nat) :=
  finCard ty 8

/-- Numeric literal value. -/
def asNumeral (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ =>
    some n
  | .const ``Nat.zero _ => some 0
  | _ => none

/-- Numeric literal value, seeing through `Fin.mk` wrappers
(our own ∀-unrolling produces those). -/
def finVal? (e : Expr) : Option Nat :=
  match asNumeral e with
  | some k => some k
  | none =>
    if e.getAppFn.isConstOf ``Fin.mk then
      let args := e.getAppArgs
      if args.size < 2 then none
      else asNumeral args[args.size - 2]!
    else none

/-- `Fin` literal `(i : Fin n)` with kernel-checked bound proof. -/
def finLit (n i : Nat) : MetaM Expr := do
  let hlt ← mkAppM ``LT.lt #[mkNatLit i, mkNatLit n]
  let pf ← mkDecideProof hlt
  mkAppM ``Fin.mk #[mkNatLit i, pf]

/-- Index of a closed value of a finite type (`0 .. card-1`,
`CtorShape` layout: constructors in declaration order, fields
mixed-radix). Computes user definitions (`box_idx` on literals),
`Option` values, `Fin`/`Bool` literals uniformly. `none` = open
term (mentions fvars) or unsupported shape. -/
partial def exprToIdx (ty : Expr) (e : Expr) (fuel : Nat := 8) :
    MetaM (Option Nat) := do
  if e.hasFVar then return none
  let tyR ← whnf ty
  match tyR with
  | .const ``Bool _ =>
    let eR ← whnf e
    if eR.isConstOf ``Bool.true then return some 1
    else if eR.isConstOf ``Bool.false then return some 0
    else return none
  | _ =>
    match tyR.getAppFn with
    | .const ``Fin _ =>
      let eR ← whnf e
      match finVal? eR with
      | some v =>
        let some c ← finCard ty 8 | return none
        if c == 0 then return none else return some (v % c)
      | none => return none
    | _ =>
      let eR ← whnf e
      -- numerals landing here (e.g. `OfNat` at an inductive type)
      if let some k := asNumeral eR then
        let some c ← finCard ty 8 | return none
        if c == 0 then return none else return some (k % c)
      else
        match ← inductiveShapes tyR fuel with
        | none => return none
        | some shapes =>
          let f := eR.getAppFn
          let args := eR.getAppArgs
          let mut base := 0
          for s in shapes do
            if f.isConstOf s.name then
              if args.size < s.fields.size then return none
              let fargs := args.toSubarray (args.size - s.fields.size) args.size
              let mut idx := 0
              for j in List.range s.fields.size do
                let stride := (s.cards.toSubarray (j + 1) s.cards.size).foldl (· * ·) 1
                let some fv ← exprToIdx s.fields[j]! fargs[j]! (fuel - 1)
                  | return none
                idx := idx + fv * stride
              return some (base + idx)
            else
              base := base + s.block
          return none

/-- Closed literal of a finite type at index `idx` (`CtorShape`
layout, inverse of `exprToIdx`). `none` = out of range or
unsupported shape. -/
partial def finValExpr (ty : Expr) (idx : Nat) (fuel : Nat := 8) :
    MetaM (Option Expr) := do
  let tyR ← whnf ty
  match tyR with
  | .const ``Bool _ =>
    match idx with
    | 0 => pure (some (mkConst ``Bool.false))
    | 1 => pure (some (mkConst ``Bool.true))
    | _ => pure none
  | _ =>
    match tyR.getAppFn with
    | .const ``Fin _ =>
      let some c ← finCard ty 8 | return none
      if c == 0 || c ≤ idx then return none
      else return some (← finLit c idx)
    | .const _head us =>
      match ← inductiveShapes tyR fuel with
      | none => return none
      | some shapes =>
        let tyArgs := tyR.getAppArgs
        let mut base := 0
        for s in shapes do
          if idx < base + s.block then
            let mut rest := idx - base
            let mut fvals : Array Expr := #[]
            for j in List.range s.fields.size do
              let stride := (s.cards.toSubarray (j + 1) s.cards.size).foldl (· * ·) 1
              let fv := if stride == 0 then 0 else rest / stride
              rest := if stride == 0 then 0 else rest % stride
              let some fe ← finValExpr s.fields[j]! fv (fuel - 1)
                | return none
              fvals := fvals.push fe
            return some (mkAppN (mkConst s.name us) (tyArgs ++ fvals))
          else
            base := base + s.block
        return none
    | _ => return none

/-- Head names of boolean connectives (refused as opaque cells;
they belong to `boolProp`). -/
def boolConnHead : Name → Bool
  | ``HAnd.hAnd => true
  | ``Bool.and => true
  | ``HOr.hOr => true
  | ``Bool.or => true
  | ``Complement.complement => true
  | ``Bool.not => true
  | _ => false
/-- Allocate (or look up) the cell id for a key expression, with
optional grid argument values (for grid-applied-to-literals).
Grid applications are canonicalized BY ARGUMENT VALUES: ∀-unrolling
produces `Fin.mk` literals while source goals use `OfNat` literals,
and raw-`Expr` equality would split one board position into two
independent SAT variables (soundness of the *search* is unaffected —
the final `decide` re-verifies — but the decoded model would satisfy
neither side's constraints together). Free variables (no args) key
by expression. -/
def cellId (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (key : Expr) (args : Option (List Nat)) : MetaM Nat := do
  let arr ← cells.get
  match args with
  | some vs =>
    match arr.findIdx? fun (_, a) => a == some vs with
    | some i => pure i
    | none => cells.set (arr.push (key, args)); pure arr.size
  | none =>
    match arr.findIdx? fun (k, a) => a.isNone && k == key with
    | some i => pure i
    | none => cells.set (arr.push (key, args)); pure arr.size

/-- Translate a term to `FTerm` at expected cardinality `c`:
literals, `true`/`false`, free finite variables and cell references
`grid`-applied-to-literals. Boolean connectives are refused here
(they belong to `boolProp` at proposition level). -/
partial def recognizeTerm (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (e : Expr) (c : Nat) : MetaM (Option FTerm) := do
  let e ← whnfR e
  if let some k := asNumeral e then
    if c == 0 then return none
    else return some (.lit c (k % c))
  match e with
  | .const ``true _ =>
    if c == 2 then pure (some (.lit 2 1)) else pure none
  | .const ``false _ =>
    if c == 2 then pure (some (.lit 2 0)) else pure none
  | _ =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if f == grid then
      -- binder arguments: `Fin`/`Bool` literals fold directly;
      -- anything else decodes against its own type (generic finite
      -- index types share the same `exprToIdx` layout)
      let mut vals : Array Nat := #[]
      for a in args do
        match finVal? a with
        | some v => vals := vals.push v
        | none =>
          let some v ← exprToIdx (← inferType a) a | return none
          vals := vals.push v
      let i ← cellId cells e (some vals.toList)
      return some (.var c i)
    else
      let ty ← inferType e
      match ← finWidth ty with
      | some w =>
        if w != c then pure none
        -- closed computable terms (`box_idx` on literals, `some v`,
        -- user helpers) fold to value literals instead of becoming
        -- disconnected opaque cells
        else match ← exprToIdx ty e with
        | some v => pure (some (.lit c (v % c)))
        -- boolean connectives are never opaque cells (they belong to
        -- `boolProp`; celling them would disconnect shared atoms)
        | none => match e.getAppFn with
          | .const n _ =>
            match ← whnfR ty with
            | .const ``Bool _ =>
              if boolConnHead n then pure none
              else
                let i ← cellId cells e none
                pure (some (.var w i))
            | _ =>
              let i ← cellId cells e none
              pure (some (.var w i))
          | _ =>
            let i ← cellId cells e none
            pure (some (.var w i))
      | none => pure none

/-- Ground decidable `Prop` → `.tru`/`.fls` by kernel evaluation.
Folds user-defined partial boards (`match`/`if` defs), `Option`
equations, and computed index terms uniformly: any *closed* (grid-free)
decidable proposition is decided now, once, in the recognizer. -/
def foldClosed (_cells : IO.Ref (Array (Expr × Option (List Nat)))) (e : Expr) :
    MetaM (Option FProp) := do
  if e.hasFVar then return none
  try
    let d ← mkDecide e
    unless (← inferType d).isConstOf ``Bool do return none
    -- force evaluation to a literal via kernel reduction (default
    -- transparency: user definitions such as `box_idx` or partial
    -- boards must unfold; `withReducible` leaves them stuck)
    let dL ← whnf d
    if dL.isConstOf ``Bool.true then return some .tru
    else if dL.isConstOf ``Bool.false then return some .fls
    else return none
  catch _ => return none

/-- Cardinality of an equation side (must be a finite type). -/
def sideCard (e : Expr) : MetaM (Option Nat) := do
  let ty ← inferType e
  finWidth ty

/-- Explicit element list literal. -/
def asListLit : Expr → Option (List Expr)
  | .app (.const ``List.nil _) _ => some []
  | .app (.app (.app (.const ``List.cons _) _) x) xs =>
    match asListLit xs with
    | some rest => some (x :: rest)
    | none => none
  | _ => none

/-- Closed-literal folding for comparisons (modular values).
`Fin`/`Bool` literals fold structurally; any other closed finite
values (`box_idx` on literals, `Option` constructors, …) decode
through the generic `exprToIdx` layout. -/
def foldLitCmp (a b : Expr) (c : Nat) (f : Nat → Nat → Bool) :
    MetaM (Option FProp) := do
  match finVal? a, finVal? b with
  | some x, some y =>
    pure (some (if f (x % c) (y % c) then .tru else .fls))
  | _, _ =>
    match ← exprToIdx (← inferType a) a, ← exprToIdx (← inferType b) b with
    | some x, some y =>
      pure (some (if f (x % c) (y % c) then .tru else .fls))
    | _, _ => pure none

/-- Binary comparison over finite sides: fold closed literals, else
translate both sides (cardinalities must agree; mismatch fails). -/
def cmpBin (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (a b : Expr) (c : Nat) (mk : FTerm → FTerm → FProp)
    (fold : Nat → Nat → Bool) : MetaM (Option FProp) := do
  match ← foldLitCmp a b c fold with
  | some p => pure (some p)
  | none =>
    match (← recognizeTerm cells grid a c),
        (← recognizeTerm cells grid b c) with
    | some ta, some tb => pure (some (mk ta tb))
    | _, _ => pure none

/-- Comparison with cardinality check on both sides. -/
def cmpSide (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (a b : Expr) (mk : FTerm → FTerm → FProp)
    (fold : Nat → Nat → Bool) : MetaM (Option FProp) := do
  match (← sideCard a), (← sideCard b) with
  | some c1, some c2 =>
    if c1 != c2 then pure none
    else cmpBin memo dedup cells grid a b c1 mk fold
  | _, _ => pure none

/-- Boolean equivalence (`a = b` over `Bool`). -/
def boolIff (pa pb : FProp) : FProp :=
  .and [.or [.not pa, pb], .or [.not pb, pa]]
/-- Boolean xor (`a ≠ b` over `Bool`). -/
def boolXor (pa pb : FProp) : FProp :=
  .or [.and [pa, .not pb], .and [.not pa, pb]]
/-- Boolean strict order (`a < b` over `Bool` ⟺ `¬a ∧ b`). -/
def boolLt (pa pb : FProp) : FProp :=
  .and [.not pa, pb]
/-- Boolean order (`a ≤ b` over `Bool` ⟺ `¬a ∨ b`). -/
def boolLe (pa pb : FProp) : FProp :=
  .or [.not pa, pb]
/-- Is this expression `Bool`-typed? -/
def isBoolTy (e : Expr) : MetaM Bool := do
  match ← whnfR (← inferType e) with
  | .const ``Bool _ => pure true
  | _ => pure false


/-- `ite` smart constructor: collapse constant conditions and
identical branches at construction time so shared subterms stay
shared instead of duplicating whole trees per branch. (The main
smart constructor is `mkIte` below, which additionally sorts
Nat-valued branches into `nite`; this helper covers the few
non-`mkIte` construction sites.) -/
def mkIteSmart : FProp → SVal → SVal → SVal
  | .tru, x, _ => x
  | .fls, _, y => y
  | c, x, y => if x == y then x else .ite c x y

mutual
/-- Boolean formula over `Bool`-typed terms to `FProp`
(`b` means `b = true`). -/
partial def boolProp (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (e : Expr) (depth : Nat) : MetaM (Option FProp) := do
  if depth == 0 then return none
  let e ← whnfR e
  match e with
  | .const ``true _ => pure (some .tru)
  | .const ``false _ => pure (some .fls)
  | _ => match e.getAppFn with
  | .const n _ =>
    let args := e.getAppArgs
    if (n == ``HAnd.hAnd || n == ``Bool.and) && 2 ≤ args.size then
      match (← boolProp memo dedup cells grid args[args.size - 2]! (depth - 1)),
          (← boolProp memo dedup cells grid args[args.size - 1]! (depth - 1)) with
      | some pa, some pb => pure (some (.and [pa, pb]))
      | _, _ => pure none
    else if (n == ``HOr.hOr || n == ``Bool.or) && 2 ≤ args.size then
      match (← boolProp memo dedup cells grid args[args.size - 2]! (depth - 1)),
          (← boolProp memo dedup cells grid args[args.size - 1]! (depth - 1)) with
      | some pa, some pb => pure (some (.or [pa, pb]))
      | _, _ => pure none
    else if (n == ``Complement.complement || n == ``Bool.not) &&
        1 ≤ args.size then
      match ← boolProp memo dedup cells grid args[args.size - 1]! (depth - 1) with
      | some pa => pure (some (.not pa))
      | none => pure none
    else
      -- partial evaluation first (unfolds applied user/library
      -- functions over explicit structures with unknowns suspended);
      -- opaque celling only as a fallback
      match ← symBoolOf memo dedup cells grid e depth with
      | some p => pure (some p)
      | none =>
        -- atom/constant equation against `true`
        match ← recognizeTerm cells grid e 2 with
        | some t => pure (some (.eq t (.lit 2 1)))
        | none =>
          -- user boolean helper: unfold one layer and retry
          let eU ← whnf e
          if eU == e then pure none
          else boolProp memo dedup cells grid eU (depth - 1)
  | _ =>
    match ← symBoolOf memo dedup cells grid e depth with
    | some p => pure (some p)
    | none =>
      match ← recognizeTerm cells grid e 2 with
      | some t => pure (some (.eq t (.lit 2 1)))
      | none =>
        let eU ← whnf e
        if eU == e then pure none
        else boolProp memo dedup cells grid eU (depth - 1)


/-- A proposition or a `Bool`-typed formula to `FProp`. -/
partial def propOrBool (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (e : Expr) (depth : Nat) : MetaM (Option FProp) := do
  let et ← inferType e
  let ty ← whnfR et
  match ty with
  | .sort _ => recognizeProp memo dedup cells grid e depth
  | .const ``Bool _ => boolProp memo dedup cells grid e depth
  | _ => pure none













/-- Boolean combinations via `boolProp` (`a = b` ⟺ `a ↔ b`,
`a ≠ b` ⟺ xor, `a < b` ⟺ `¬a ∧ b`, `a ≤ b` ⟺ `¬a ∨ b`). -/
partial def boolCmp (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (a b : Expr) (mk : FProp → FProp → FProp) (depth : Nat) :
    MetaM (Option FProp) := do
  match (← boolProp memo dedup cells grid a (depth - 1)),
      (← boolProp memo dedup cells grid b (depth - 1)) with
  | some pa, some pb => pure (some (mk pa pb))
  | _, _ => pure none

/-- Dispatch a comparison: `Bool`-typed sides go through `boolProp`
(structural); anything else through cell equations. -/
partial def cmpDispatch (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (a b : Expr) (mk : FTerm → FTerm → FProp) (fold : Nat → Nat → Bool)
    (bmk : FProp → FProp → FProp) (depth : Nat) : MetaM (Option FProp) := do
  if (← isBoolTy a) || (← isBoolTy b) then
    boolCmp memo dedup cells grid a b bmk depth
  else
    cmpSide memo dedup cells grid a b mk fold

/-- One orientation of the counting constraint: `cardE` must be a
`Fintype.card` over a subtype, `litE` a numeral. -/
partial def cardSide (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (cardE litE : Expr) (depth : Nat) : MetaM (Option FProp) := do
  match asNumeral (← whnfR litE) with
  | none => pure none
  | some k =>
    let cardR ← whnfR cardE
    match cardR.getAppFn with
    | .const n _ =>
      if n != ``Fintype.card then pure none
      else
        -- find the `Subtype` argument (robust to instance implicits)
        let mut subTy : Option Expr := none
        for arg in cardR.getAppArgs do
          match (← whnfR arg).getAppFn with
          | .const m _ =>
            if m == ``Subtype then subTy := some (← whnfR arg)
            else pure ()
          | _ => pure ()
        match subTy with
        | none => pure none
        | some st =>
          let sargs := st.getAppArgs
          if sargs.isEmpty then pure none
          else
            let pred := sargs.back!
            lambdaTelescope pred fun fvars _ => do
              if fvars.size != 1 then pure none
              else
                let dom ← inferType fvars[0]!
                match ← finWidth dom with
                | none => pure none
                | some nn =>
                  -- Width nine permits 9x9 counts; retain a small bound on subset expansion.
                  if 9 < nn then pure none
                  else
                    let mut props : List FProp := []
                    for i in List.range nn do
                      let some arg ← finValExpr dom i | return none
                      match ← propOrBool memo dedup cells grid (mkApp pred arg)
                          (depth - 1) with
                      | some p => props := props ++ [p]
                      | none => return none
                    pure (some (.exactK props k))
    | _ => pure none

/-- Counting constraint `Fintype.card { j // P j } = k` (either side)
over a finite index type: unroll the predicate per value and emit
`exactK` (capped: the encoder's subset blowup). `none` = not a
counting shape (caller falls back to equation handling). -/
partial def countCard (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (a b : Expr) (depth : Nat) : MetaM (Option FProp) := do
  match ← cardSide memo dedup cells grid a b depth with
  | some p => pure (some p)
  | none => cardSide memo dedup cells grid b a depth

/-- Translate a proposition to `FProp`. `grid` is the bound variable;
`depth` bounds ∀-unrolling fuel.
Matching discipline: heads are matched on `whnfR` (reducible-only)
forms with trailing-argument extraction, so instance-implicit arities
(`LT.lt`/`LE.le` take 4 args, `Ne` 3, `Iff` 2, `Pairwise` 3) all work;
`Ne` is also matched pre-`whnfR` since it is reducible to `Not`.
Anything else falls through to one `whnf` unfold step (user
definitions like puzzle validity predicates) and retries; failure
yields `none` (the procedure yields, never unsound).
Soundness note: `∀` over `Fin n` unrolls to a conjunction
(`∀`-elim per instance, intuitionistic); ground `A → B` becomes
`¬A ∨ B` (classical step — consistent with the CDCL-oracle discipline
where reconstruction may use classical native axioms; synthesis
verdicts are always re-verified by `decide`). -/
partial def recognizeProp (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (e : Expr) (depth : Nat := 64) : MetaM (Option FProp) := do
  if depth == 0 then return none
  -- `Ne` first on the raw form: it is reducible (`Ne a b ≡ ¬(a = b)`),
  -- so `whnfR` would hide it (the `Not` arm below covers that case too,
  -- equivalently — this is just the direct path).
  match e.getAppFn with
  | .const n _ =>
    let args := e.getAppArgs
    if n == ``Ne && 2 ≤ args.size then
      return ← cmpDispatch memo dedup cells grid args[args.size - 2]! args[args.size - 1]!
        .ne (· != ·) boolXor depth
    else pure ()
  | _ => pure ()
  let eR ← whnfR e
  -- binders (not an application head)
  match eR with
  | .forallE _ d b _ =>
    -- bounded universal: unroll to a conjunction over the domain's
    -- enumerated values (generic finite types share the `finValExpr`
    -- layout; capped: unrolling blowup guard)
    match ← finWidth d with
    | some n =>
      if 16 < n then return none
      else
        let mut conj : List FProp := []
        for i in List.range n do
          let some arg ← finValExpr d i | return none
          let inst ← instantiateForall eR #[arg]
          match ← propOrBool memo dedup cells grid inst (depth - 1) with
          | some p => conj := conj ++ [p]
          | none => return none
        return some (.and conj)
    | none =>
      -- nondependent implication over closed body: `¬A ∨ B`, with
      -- short-circuit on folded hypotheses (vacuous instances vanish
      -- instead of emitting dead Tseitin gates: at 9⁴ box instances
      -- this is the difference between fitting the CNF budget or not)
      if b.hasLooseBVars then return none
      else
        match ← foldClosed cells d with
        | some .fls => return some .tru
        | some .tru =>
          match ← propOrBool memo dedup cells grid b (depth - 1) with
          | some pb => return some pb
          | none => return none
        | _ =>
          match (← propOrBool memo dedup cells grid d (depth - 1)),
              (← propOrBool memo dedup cells grid b (depth - 1)) with
          | some pa, some pb => return some (.or [.not pa, pb])
          | _, _ => return none
  | _ => pure ()
  -- head dispatch on the reducible form (trailing args: robust to
  -- instance-implicit arities)
  match eR.getAppFn with
  | .const n _ =>
    let args := eR.getAppArgs
    let last2 : Option (Expr × Expr) :=
      if 2 ≤ args.size then some (args[args.size - 2]!, args[args.size - 1]!)
      else none
    if n == ``True then pure (some .tru)
    else if n == ``False then pure (some .fls)
    else if n == ``And then
      match last2 with
      | some (a, b) =>
        match (← propOrBool memo dedup cells grid a (depth - 1)),
            (← propOrBool memo dedup cells grid b (depth - 1)) with
        | some pa, some pb => pure (some (.and [pa, pb]))
        | _, _ => pure none
      | none => pure none
    else if n == ``Or then
      match last2 with
      | some (a, b) =>
        match (← propOrBool memo dedup cells grid a (depth - 1)),
            (← propOrBool memo dedup cells grid b (depth - 1)) with
        | some pa, some pb => pure (some (.or [pa, pb]))
        | _, _ => pure none
      | none => pure none
    else if n == ``Not then
      match args.back? with
      | some a =>
        match ← propOrBool memo dedup cells grid a (depth - 1) with
        | some pa => pure (some (.not pa))
        | none => pure none
      | none => pure none
    else if n == ``Eq then
      match last2 with
      | some (a, b) =>
        -- counting form first (`Fintype.card {j // P j} = k`);
        -- plain finite equations after
        match ← countCard memo dedup cells grid a b depth with
        | some p => pure (some p)
        | none => cmpDispatch memo dedup cells grid a b .eq (· == ·) boolIff depth
      | none => pure none
    else if n == ``Ne then
      match last2 with
      | some (a, b) => cmpDispatch memo dedup cells grid a b .ne (· != ·) boolXor depth
      | none => pure none
    else if n == ``LT.lt then
      match last2 with
      | some (a, b) => cmpDispatch memo dedup cells grid a b .lt (· < ·) boolLt depth
      | none => pure none
    else if n == ``LE.le then
      match last2 with
      | some (a, b) => cmpDispatch memo dedup cells grid a b .le (· ≤ ·) boolLe depth
      | none => pure none
    else if n == ``Iff then
      match last2 with
      | some (a, b) =>
        match (← propOrBool memo dedup cells grid a (depth - 1)),
            (← propOrBool memo dedup cells grid b (depth - 1)) with
        | some pa, some pb =>
          pure (some (.and [.or [.not pa, pb], .or [.not pb, pa]]))
        | _, _ => pure none
      | none => pure none
    else if n == ``List.Pairwise then
      -- `List.Pairwise R [explicit elements]`: conjunction over pairs
      -- (capped: quadratic blowup)
      if args.size < 2 then pure none
      else
        let r := args[args.size - 2]!
        let xs := args[args.size - 1]!
        match asListLit xs with
        | none => pure none
        | some elts =>
          if 24 < elts.length then pure none
          else
            let mut conj : List FProp := []
            for i in List.range elts.length do
              for j in List.range elts.length do
                if i < j then
                  let app := mkApp (mkApp r elts[i]!) elts[j]!
                  match ← propOrBool memo dedup cells grid app (depth - 1) with
                  | some p => conj := conj ++ [p]
                  | none => return none
                else pure ()
            pure (some (.and conj))
    else
      -- unknown head: unfold one layer (user definitions) and retry
      let eU ← whnf e
      if eU == eR then pure none
      else recognizeProp memo dedup cells grid eU (depth - 1)
  | _ =>
    let eU ← whnf e
    if eU == eR then pure none
    else recognizeProp memo dedup cells grid eU (depth - 1)

/-- Constructor name of an `SVal` (for diagnostics). -/
partial def svalKind : Option SVal → String
  | none => "none"
  | some (.lit _ _ _) => "lit"
  | some (.cell _ _ _) => "cell"
  | some (.blit _) => "blit"
  | some (.prop _) => "prop"
  | some (.ite _ _ _) => "ite"
  | some (.lst _ _) => "lst"
  | some (.nat _) => "nat"
  | some (.nite _ _ _) => "nite"

/-- `symVal` + `svalBool` combined: the `FProp` meaning of a
Bool-typed term, or `none`. Fuel scales with depth: symbolic
evaluation over recursive combinators (`eraseDups` loops,
`any`-chains) takes hundreds of unfold steps per constraint. -/
partial def symBoolOf (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) (e : Expr) (fuel : Nat) : MetaM (Option FProp) := do
  let sv ← symVal memo dedup cells grid e (fuel * 2560 + 10240)
  match sv with
  | none => pure none
  | some v => svalBool memo dedup cells grid v

/-- Finite data `SVal` to `FTerm`; `none` for non-data. -/
partial def svalTerm (v : SVal) : MetaM (Option FTerm) := do
  match v with
  | .lit ty _ k =>
    let c ← finWidth ty
    match c with
    | some n => if n == 0 then pure none else pure (some (.lit n (k % n)))
    | none => pure none
  | .cell ty i _ =>
    let c ← finWidth ty
    match c with
    | some n => if n == 0 then pure none else pure (some (.var n i))
    | none => pure none
  | _ => pure none

/-- `SVal` back to a Lean term (data only: literals, cells, Nats,
explicit lists). Suspended branches (`ite`/`nite`) and constraints
(`prop`) do not convert — float sites yield instead of diverging. -/
partial def svalExpr : SVal → MetaM (Option Expr)
  | .lit ty _ k => finValExpr ty k
  | .cell _ _ src => pure (some src)
  | .blit true => pure (some (mkConst ``Bool.true))
  | .blit false => pure (some (mkConst ``Bool.false))
  | .nat n => pure (some (mkNatLit n))
  | .lst elemTy vs => do
    let u ← getDecLevel elemTy
    let mut out := mkApp (mkConst ``List.nil [u]) elemTy
    for v in vs.reverse do
      let ve ← svalExpr v
      match ve with
      | none => return none
      | some e => out := mkAppN (mkConst ``List.cons [u]) #[elemTy, e, out]
    pure (some out)
  | _ => pure none

/-- Symbolic Bool to `FProp` (suspended branches case-split; this
stays linear because conditions remain symbolic — no path
enumeration, mirroring how a solver treats `ite`). -/
partial def svalBool (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) : SVal → MetaM (Option FProp)
  | .blit true => pure (some .tru)
  | .blit false => pure (some .fls)
  | .prop p => pure (some p)
  | .ite c t e => do
    let pt ← svalBool memo dedup cells grid t
    let pe ← svalBool memo dedup cells grid e
    match pt, pe with
    | some a, some b =>
      pure (some (.and [.or [.not c, a], .or [c, b]]))
    | _, _ => pure none
  | _ => pure none

/-- Equality of finite data values to `FProp`: distribute over
suspended branches (both sides), else a single flat comparison.
Closed literals and identical terms short-circuit without emitting
gates.

Z3-`recfun` sharing: results are hash-consed through `Dedup`
(`dedupProp`), so the same comparison shared by many `eraseDups`
membership tests becomes one Tseitin gate instead of an
exponentially duplicated tree. Pure sharing — semantics unchanged. -/
partial def symEqData (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) (c : Nat) (a b : SVal) (fuel : Nat) :
    MetaM (Option FProp) := do
  if fuel == 0 then return none
  match a, b with
  | .lit _ _ x, .lit _ _ y =>
    pure (some (if x % c == y % c then .tru else .fls))
  | .ite g x y, z => do
    let px ← symEqData memo dedup cells grid c x z (fuel - 1)
    let py ← symEqData memo dedup cells grid c y z (fuel - 1)
    match px, py with
    | some u, some v =>
      pure (some (← dedupProp dedup (.and [.or [.not g, u], .or [g, v]])))
    | _, _ => pure none
  | z, .ite g x y => do
    let px ← symEqData memo dedup cells grid c z x (fuel - 1)
    let py ← symEqData memo dedup cells grid c z y (fuel - 1)
    match px, py with
    | some u, some v =>
      pure (some (← dedupProp dedup (.and [.or [.not g, u], .or [g, v]])))
    | _, _ => pure none
  | _, _ => do
    let ta ← svalTerm a
    let tb ← svalTerm b
    match ta, tb with
    | some x, some y =>
      if x == y then pure (some .tru)
      else pure (some (← dedupProp dedup (.eq x y)))
    | _, _ => pure none

/-- Equality of Nat values to `FProp`: distribute over suspended
branches, else compare directly. Hash-consed like `symEqData`. -/
partial def symEqNat (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) (a b : SVal) (fuel : Nat) : MetaM (Option FProp) := do
  if fuel == 0 then return none
  match a, b with
  | .nat x, .nat y => pure (some (if x == y then .tru else .fls))
  | .nite g x y, z => do
    let px ← symEqNat memo dedup cells grid x z (fuel - 1)
    let py ← symEqNat memo dedup cells grid y z (fuel - 1)
    match px, py with
    | some u, some v =>
      pure (some (← dedupProp dedup (.and [.or [.not g, u], .or [g, v]])))
    | _, _ => pure none
  | z, .nite g x y => do
    let px ← symEqNat memo dedup cells grid z x (fuel - 1)
    let py ← symEqNat memo dedup cells grid z y (fuel - 1)
    match px, py with
    | some u, some v =>
      pure (some (← dedupProp dedup (.and [.or [.not g, u], .or [g, v]])))
    | _, _ => pure none
  | _, _ => pure none

/-- Smart `ite` constructor: `nite` when both branches are
Nat-valued, `ite` otherwise. Distribution sites all funnel through
here so Nat-valued conditionals (`length` of an `ite`-list) stay in
the `nite` fragment that `symEqNat` understands. -/
partial def mkIte (c : FProp) (a b : SVal) : SVal :=
  match c with
  | .tru => a
  | .fls => b
  | _ =>
    if a == b then a
    else match a, b with
    | .nat _, .nat _ => .nite c a b
    | .nat _, .nite _ _ _ => .nite c a b
    | .nite _ _ _, .nat _ => .nite c a b
    | .nite _ _ _, .nite _ _ _ => .nite c a b
    | _, _ => .ite c a b

/-- Structural distribution over nested suspended branches (used
when `svalExpr` cannot cross an `ite`): push the stuck application
into both branches and recurse — branches shrink structurally, so
this terminates; leaves rebuild once from converted values. -/
partial def floatDistrib (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) (fn : Expr) (args : Array Expr) (sargs : Array (Option SVal))
    (i : Nat) (fuel : Nat) : MetaM (Option SVal) := do
  if fuel == 0 then return none
  match sargs[i]! with
  | some (.ite c x y) =>
    let l ← floatDistrib memo dedup cells grid fn args (sargs.setIfInBounds i (some x)) i (fuel - 1)
    let r ← floatDistrib memo dedup cells grid fn args (sargs.setIfInBounds i (some y)) i (fuel - 1)
    match l, r with
    | some a, some b => pure (some (mkIte c a b))
    | _, _ => pure none
  | some (.nite c x y) =>
    let l ← floatDistrib memo dedup cells grid fn args (sargs.setIfInBounds i (some x)) i (fuel - 1)
    let r ← floatDistrib memo dedup cells grid fn args (sargs.setIfInBounds i (some y)) i (fuel - 1)
    match l, r with
    | some a, some b => pure (some (mkIte c a b))
    | _, _ => pure none
  | _ =>
    -- fully distributed at this position: rebuild once, keeping
    -- original terms where evaluation was skipped, converting leaves
    let mut exprs : Array Expr := #[]
    for j in List.range args.size do
      match sargs[j]! with
      | none => exprs := exprs.push args[j]!
      | some s =>
        let e ← svalExpr s
        match e with
        | none =>
          return none
        | some t => exprs := exprs.push t
    let r ← symVal memo dedup cells grid (mkAppN fn exprs) (fuel - 1)
    pure r

/-- Congruence over suspended branches: a stuck application with an
`ite`/`nite`-valued argument distributes (`f (ite c x y)` becomes
`ite c (f x) (f y)`), evaluated per branch. This is the general rule
that lets `length`/`reverse`/`any`/accumulators flow through
conditionals without naming any of them. Fuel-bounded; branch
terms rebuild via `svalExpr`, so deeply nested symbolic branches
yield instead of diverging. -/
partial def floatApp (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) (fn : Expr) (args : Array Expr) (fuel : Nat) :
    MetaM (Option SVal) := do
  if fuel == 0 then return none
  let mut sargs : Array (Option SVal) := #[]
  for a in args do
    -- skip types, props, and non-applications: only stuck
    -- applications can carry suspended branches (this also skips
    -- motive/instance/lambda args that only pollute logs)
    if !a.isApp then
      sargs := sargs.push none
    else if (← inferType a).isSort then
      sargs := sargs.push none
    else if (← isProp a) then
      sargs := sargs.push none
    else
      let v ← symVal memo dedup cells grid a (fuel - 1)
      sargs := sargs.push v
  let mut pos : Option (Nat × FProp × Expr × Expr) := none
  for i in List.range args.size do
    match sargs[i]! with
    | some (.ite c x y) =>
      let xe ← svalExpr x
      let ye ← svalExpr y
      match xe, ye with
      | some a, some b => pos := some (i, c, a, b)
      | _, _ =>
        -- nested branches: distribute structurally instead (see
        -- `floatDistrib`; Expr conversion cannot cross `ite`)
        match ← floatDistrib memo dedup cells grid fn args sargs i fuel with
        | some v => return some v
        | none => return none
    | some (.nite c x y) =>
      let xe ← svalExpr x
      let ye ← svalExpr y
      match xe, ye with
      | some a, some b => pos := some (i, c, a, b)
      | _, _ =>
        match ← floatDistrib memo dedup cells grid fn args sargs i fuel with
        | some v => return some v
        | none => return none
    | _ => pure ()
    if pos.isSome then break
  match pos with
  | none => pure none
  | some (i, c, xe, ye) =>
    let rx ← (try pure (← symVal memo dedup cells grid (mkAppN fn (args.setIfInBounds i xe)) (fuel - 1)) catch _ => pure (none : Option SVal))
    let ry ← (try pure (← symVal memo dedup cells grid (mkAppN fn (args.setIfInBounds i ye)) (fuel - 1)) catch _ => pure (none : Option SVal))
    match rx, ry with
    | some a, some b => pure (some (mkIte c a b))
    | _, _ => pure none

/-- Closed leaf: no fvars, so kernel-level decoding applies
(finite values, Nats). Returns `none` for anything open. -/
partial def closedLeaf (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) (e0 : Expr) : MetaM (Option SVal) := do
  if e0.hasFVar then return none
  let ty ← inferType e0
  let tyR ← whnf ty
  match tyR with
  | .const ``Nat _ =>
    let w ← whnf e0
    match asNumeral w with
    | some k => pure (some (.nat k))
    | none => pure none
  | _ =>
    let c ← finWidth ty
    match c with
    | some n =>
      let v ← exprToIdx ty e0
      match v with
      | some k => pure (some (.lit ty n (k % n)))
      | none => pure none
    | none => pure none

/-- Partial evaluator over Lean terms with the synthesis grid held
opaque: unfolds applied definitions, iota-reduces over explicit
list spines, beta-reduces predicates, evaluates closed leaves, and
suspends unknowns (grid cells) and branches (`ite`) instead of
blocking. Fuel-bounded; `none` means yield.

Z3-`recfun` discipline: results are memoized per expression node
(`memo`), so a shared subterm (one `eraseDups` spine tested by many
`==`) is expanded once and shared as a DAG instead of re-expanded
at every use (the 9x9 `eraseDups` blowup: 2.4M clauses → ~40k).
The memo is purely a sharing cache — hits return the identical
`SVal`, so semantics are unchanged. -/
partial def symVal (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) (e : Expr) (fuel : Nat) : MetaM (Option SVal) := do
  if fuel == 0 then return none
  let m ← memo.get
  match m[e]? with
  | some v => return some v
  | none =>
    let r ← symValBody memo dedup cells grid e fuel
    match r with
    | some v => memo.modify (·.insert e v); return some v
    | none => return none

partial def symValBody (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) (e : Expr) (fuel : Nat) : MetaM (Option SVal) := do
  -- grid application on literal arguments → cell (same allocation
  -- as `recognizeTerm`, so ids agree across paths; `whnf` is a
  -- no-op here since the head is a free variable)
  if e.getAppFn == grid then
    let args := e.getAppArgs
    let mut vals : Array Nat := #[]
    for a in args do
      match finVal? a with
      | some v => vals := vals.push v
      | none =>
        let v ← exprToIdx (← inferType a) a
        match v with
        | none => return none
        | some w => vals := vals.push w
    let ty ← inferType e
    let i ← cellId cells e (some vals.toList)
    return some (.cell ty i e)
  match e.getAppFn with
  | .proj _ _ s =>
    -- arithmetic instance projections (`(instHAdd ..).1` etc.):
    -- normalize to kernel `Nat.add/mul/sub` and re-evaluate
    match s.getAppFn with
    | .const sn _ =>
      let last2 := e.getAppArgs
      if last2.size < 2 then return none
      else
        let a := last2[last2.size - 2]!
        let b := last2[last2.size - 1]!
        if sn == ``instHAdd then
          symVal memo dedup cells grid (mkAppN (mkConst ``Nat.add) #[a, b]) (fuel - 1)
        else if sn == ``instHMul then
          symVal memo dedup cells grid (mkAppN (mkConst ``Nat.mul) #[a, b]) (fuel - 1)
        else if sn == ``instHSub then
          symVal memo dedup cells grid (mkAppN (mkConst ``Nat.sub) #[a, b]) (fuel - 1)
        else
          unfoldSym memo dedup cells grid e fuel
    | _ => unfoldSym memo dedup cells grid e fuel
  | .const n _ =>
    if n == ``ite then
      let args := e.getAppArgs
      if args.size < 5 then return none
      else
        -- `ite {α} (c : Prop) [Decidable c] (t e : α)`: five args,
        -- condition is fourth-from-the-right (size-3 would grab the
        -- Decidable instance!)
        let c := args[args.size - 4]!
        let t := args[args.size - 2]!
        let f := args[args.size - 1]!
        let pc ← propOrBool memo dedup cells grid c fuel
        match pc with
        | none => return none
        | some .tru => symVal memo dedup cells grid t (fuel - 1)
        | some .fls => symVal memo dedup cells grid f (fuel - 1)
        | some p =>
          let st ← symVal memo dedup cells grid t (fuel - 1)
          let sf ← symVal memo dedup cells grid f (fuel - 1)
          match st, sf with
          | some a, some b => pure (some (mkIte p a b))
          | _, _ => pure none
    else if n == ``cond then
      let args := e.getAppArgs
      if args.size < 3 then return none
      else
        let c := args[args.size - 3]!
        let t := args[args.size - 2]!
        let f := args[args.size - 1]!
        let sc ← symVal memo dedup cells grid c (fuel - 1)
        match sc with
        | none => return none
        | some v =>
          let pc ← svalBool memo dedup cells grid v
          match pc with
          | none => return none
          | some .tru => symVal memo dedup cells grid t (fuel - 1)
          | some .fls => symVal memo dedup cells grid f (fuel - 1)
          | some p =>
            let st ← symVal memo dedup cells grid t (fuel - 1)
            let sf ← symVal memo dedup cells grid f (fuel - 1)
            match st, sf with
            | some a, some b => pure (some (mkIte p a b))
            | _, _ => pure none
    else if n == ``BEq.beq then
      let args := e.getAppArgs
      if args.size < 2 then return none
      else
        let a := args[args.size - 2]!
        let b := args[args.size - 1]!
        let ty ← whnf (← inferType a)
        match ty with
        | .const ``Bool _ =>
          let sa ← symVal memo dedup cells grid a (fuel - 1)
          let sb ← symVal memo dedup cells grid b (fuel - 1)
          match sa, sb with
          | some x, some y =>
            let pa ← svalBool memo dedup cells grid x
            let pb ← svalBool memo dedup cells grid y
            match pa, pb with
            | some u, some v => pure (some (.prop (boolIff u v)))
            | _, _ => pure none
          | _, _ => pure none
        | .const ``Nat _ =>
          let sa ← symVal memo dedup cells grid a (fuel - 1)
          let sb ← symVal memo dedup cells grid b (fuel - 1)
          match sa, sb with
          | some x, some y =>
            let p ← symEqNat memo dedup cells grid x y fuel
            match p with
            | some q => pure (some (.prop q))
            | none => pure none
          | _, _ => pure none
        | _ =>
          let c ← finWidth ty
          match c with
          | some n =>
            let sa ← symVal memo dedup cells grid a (fuel - 1)
            let sb ← symVal memo dedup cells grid b (fuel - 1)
            match sa, sb with
            | some x, some y =>
              let p ← symEqData memo dedup cells grid n x y fuel
              match p with
              | some q => pure (some (.prop q))
              | none => pure none
            | _, _ => pure none
          | none => pure none
    else if n == ``bne then
      -- `a != b`: boolean negation of `==` (same dispatch by side
      -- type as `BEq.beq`; intercepted pre-`whnf` so the derived
      -- `decEq` matchers never surface)
      let args := e.getAppArgs
      if args.size < 2 then return none
      else
        let sa ← symVal memo dedup cells grid args[args.size - 2]! (fuel - 1)
        let sb ← symVal memo dedup cells grid args[args.size - 1]! (fuel - 1)
        match sa, sb with
        | some x, some y =>
          let ty ← whnf (← inferType args[args.size - 2]!)
          match ty with
          | .const ``Bool _ =>
            let pa ← svalBool memo dedup cells grid x
            let pb ← svalBool memo dedup cells grid y
            match pa, pb with
            | some u, some v => pure (some (.prop (.not (boolIff u v))))
            | _, _ => pure none
          | .const ``Nat _ =>
            let p ← symEqNat memo dedup cells grid x y fuel
            match p with
            | some q => pure (some (.prop (.not q)))
            | none => pure none
          | _ =>
            let c ← finWidth ty
            match c with
            | some m =>
              let p ← symEqData memo dedup cells grid m x y fuel
              match p with
              | some q => pure (some (.prop (.not q)))
              | none => pure none
            | none => pure none
        | _, _ => pure none
    else if n == ``Nat.beq then
      -- dot-notation `Nat.beq`: same as the `BEq.beq` Nat path
      -- (elaboration produces this head directly for `==` on `Nat`)
      let args := e.getAppArgs
      if args.size < 2 then return none
      else
        let sa ← symVal memo dedup cells grid args[args.size - 2]! (fuel - 1)
        let sb ← symVal memo dedup cells grid args[args.size - 1]! (fuel - 1)
        match sa, sb with
        | some x, some y =>
          let p ← symEqNat memo dedup cells grid x y fuel
          match p with
          | some q => pure (some (.prop q))
          | none => pure none
        | _, _ => pure none
    else if n == ``decide then
      -- `decide P`: bridge Prop constraints into Bool values.
      -- `P` over `Nat` (`length`-style equalities) has no `FProp`
      -- form, so evaluate Nat sides directly instead of going
      -- through `propOrBool` (which cannot express Nat equality).
      let args := e.getAppArgs
      if args.isEmpty then return none
      else
        let p := args[0]!
        match p.getAppFn with
        | .const pn _ =>
          if (pn == ``Eq || pn == ``Ne) && 2 ≤ p.getAppArgs.size then
            let pa := p.getAppArgs
            let a := pa[pa.size - 2]!
            let b := pa[pa.size - 1]!
            let ty ← whnf (← inferType a)
            match ty with
            | .const ``Nat _ =>
              let sa ← symVal memo dedup cells grid a (fuel - 1)
              let sb ← symVal memo dedup cells grid b (fuel - 1)
              match sa, sb with
              | some x, some y =>
                let q ← symEqNat memo dedup cells grid x y fuel
                match q with
                | some r =>
                  pure (some (.prop (if pn == ``Ne then .not r else r)))
                | none => pure none
              | _, _ => pure none
            | _ =>
              let q ← propOrBool memo dedup cells grid p fuel
              match q with
              | some r => pure (some (.prop r))
              | none => pure none
          else
            let q ← propOrBool memo dedup cells grid p fuel
            match q with
            | some r => pure (some (.prop r))
            | none => pure none
        | _ =>
          let q ← propOrBool memo dedup cells grid p fuel
          match q with
          | some r => pure (some (.prop r))
          | none => pure none
    else if n == ``OfNat.ofNat then
      -- numeric literals (`OfNat.ofNat T k inst`, what `mkNatLit`
      -- and elaborated numerals produce): resolve by type instead of
      -- unfolding the projection (which leads astray)
      match asNumeral e with
      | none => unfoldSym memo dedup cells grid e fuel
      | some k =>
        let ty ← whnf (← inferType e)
        match ty with
        | .const ``Nat _ => pure (some (.nat k))
        | _ =>
          match ← finWidth ty with
          | some c =>
            match ← exprToIdx ty e with
            | some v => pure (some (.lit ty c (v % c)))
            | none =>
              -- not a finite value after all (e.g. open): unfold
              unfoldSym memo dedup cells grid e fuel
          | none => unfoldSym memo dedup cells grid e fuel
    else if n == ``List.nil then
      let args := e.getAppArgs
      if args.isEmpty then return none
      else pure (some (.lst args.back! []))
    else if n == ``List.cons then
      let args := e.getAppArgs
      if args.size < 3 then return none
      else
        let elemTy := args[args.size - 3]!
        let sh ← symVal memo dedup cells grid args[args.size - 2]! (fuel - 1)
        let st ← symVal memo dedup cells grid args[args.size - 1]! (fuel - 1)
        match sh, st with
        | some h, some (.lst _ t) => pure (some (.lst elemTy (h :: t)))
        | _, _ =>
          -- tail is symbolic (e.g. an `ite`-list): distribute
          floatApp memo dedup cells grid e.getAppFn args fuel
    else if n == ``Bool.true then pure (some (.blit true))
    else if n == ``Bool.false then pure (some (.blit false))
    else if n == ``HAnd.hAnd || n == ``Bool.and then
      let args := e.getAppArgs
      if args.size < 2 then return none
      else
        let sa ← symVal memo dedup cells grid args[args.size - 2]! (fuel - 1)
        let sb ← symVal memo dedup cells grid args[args.size - 1]! (fuel - 1)
        match sa, sb with
        | some x, some y =>
          let pa ← svalBool memo dedup cells grid x
          let pb ← svalBool memo dedup cells grid y
          match pa, pb with
          | some u, some v => pure (some (.prop (.and [u, v])))
          | _, _ => pure none
        | _, _ => pure none
    else if n == ``HOr.hOr || n == ``Bool.or then
      let args := e.getAppArgs
      if args.size < 2 then return none
      else
        let sa ← symVal memo dedup cells grid args[args.size - 2]! (fuel - 1)
        let sb ← symVal memo dedup cells grid args[args.size - 1]! (fuel - 1)
        match sa, sb with
        | some x, some y =>
          let pa ← svalBool memo dedup cells grid x
          let pb ← svalBool memo dedup cells grid y
          match pa, pb with
          | some u, some v => pure (some (.prop (.or [u, v])))
          | _, _ => pure none
        | _, _ => pure none
    else if n == ``Complement.complement || n == ``Bool.not then
      let args := e.getAppArgs
      match args.back? with
      | none => return none
      | some a =>
        let sa ← symVal memo dedup cells grid a (fuel - 1)
        match sa with
        | none => return none
        | some v =>
          let pa ← svalBool memo dedup cells grid v
          match pa with
          | some p => pure (some (.prop (.not p)))
          | none => pure none
    else if n == ``Nat.succ then
      let args := e.getAppArgs
      match args.back? with
      | none => return none
      | some a =>
        let sa ← symVal memo dedup cells grid a (fuel - 1)
        match sa with
        | some (.nat k) => pure (some (.nat (k + 1)))
        | some (.nite c x y) =>
          let sx ← symValNatSucc memo dedup cells grid x (fuel - 1)
          let sy ← symValNatSucc memo dedup cells grid y (fuel - 1)
          match sx, sy with
          | some u, some v => pure (some (.nite c u v))
          | _, _ => pure none
        | _ => pure none
    else if n == ``Nat.add || n == ``Nat.mul || n == ``Nat.sub ||
        n == ``HAdd.hAdd || n == ``HMul.hMul || n == ``HSub.hSub then
      let args := e.getAppArgs
      if args.size < 2 then return none
      else
        let sa ← symVal memo dedup cells grid args[args.size - 2]! (fuel - 1)
        let sb ← symVal memo dedup cells grid args[args.size - 1]! (fuel - 1)
        match sa, sb with
        | some (.nat x), some (.nat y) =>
          let r := if n == ``Nat.add || n == ``HAdd.hAdd then x + y
            else if n == ``Nat.mul || n == ``HMul.hMul then x * y else x - y
          pure (some (.nat r))
        | _, _ =>
          -- symbolic Nat args: distribute like a stuck head
          floatApp memo dedup cells grid e.getAppFn args fuel
    else if n == ``HAdd.mk || n == ``HMul.mk || n == ``HSub.mk then
      -- class-mk wrapper around the operation (`HAdd.mk f a b`
      -- means `f a b`): strip and re-evaluate. Guarded: instance
      -- unfolding can surface partial/variant layouts, and a
      -- mis-split rebuild would be ill-typed (caught → yield).
      let args := e.getAppArgs
      if args.size < 3 then return none
      else
        let f := args[args.size - 3]!
        let a := args[args.size - 2]!
        let b := args[args.size - 1]!
        let ft ← try pure (← inferType f) catch _ => return none
        match ft with
        | .forallE _ _ _ _ =>
          try
            symVal memo dedup cells grid (mkAppN f #[a, b]) (fuel - 1)
          catch _ => pure none
        | _ => pure none
    else if n == ``Bool.rec then
      -- `Bool.rec motive f t b`: false-case, true-case, scrutinee
      let args := e.getAppArgs
      if args.size < 3 then return none
      else
        symBoolMatch memo dedup cells grid args[args.size - 1]! args[args.size - 3]!
          args[args.size - 2]! fuel
    else if n == ``Bool.casesOn then
      -- `Bool.casesOn motive b f t`: scrutinee, false-case, true-case
      let args := e.getAppArgs
      if args.size < 3 then return none
      else
        symBoolMatch memo dedup cells grid args[args.size - 3]! args[args.size - 2]!
          args[args.size - 1]! fuel
    else
      -- anything else: unfold one layer and retry, else leaves/float
      unfoldSym memo dedup cells grid e fuel
  | _ =>
    unfoldSym memo dedup cells grid e fuel

/-- Distribute a stuck match over a finite inductive scrutinee into
an `ite` cascade (`match v with | cᵢ => bᵢ` becomes nested
`ite (v == litᵢ)`). Applies to compiler matchers (`match_1`),
recursors, and `casesOn` uniformly, never by name: the scrutinee is
the argument whose type is itself a finite inductive, minor premises
follow in constructor order (verified for `Bool.rec`/`Val.rec`
layouts). Lambda-wrapped branches taking `Unit` are applied to `()`;
anything else yields. A wrong order guess cannot cause unsoundness:
the kernel re-verifies the final model, so it can only fail to
close, never prove a falsehood. -/
partial def symInductiveMatch (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) (e : Expr) (fuel : Nat) : MetaM (Option SVal) := do
  if fuel == 0 then return none
  try
    let r ← matchMatchBody memo dedup cells grid e fuel
    pure r
  catch ex =>
    return none

partial def matchMatchBody (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) (e : Expr) (fuel : Nat) : MetaM (Option SVal) := do
  let args := e.getAppArgs
  -- scrutinee: unique arg whose type is a finite inductive
  let mut scri : Option (Nat × Expr × Nat) := none
  for i in List.range args.size do
    let a := args[i]!
    if a.isApp || a.isFVar || a.isConst then
      let ty ← whnf (← inferType a)
      match ty.getAppFn with
      | .const _ _ =>
        let c ← finWidth ty
        match c with
        | some n =>
          if 1 < n then
            match scri with
            | none => scri := some (i, ty, n)
            | some _ => return none
        | none => pure ()
      | _ => pure ()
  match scri with
  | none =>
    return none
  | some (si, sty, card) =>
    -- minors: value args in listed order (types, props, and
    -- sort-valued motives skipped)
    let mut minors : Array Expr := #[]
    for i in List.range args.size do
      if i == si then continue
      else
        let a := args[i]!
        if (← inferType a).isSort then continue
        else if (← isProp a) then continue
        else
          let aty ← whnf (← inferType a)
          match aty with
          | .forallE _ _ _ _ =>
            -- motive or wrapped branch: keep only data-valued
            -- single-binder pis (motive codomains are sorts)
            let keep ← forallTelescope aty fun xs b => do
              if xs.size != 1 then pure false
              else
                let bt ← whnf b
                pure (!bt.isSort)
            if keep then minors := minors.push a
            else continue
          | _ => minors := minors.push a
    if minors.size != card then
      return none
    let sv ← symVal memo dedup cells grid args[si]! (fuel - 1)
    match sv with
    | none =>
      return none
    | some s =>
      -- a Bool-valued scrutinee is already a constraint (e.g. an
      -- `any`-chain): no per-constructor cascade needed, just split
      -- the two branches (listed order assumed source order)
      let pb ← svalBool memo dedup cells grid s
      match pb with
      | some p =>
        if card != 2 || minors.size != 2 then
          return none
        else
          let b0 ← applyUnit minors[0]!
          let b1 ← applyUnit minors[1]!
          match b0, b1 with
          | some e0, some e1 =>
            let st ← symVal memo dedup cells grid e0 (fuel - 1)
            let sf ← symVal memo dedup cells grid e1 (fuel - 1)
            match st, sf with
            | some a, some b => pure (some (mkIte p a b))
            | _, _ =>
              return none
          | _, _ =>
            return none
      | none =>
        symInductiveCascade memo dedup cells grid sty card minors s fuel

/-- Per-constructor cascade for `symInductiveMatch` (scrutinee is
data, not a Bool constraint): nested `ite (v == litᵢ)`. -/
partial def symInductiveCascade (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) (sty : Expr) (card : Nat) (minors : Array Expr)
    (s : SVal) (fuel : Nat) : MetaM (Option SVal) := do
      -- fold from the last constructor down, applying `Unit`
      -- wrappers as needed
      let blast ← applyUnit minors[card - 1]!
      match blast with
      | none =>
        return none
      | some blastE =>
      let last ← symVal memo dedup cells grid blastE (fuel - 1)
      match last with
      | none =>
        return none
      | some acc =>
        let mut cur := acc
        for j in (List.range (card - 1)).reverse do
          let bj ← applyUnit minors[j]!
          match bj with
          | none =>
            return none
          | some bjE =>
          let sb ← symVal memo dedup cells grid bjE (fuel - 1)
          match sb with
          | none =>
            return none
          | some b =>
            let c ← symEqData memo dedup cells grid card s (.lit sty card j) fuel
            match c with
            | none =>
              return none
            | some g => cur := mkIte g b cur
        pure (some cur)

/-- Apply a `Unit`-wrapped branch (`fun _ : Unit => body`); anything
else yields (proof-taking branches cannot be supplied). -/
partial def applyUnit (b : Expr) : MetaM (Option Expr) := do
  if !b.isLambda then return some b
  else
    -- open the lambda *term* itself (not its pi type) and check the
    -- single binder domain
    lambdaTelescope b fun xs body => do
      if xs.size != 1 then
        return none
      else
        let dt ← whnf (← inferType xs[0]!)
        match dt with
        | .const ``Unit _ => pure (some (mkApp b (mkConst ``Unit.unit)))
        | .const ``PUnit _ => pure (some (mkApp b (mkConst ``PUnit.unit)))
        | _ =>
          pure none

partial def unfoldSym (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) (e : Expr) (fuel : Nat) : MetaM (Option SVal) := do
  -- NOTE: deliberately *not* `whnf` here: `whnf` greedily reduces
  -- through interception points (`==`/`decide`/`ite` become compiler
  -- matchers in one step). Beta first, then a single delta layer so
  -- the main match can intercept sacred heads one at a time.
  let eb ← Core.betaReduce e
  if eb != e then symVal memo dedup cells grid eb (fuel - 1)
  else
    match e.getAppFn with
    | .const h _ =>
      let n := h.toString
      if (n.splitOn "match_").length != 1 || n.endsWith ".rec" ||
          n.endsWith "casesOn" then
        -- recursor/matcher with symbolic scrutinee (the iota case
        -- already reduced): finite-inductive matches distribute via
        -- `symInductiveMatch`, everything else yields here
        match ← symInductiveMatch memo dedup cells grid e fuel with
        | some v => pure (some v)
        | none =>
          let cl ← closedLeaf memo dedup cells grid e
          match cl with
          | some v => pure (some v)
          | none =>
            floatApp memo dedup cells grid e.getAppFn (e.getAppArgs) fuel
      else
        match ← unfoldDefinition? e with
        | some e1 => symVal memo dedup cells grid e1 (fuel - 1)
        | none =>
          let cl ← closedLeaf memo dedup cells grid e
          match cl with
          | some v => pure (some v)
          | none =>
            floatApp memo dedup cells grid e.getAppFn (e.getAppArgs) fuel
    | _ =>
      let cl ← closedLeaf memo dedup cells grid e
      match cl with
      | some v => pure (some v)
      | none =>
        floatApp memo dedup cells grid e.getAppFn (e.getAppArgs) fuel

/-- `Nat.succ` pushed through one symbolic level (maps `Nat.succ`
over `nite` branches without rebuilding terms). -/
partial def symValNatSucc (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) : SVal → Nat → MetaM (Option SVal)
  | .nat k, _ => pure (some (.nat (k + 1)))
  | .nite c x y, fuel => do
    let sx ← symValNatSucc memo dedup cells grid x fuel
    let sy ← symValNatSucc memo dedup cells grid y fuel
    match sx, sy with
    | some u, some v => pure (some (.nite c u v))
    | _, _ => pure none
  | _, _ => pure none

/-- Symbolic `match` on a Bool: closed scrutinee picks a branch,
symbolic suspends as `ite`. `f`/`t` are the false/true branches
(caller passes them in the order of the matched recursor). -/
partial def symBoolMatch (memo : IO.Ref Memo) (dedup : IO.Ref Dedup)
    (cells : IO.Ref (Array (Expr × Option (List Nat))))
    (grid : Expr) (b f t : Expr) (fuel : Nat) : MetaM (Option SVal) := do
  let sb ← symVal memo dedup cells grid b (fuel - 1)
  match sb with
  | none => return none
  | some v =>
    let pb ← svalBool memo dedup cells grid v
    match pb with
    | none => return none
    | some .tru => symVal memo dedup cells grid t (fuel - 1)
    | some .fls => symVal memo dedup cells grid f (fuel - 1)
    | some p =>
      let st ← symVal memo dedup cells grid t (fuel - 1)
      let sf ← symVal memo dedup cells grid f (fuel - 1)
      match st, sf with
      | some a, some b => pure (some (mkIte p a b))
      | _, _ => pure none
end

end Lynth.FinSearch.Recognize
