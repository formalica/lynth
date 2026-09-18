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
def cmpBin (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
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
def cmpSide (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (a b : Expr) (mk : FTerm → FTerm → FProp)
    (fold : Nat → Nat → Bool) : MetaM (Option FProp) := do
  match (← sideCard a), (← sideCard b) with
  | some c1, some c2 =>
    if c1 != c2 then pure none
    else cmpBin cells grid a b c1 mk fold
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

mutual
/-- Boolean formula over `Bool`-typed terms to `FProp`
(`b` means `b = true`). -/
partial def boolProp (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
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
      match (← boolProp cells grid args[args.size - 2]! (depth - 1)),
          (← boolProp cells grid args[args.size - 1]! (depth - 1)) with
      | some pa, some pb => pure (some (.and [pa, pb]))
      | _, _ => pure none
    else if (n == ``HOr.hOr || n == ``Bool.or) && 2 ≤ args.size then
      match (← boolProp cells grid args[args.size - 2]! (depth - 1)),
          (← boolProp cells grid args[args.size - 1]! (depth - 1)) with
      | some pa, some pb => pure (some (.or [pa, pb]))
      | _, _ => pure none
    else if (n == ``Complement.complement || n == ``Bool.not) &&
        1 ≤ args.size then
      match ← boolProp cells grid args[args.size - 1]! (depth - 1) with
      | some pa => pure (some (.not pa))
      | none => pure none
    else
      -- atom/constant equation against `true`
      match ← recognizeTerm cells grid e 2 with
      | some t => pure (some (.eq t (.lit 2 1)))
      | none =>
        -- user boolean helper: unfold one layer and retry
        let eU ← whnf e
        if eU == e then pure none
        else boolProp cells grid eU (depth - 1)
  | _ =>
    match ← recognizeTerm cells grid e 2 with
    | some t => pure (some (.eq t (.lit 2 1)))
    | none =>
      let eU ← whnf e
      if eU == e then pure none
      else boolProp cells grid eU (depth - 1)


/-- A proposition or a `Bool`-typed formula to `FProp`. -/
partial def propOrBool (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (e : Expr) (depth : Nat) : MetaM (Option FProp) := do
  let et ← inferType e
  let ty ← whnfR et
  match ty with
  | .sort _ => recognizeProp cells grid e depth
  | .const ``Bool _ => boolProp cells grid e depth
  | _ => pure none













/-- Boolean combinations via `boolProp` (`a = b` ⟺ `a ↔ b`,
`a ≠ b` ⟺ xor, `a < b` ⟺ `¬a ∧ b`, `a ≤ b` ⟺ `¬a ∨ b`). -/
partial def boolCmp (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (a b : Expr) (mk : FProp → FProp → FProp) (depth : Nat) :
    MetaM (Option FProp) := do
  match (← boolProp cells grid a (depth - 1)),
      (← boolProp cells grid b (depth - 1)) with
  | some pa, some pb => pure (some (mk pa pb))
  | _, _ => pure none

/-- Dispatch a comparison: `Bool`-typed sides go through `boolProp`
(structural); anything else through cell equations. -/
partial def cmpDispatch (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (a b : Expr) (mk : FTerm → FTerm → FProp) (fold : Nat → Nat → Bool)
    (bmk : FProp → FProp → FProp) (depth : Nat) : MetaM (Option FProp) := do
  if (← isBoolTy a) || (← isBoolTy b) then
    boolCmp cells grid a b bmk depth
  else
    cmpSide cells grid a b mk fold

/-- One orientation of the counting constraint: `cardE` must be a
`Fintype.card` over a subtype, `litE` a numeral. -/
partial def cardSide (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
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
                      match ← propOrBool cells grid (mkApp pred arg)
                          (depth - 1) with
                      | some p => props := props ++ [p]
                      | none => return none
                    pure (some (.exactK props k))
    | _ => pure none

/-- Counting constraint `Fintype.card { j // P j } = k` (either side)
over a finite index type: unroll the predicate per value and emit
`exactK` (capped: the encoder's subset blowup). `none` = not a
counting shape (caller falls back to equation handling). -/
partial def countCard (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (a b : Expr) (depth : Nat) : MetaM (Option FProp) := do
  match ← cardSide cells grid a b depth with
  | some p => pure (some p)
  | none => cardSide cells grid b a depth

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
partial def recognizeProp (cells : IO.Ref (Array (Expr × Option (List Nat)))) (grid : Expr)
    (e : Expr) (depth : Nat := 64) : MetaM (Option FProp) := do
  if depth == 0 then return none
  -- `Ne` first on the raw form: it is reducible (`Ne a b ≡ ¬(a = b)`),
  -- so `whnfR` would hide it (the `Not` arm below covers that case too,
  -- equivalently — this is just the direct path).
  match e.getAppFn with
  | .const n _ =>
    let args := e.getAppArgs
    if n == ``Ne && 2 ≤ args.size then
      return ← cmpDispatch cells grid args[args.size - 2]! args[args.size - 1]!
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
          match ← propOrBool cells grid inst (depth - 1) with
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
          match ← propOrBool cells grid b (depth - 1) with
          | some pb => return some pb
          | none => return none
        | _ =>
          match (← propOrBool cells grid d (depth - 1)),
              (← propOrBool cells grid b (depth - 1)) with
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
        match (← propOrBool cells grid a (depth - 1)),
            (← propOrBool cells grid b (depth - 1)) with
        | some pa, some pb => pure (some (.and [pa, pb]))
        | _, _ => pure none
      | none => pure none
    else if n == ``Or then
      match last2 with
      | some (a, b) =>
        match (← propOrBool cells grid a (depth - 1)),
            (← propOrBool cells grid b (depth - 1)) with
        | some pa, some pb => pure (some (.or [pa, pb]))
        | _, _ => pure none
      | none => pure none
    else if n == ``Not then
      match args.back? with
      | some a =>
        match ← propOrBool cells grid a (depth - 1) with
        | some pa => pure (some (.not pa))
        | none => pure none
      | none => pure none
    else if n == ``Eq then
      match last2 with
      | some (a, b) =>
        -- counting form first (`Fintype.card {j // P j} = k`);
        -- plain finite equations after
        match ← countCard cells grid a b depth with
        | some p => pure (some p)
        | none => cmpDispatch cells grid a b .eq (· == ·) boolIff depth
      | none => pure none
    else if n == ``Ne then
      match last2 with
      | some (a, b) => cmpDispatch cells grid a b .ne (· != ·) boolXor depth
      | none => pure none
    else if n == ``LT.lt then
      match last2 with
      | some (a, b) => cmpDispatch cells grid a b .lt (· < ·) boolLt depth
      | none => pure none
    else if n == ``LE.le then
      match last2 with
      | some (a, b) => cmpDispatch cells grid a b .le (· ≤ ·) boolLe depth
      | none => pure none
    else if n == ``Iff then
      match last2 with
      | some (a, b) =>
        match (← propOrBool cells grid a (depth - 1)),
            (← propOrBool cells grid b (depth - 1)) with
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
                  match ← propOrBool cells grid app (depth - 1) with
                  | some p => conj := conj ++ [p]
                  | none => return none
                else pure ()
            pure (some (.and conj))
    else
      -- unknown head: unfold one layer (user definitions) and retry
      let eU ← whnf e
      if eU == eR then pure none
      else recognizeProp cells grid eU (depth - 1)
  | _ =>
    let eU ← whnf e
    if eU == eR then pure none
    else recognizeProp cells grid eU (depth - 1)
end

end Lynth.FinSearch.Recognize
