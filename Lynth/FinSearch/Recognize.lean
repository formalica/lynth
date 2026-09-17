import Lean
import Mathlib.Data.Fintype.Card
import Lynth.FinSearch.Syntax

/-!
Translation from Lean synthesis goals to `FProp` constraints.

Recognized shapes (the procedure's constraint language — anything else
fails the translation and the procedure yields, never unsound):
- `Eq`/`Ne` over `Fin n` (literal `n`) or `Bool`,
- `And`/`Or`/`Not`/`True`/`False`, `Iff`, ground `A → B` (classical
  step, consistent with the CDCL-oracle discipline),
- bounded `∀ (i : Fin n)` (literal `n`, capped) unrolled,
- `List.Pairwise R [explicit elements]`,
- `LT.lt`/`LE.le` over `Fin n`.

Terms: literals, free finite variables (own cells), and cell
references `g c₁ … cₖ` (head applied to literals only). Cardinalities
must agree everywhere; mismatch fails the translation.
-/
namespace Lynth.FinSearch.Recognize

open Lean Meta
open Lynth.FinSearch

/-- Cardinality of a finite type: `Fin n` → `n`, `Bool` → 2. -/
def finWidth (ty : Expr) : MetaM (Option Nat) := do
  let ty ← whnfR ty
  match ty with
  | .app (.const ``Fin _) w =>
    let w ← whnfR w
    match w with
    | .lit (.natVal n) => pure (some n)
    | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ =>
      pure (some n)
    | _ => pure none
  | .const ``Bool _ => pure (some 2)
  | _ => pure none

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
      let argVals := args.toList.map finVal?
      if argVals.all (·.isSome) then
        let i ← cellId cells e (some (argVals.filterMap id))
        return some (.var c i)
      else return none
    else
      let ty ← inferType e
      match ← finWidth ty with
      | some w =>
        if w != c then pure none
        -- boolean connectives are never opaque cells (they belong to
        -- `boolProp`; celling them would disconnect shared atoms)
        else match e.getAppFn with
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

/-- `Fin` literal `(i : Fin n)` with kernel-checked bound proof. -/
def finLit (n i : Nat) : MetaM Expr := do
  let hlt ← mkAppM ``LT.lt #[mkNatLit i, mkNatLit n]
  let pf ← mkDecideProof hlt
  mkAppM ``Fin.mk #[mkNatLit i, pf]

/-- Closed-literal folding for comparisons (modular values). -/
def foldLitCmp (a b : Expr) (c : Nat) (f : Nat → Nat → Bool) :
    MetaM (Option FProp) := do
  match finVal? a, finVal? b with
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
                    let isBool ← whnfR dom >>= fun t =>
                      pure (t.isConstOf ``Bool)
                    let mut props : List FProp := []
                    if isBool then
                      for v in [true, false] do
                        let arg : Expr := match v with
                          | true => mkConst ``Bool.true
                          | false => mkConst ``Bool.false
                        match ← propOrBool cells grid (mkApp pred arg)
                            (depth - 1) with
                        | some p => props := props ++ [p]
                        | none => return none
                    else
                      for i in List.range nn do
                        let arg ← finLit nn i
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
    -- bounded universal: unroll to a conjunction (`Fin n` with `Fin`
    -- literals, `Bool` with both values)
    match ← finWidth d with
    | some n =>
      if 16 < n then return none
      else
        let isBool ← whnfR d >>= fun t => pure (t.isConstOf ``Bool)
        let mut conj : List FProp := []
        if isBool then
          for v in [true, false] do
            let arg : Expr := match v with
              | true => mkConst ``Bool.true
              | false => mkConst ``Bool.false
            let inst ← instantiateForall eR #[arg]
            match ← propOrBool cells grid inst (depth - 1) with
            | some p => conj := conj ++ [p]
            | none => return none
        else
          for i in List.range n do
            let arg ← finLit n i
            let inst ← instantiateForall eR #[arg]
            match ← propOrBool cells grid inst (depth - 1) with
            | some p => conj := conj ++ [p]
            | none => return none
        return some (.and conj)
    | none =>
      -- nondependent implication over closed body: `¬A ∨ B`
      if b.hasLooseBVars then return none
      else
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
