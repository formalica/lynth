-- Finite-domain pilot: finite algebraic model (group of order 3).
-- Witness is an operation TABLE `op : Fin 3 → Fin 3 → Fin 3` plus a unit
-- element `e`, checked by UNIVERSAL equational axioms: associativity
-- and identity laws (∀ over `Fin 3` = finite conjunctions for SAT).
-- Unlike the other pilots, there are no example lists and no ≠/order
-- constraints — the spec is pure equations.
-- NOTE: `lynth` should infer finiteness: 3^(3*3) = 19683 tables × 3
-- choices of unit — brute-force enumeration applies.
-- TODO: failing until table-with-axioms synthesis lands in the pipeline.
import Lynth

/-- Associativity + identity laws over `Fin 3`. -/
def groupValid (op : Fin 3 → Fin 3 → Fin 3) (e : Fin 3) : Prop :=
  (∀ a b c : Fin 3, op (op a b) c = op a (op b c)) ∧
  (∀ a : Fin 3, op e a = a ∧ op a e = a)

/-- All elements, for computable checks. -/
def elems : List (Fin 3) := [0, 1, 2]

/-- Computable validity check (mirrors `groupValid`). -/
def groupValidCheck (op : Fin 3 → Fin 3 → Fin 3) (e : Fin 3) : Bool :=
  (elems.all fun a => elems.all fun b => elems.all fun c =>
    op (op a b) c == op a (op b c)) &&
  (elems.all fun a => (op e a == a) && (op a e == a))

/-- The goal `lynth` must fill: operation table + unit element. -/
def groupSol : { oe : (Fin 3 → Fin 3 → Fin 3) × Fin 3 // groupValid oe.1 oe.2 } := by
  lynth

/-- Addition mod 3. -/
def add3 (a b : Fin 3) : Fin 3 := ⟨(a.val + b.val) % 3, by omega⟩

/-- Etalon: addition mod 3 with unit 0. -/
def etalon : (Fin 3 → Fin 3 → Fin 3) × Fin 3 := (add3, 0)

-- The value computed by `lynth`:
#eval (groupSol : (Fin 3 → Fin 3 → Fin 3) × Fin 3)

-- The etalon checks out:
#eval groupValidCheck etalon.1 etalon.2

-- Runtime check: witness satisfies the axioms.
#guard groupValidCheck (groupSol : (Fin 3 → Fin 3 → Fin 3) × Fin 3).1 (groupSol : (Fin 3 → Fin 3 → Fin 3) × Fin 3).2

/-- info: 'groupSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms groupSol
