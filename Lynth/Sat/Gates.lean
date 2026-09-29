import Lynth.Sat.Solver
import Mathlib

/-!
Verified gate library: pure CNF combinators with correctness lemmas.

Every gate is a plain function producing clauses, paired with a lemma
stated uniformly in `checkSat` language (`checkSat gate a = true → …`),
so a future spec compiler assembles gates and composes the lemmas by
rewriting — no search, no rechecking. The bridge lemmas below connect
`checkSat` to the option-valued `evalLit` once; gate proofs then run
on clean propositional structure. All lemmas are proven structurally
(core axioms only); nothing here touches the solver, its axioms, or
any puzzle-specific encoding.
-/
namespace Lynth.Sat.Gates

open Lynth.Sat

/-- Single-literal check unfolds to literal evaluation. -/
theorem checkSat_single (a : Assignment) (l : Lit) :
    checkSat [[l]] a = true ↔ evalLit a l = some true := by
  unfold checkSat evalLit lookup
  grind

/-- Literal negation commutes with evaluation. -/
theorem evalLit_neg (a : Assignment) (l : Lit) :
    evalLit a (-l) = (evalLit a l).map (!·) := by
  unfold evalLit varOf lookup
  simp only [Int.natAbs_neg]
  match ha : (if _h : 0 < varOf l ∧ varOf l ≤ a.length then a[varOf l - 1] else none) with
  | none => simp_all
  | some b =>
    rcases lt_trichotomy l 0 with hneg | rfl | hpos
    · have c2 : ¬ ((0 : Lit) < l) := not_lt.mpr (le_of_lt hneg)
      simp [c2]; try exact hneg
    · simp [varOf] at ha
    · have hle : (0 : Lit) ≤ l := hpos.le
      simp [hpos, hle]

/-- `checkSat` splits over concatenated CNFs. -/
theorem checkSat_append (a : Assignment) (c1 c2 : CNF) :
    checkSat (c1 ++ c2) a = (checkSat c1 a && checkSat c2 a) := by
  unfold checkSat
  simp only [List.all_append]

/-- Head clause of a satisfied CNF is satisfied. -/
theorem checkSat_cons (a : Assignment) (c : Clause) (cs : CNF)
    (h : checkSat (c :: cs) a = true) : checkSat [c] a = true := by
  have h3 := checkSat_append a [c] cs
  rw [List.singleton_append] at h3
  rw [h3] at h
  exact (Bool.and_eq_true_iff.mp h).1

/-- Tail of a satisfied CNF is satisfied. -/
theorem checkSat_cons_tail (a : Assignment) (c : Clause) (cs : CNF)
    (h : checkSat (c :: cs) a = true) : checkSat cs a = true := by
  have h3 := checkSat_append a [c] cs
  rw [List.singleton_append] at h3
  rw [h3] at h
  exact (Bool.and_eq_true_iff.mp h).2

/-- Any member clause of a satisfied CNF is satisfied. -/
theorem checkSat_mem (a : Assignment) (cnf : CNF) (c : Clause)
    (hm : c ∈ cnf) (h : checkSat cnf a = true) :
    checkSat [c] a = true := by
  induction cnf with
  | nil => simp only [List.not_mem_nil] at hm
  | cons d ds ih =>
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact checkSat_cons _ _ _ h
    · exact ih hm (checkSat_cons_tail a d ds h)

/-- A CNF holds when every singleton does (clause aggregation). -/
theorem checkSat_of_all_single (a : Assignment) (cs : CNF)
    (h : ∀ c ∈ cs, checkSat [c] a = true) : checkSat cs a = true := by
  induction cs with
  | nil => simp [checkSat]
  | cons c cs ih =>
    have h1 := h c List.mem_cons_self
    have h2 := ih (fun c' hm => h c' (List.mem_cons.mpr (Or.inr hm)))
    have h3 := checkSat_append a [c] cs
    rw [List.singleton_append] at h3
    rw [h3]
    simp [h1, h2]

/-- A flatMapped CNF holds when every piece does (generic lifter for
cell/edge-iterated encodings — no problem-specific content). -/
theorem checkSat_flatMap (a : Assignment) (l : List α) (f : α → CNF)
    (h : ∀ x ∈ l, checkSat (f x) a = true) :
    checkSat (l.flatMap f) a = true := by
  apply checkSat_of_all_single
  intro c hc
  obtain ⟨x, hx, hmem⟩ := List.mem_flatMap.mp hc
  exact checkSat_mem a _ _ hmem (h x hx)

/-- Conditional clauses: emit `cls` iff the (possibly stuck) Boolean
`b` holds. Lets encodings branch on input data without evaluating
it; proofs case-split on `b` instead. -/
def condClauses (b : Bool) (cls : CNF) : CNF :=
  if b then cls else []

/-- Conditional emission, positive direction. -/
theorem condClauses_of_true (a : Assignment) (b : Bool) (cls : CNF)
    (hb : b = true) (h : checkSat cls a = true) :
    checkSat (condClauses b cls) a = true := by
  change checkSat (if b then cls else []) a = true
  rw [hb]
  exact h

/-- Conditional emission, elimination direction. -/
theorem condClauses_elim (a : Assignment) (b : Bool) (cls : CNF)
    (h : checkSat (condClauses b cls) a = true) (hb : b = true) :
    checkSat cls a = true := by
  change checkSat (if b then cls else []) a = true at h
  rw [hb] at h
  exact h


/-- Sub-CNF extraction: a held flatMap's every piece holds.
Generic splitter for all compiled encodings. -/
theorem checkSat_piece (m : Assignment) (l : List α) (f : α → CNF)
    (x : α) (hx : x ∈ l)
    (h : checkSat (l.flatMap f) m = true) :
    checkSat (f x) m = true := by
  apply checkSat_of_all_single
  intro cl hc
  exact checkSat_mem m _ _
    (List.mem_flatMap.mpr ⟨x, hx, hc⟩) h

/-- Append combination: held parts make a held whole. -/
theorem appendHeld (a b : CNF) (m : Assignment)
    (h1 : checkSat a m = true) (h2 : checkSat b m = true) :
    checkSat (a ++ b) m = true := by
  have h3 := checkSat_append m a b
  rw [h3]
  simp [h1, h2]

/-- Append splitting: a held whole makes held parts. -/
theorem checkSat_appendHeld (a b : CNF) (m : Assignment)
    (h : checkSat (a ++ b) m = true) :
    checkSat a m = true ∧ checkSat b m = true := by
  have h3 := checkSat_append m a b
  rw [h3] at h
  exact (Bool.and_eq_true_iff.mp h)
theorem checkSat_condFlatMap (m : Assignment) (l : List α)
    (f : α → CNF) (g : α → Bool) (x : α)
    (hx : x ∈ l) (hgx : g x = true)
    (h : checkSat (l.flatMap fun a => condClauses (g a) (f a)) m = true) :
    checkSat (f x) m = true := by
  apply checkSat_of_all_single
  intro cl hc
  have hmem : cl ∈ l.flatMap fun a => condClauses (g a) (f a) := by
    apply List.mem_flatMap.mpr
    refine ⟨x, hx, ?_⟩
    have heq : condClauses (g x) (f x) = f x := by
      simp [condClauses, hgx]
    rw [heq]
    exact hc
  exact checkSat_mem m _ _ hmem h

/-- At-least-one clause over literals. -/
def atLeastOneCNF (lits : List Lit) : CNF := [lits]

/-- At-least-one converse: a true member satisfies the clause. -/
theorem atLeastOne_of_true (a : Assignment) (lits : List Lit) (l : Lit)
    (hm : l ∈ lits) (ht : evalLit a l = some true) :
    checkSat (atLeastOneCNF lits) a = true := by
  unfold atLeastOneCNF checkSat
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [List.any_eq_true]
  refine ⟨l, hm, ?_⟩
  unfold evalLit lookup at ht
  grind

/-- At-least-one correctness: a satisfied clause has a true member. -/
theorem atLeastOne_correct (a : Assignment) (lits : List Lit)
    (h : checkSat (atLeastOneCNF lits) a = true) :
    ∃ l ∈ lits, evalLit a l = some true := by
  unfold atLeastOneCNF checkSat at h
  simp only [List.all_cons, List.all_nil, Bool.and_true] at h
  rw [List.any_eq_true] at h
  obtain ⟨l, hm, ht⟩ := h
  exact ⟨l, hm, by unfold evalLit lookup; grind⟩

/-- At-most-one clauses (pairwise mutual exclusion) over literals. -/
def atMostOneCNF : List Lit → CNF
  | [] => []
  | x :: xs => (xs.map fun y => [negLit x, negLit y]) ++ atMostOneCNF xs

/-- At-most-one membership: every clause is a negated distinct pair
(needs `Nodup`: otherwise `[¬x, ¬x]` pairs could occur). -/
theorem mem_atMostOne (lits : List Lit) (nd : lits.Nodup) (c : Clause)
    (h : c ∈ atMostOneCNF lits) :
    ∃ x y, x ∈ lits ∧ y ∈ lits ∧ x ≠ y ∧ c = [negLit x, negLit y] := by
  revert h
  induction lits with
  | nil =>
    intro h
    simp [atMostOneCNF] at h
  | cons x xs ih =>
    intro h
    have ndx : x ∉ xs ∧ xs.Nodup := List.nodup_cons.mp nd
    simp only [atMostOneCNF] at h
    have h3 := List.mem_append.mp h
    rcases h3 with hm | ht
    · obtain ⟨y, hym, hfc⟩ := List.mem_map.mp hm
      subst hfc
      refine ⟨x, y, List.mem_cons_self,
        List.mem_cons.mpr (Or.inr hym), ?_, rfl⟩
      intro hcon
      subst hcon
      exact ndx.1 hym
    · obtain ⟨a, b, ha, hb, hne, hcc⟩ := ih ndx.2 ht
      exact ⟨a, b, List.mem_cons.mpr (Or.inr ha),
        List.mem_cons.mpr (Or.inr hb), hne, hcc⟩


/-- Pairwise disjunction evaluates: a holding 2-clause has a true side. -/
theorem checkSat_pair_eval (a : Assignment) (x y : Lit)
    (h : checkSat [[x, y]] a = true) :
    evalLit a x = some true ∨ evalLit a y = some true := by
  have h1 : checkSat (atLeastOneCNF [x, y]) a = true := h
  obtain ⟨l, hm, ht⟩ := atLeastOne_correct a [x, y] h1
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl
  · exact Or.inl ht
  · exact Or.inr ht

/-- Converse: a true side satisfies the 2-clause (generic lifter for
completeness directions — proved once via the same unfolding as
`checkSat_single`, so callers never re-prove array reasoning). -/
theorem checkSat_pair_of_true_left (a : Assignment) (x y : Lit)
    (h : evalLit a x = some true) : checkSat [[x, y]] a = true := by
  unfold checkSat evalLit lookup at *
  grind

/-- Converse, right side. -/
theorem checkSat_pair_of_true_right (a : Assignment) (x y : Lit)
    (h : evalLit a y = some true) : checkSat [[x, y]] a = true := by
  unfold checkSat evalLit lookup at *
  grind

/-- Pairwise exclusion helper: a holding `[¬u, ¬v]` clause plus
`u` true forces `v` false. Stated with `-` (callers' `negLit`
applications are definitionally equal, so no unfolding is needed). -/
theorem pairFalse (a : Assignment) (u v : Lit)
    (hc : checkSat [[-u, -v]] a = true)
    (hu : evalLit a u = some true) : evalLit a v = some false := by
  have hdisj := checkSat_pair_eval a (-u) (-v) hc
  rcases hdisj with hnu | hnv
  · rw [evalLit_neg, hu] at hnu
    simp at hnu
  · rw [evalLit_neg] at hnv
    cases hev : evalLit a v with
    | none => simp [hev] at hnv
    | some b =>
      simp only [hev, Option.map_some] at hnv
      cases b <;> simp_all

/-- Two-literal clauses are order-insensitive. -/
theorem checkSat_pair_swap (a : Assignment) (x y : Lit) :
    checkSat [[x, y]] a = checkSat [[y, x]] a := by
  unfold checkSat
  simp only [List.all_cons, List.all_nil, Bool.and_true,
    List.any_cons, List.any_nil, Bool.or_false]
  exact Bool.or_comm _ _

/-- At-most-one correctness: no two distinct members are true. -/
theorem atMostOne_correct (a : Assignment) (lits : List Lit)
    (h : checkSat (atMostOneCNF lits) a = true) :
    ∀ x ∈ lits, ∀ y ∈ lits, x ≠ y →
      evalLit a x = some true → evalLit a y = some false := by
  revert h
  induction lits with
  | nil =>
    intro h x hx
    simp at hx
  | cons x xs ih =>
    intro h y hy z hz hne hty
    simp only [atMostOneCNF] at h
    have hmap : checkSat (xs.map fun w => [negLit x, negLit w]) a = true := by
      have h3 := checkSat_append a
        (xs.map fun w => [negLit x, negLit w]) (atMostOneCNF xs)
      rw [h3] at h
      exact (Bool.and_eq_true_iff.mp h).1
    have hrest : checkSat (atMostOneCNF xs) a = true := by
      have h3 := checkSat_append a
        (xs.map fun w => [negLit x, negLit w]) (atMostOneCNF xs)
      rw [h3] at h
      exact (Bool.and_eq_true_iff.mp h).2
    simp only [List.mem_cons] at hy hz
    rcases hy with hy | hy
    · -- `y = x`: eliminate `y`, keep the head
      have hys : x = y := hy.symm
      subst hys
      rcases hz with hz | hz
      · have hzs : x = z := hz.symm
        subst hzs
        exact absurd rfl hne
      · exact pairFalse a x z
          (checkSat_mem a _ _ (List.mem_map.mpr ⟨z, hz, rfl⟩) hmap) hty
    · rcases hz with hz | hz
      · -- `z = x`: eliminate `z`, keep the head
        have hzs : x = z := hz.symm
        subst hzs
        have h0 := checkSat_mem a _ _
          (List.mem_map.mpr ⟨y, hy, rfl⟩) hmap
        have hc : checkSat [[negLit y, negLit x]] a = true := by
          rwa [checkSat_pair_swap] at h0
        exact pairFalse a y x hc hty
      · exact ih hrest y hy z hz hne hty

/-- One-hot row: at-least-one plus at-most-one. -/
def oneHotRowCNF (lits : List Lit) : CNF :=
  atLeastOneCNF lits ++ atMostOneCNF lits

/-- One-hot correctness: exactly one member is true. -/
theorem oneHotRow_correct (a : Assignment) (lits : List Lit)
    (h : checkSat (oneHotRowCNF lits) a = true) :
    (∃ w ∈ lits, evalLit a w = some true) ∧
    (∀ x ∈ lits, ∀ y ∈ lits, x ≠ y →
      evalLit a x = some true → evalLit a y = some false) := by
  unfold oneHotRowCNF at h
  have h1 : checkSat (atLeastOneCNF lits) a = true := by
    have h3 := checkSat_append a (atLeastOneCNF lits) (atMostOneCNF lits)
    rw [h3] at h
    exact (Bool.and_eq_true_iff.mp h).1
  have h2 : checkSat (atMostOneCNF lits) a = true := by
    have h3 := checkSat_append a (atLeastOneCNF lits) (atMostOneCNF lits)
    rw [h3] at h
    exact (Bool.and_eq_true_iff.mp h).2
  exact ⟨atLeastOne_correct a lits h1,
    fun x hx y hy hne htx => atMostOne_correct a lits h2 x hx y hy hne htx⟩

/-- N-ary Tseitin AND: `o ↔ ∧ ins`. -/
def andGateCNF (o : Lit) (ins : List Lit) : CNF :=
  (ins.map fun x => [negLit o, x]) ++ [[o] ++ ins.map fun x => negLit x]

/-- AND-gate correctness. -/
theorem andGate_correct (a : Assignment) (o : Lit) (ins : List Lit)
    (h : checkSat (andGateCNF o ins) a = true) :
    (evalLit a o = some true) ↔ (∀ l ∈ ins, evalLit a l = some true) := by
  unfold andGateCNF at h
  have hA : checkSat (ins.map fun x => [negLit o, x]) a = true := by
    have h3 := checkSat_append a
      (ins.map fun x => [negLit o, x]) [[o] ++ ins.map fun x => negLit x]
    rw [h3] at h
    exact (Bool.and_eq_true_iff.mp h).1
  have hB : checkSat [[o] ++ ins.map fun x => negLit x] a = true := by
    have h3 := checkSat_append a
      (ins.map fun x => [negLit o, x]) [[o] ++ ins.map fun x => negLit x]
    rw [h3] at h
    exact (Bool.and_eq_true_iff.mp h).2
  constructor
  · intro ho l hl
    have hc := checkSat_mem a _ _
      (List.mem_map.mpr ⟨l, hl, rfl⟩) hA
    have hdisj := checkSat_pair_eval a (-o) l hc
    rcases hdisj with hno | hl2
    · rw [evalLit_neg, ho] at hno
      simp at hno
    · exact hl2
  · intro hall
    have hdisj := atLeastOne_correct a ([o] ++ ins.map fun x => negLit x) hB
    obtain ⟨l, hm, ht⟩ := hdisj
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hm
    rcases hm with rfl | hm
    · exact ht
    · obtain ⟨x, hx, hfx⟩ := List.mem_map.mp hm
      subst hfx
      -- `ht` is now at `negLit x`; fold to `-x` by defeq
      have ht2 : evalLit a (-x) = some true := ht
      rw [evalLit_neg] at ht2
      have hx2 := hall x hx
      rw [hx2] at ht2
      simp at ht2

/-- N-ary Tseitin OR: `o ↔ ∨ ins`. -/
def orGateCNF (o : Lit) (ins : List Lit) : CNF :=
  (ins.map fun x => [negLit x, o]) ++ [[negLit o] ++ ins]

/-- OR-gate correctness. -/
theorem orGate_correct (a : Assignment) (o : Lit) (ins : List Lit)
    (h : checkSat (orGateCNF o ins) a = true) :
    (evalLit a o = some true) ↔ (∃ l ∈ ins, evalLit a l = some true) := by
  unfold orGateCNF at h
  have hA : checkSat (ins.map fun x => [negLit x, o]) a = true := by
    have h3 := checkSat_append a
      (ins.map fun x => [negLit x, o]) [[negLit o] ++ ins]
    rw [h3] at h
    exact (Bool.and_eq_true_iff.mp h).1
  have hB : checkSat [[negLit o] ++ ins] a = true := by
    have h3 := checkSat_append a
      (ins.map fun x => [negLit x, o]) [[negLit o] ++ ins]
    rw [h3] at h
    exact (Bool.and_eq_true_iff.mp h).2
  constructor
  · intro ho
    have hdisj := atLeastOne_correct a ([negLit o] ++ ins) hB
    obtain ⟨l, hm, ht⟩ := hdisj
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hm
    rcases hm with rfl | hm
    · -- `l = ¬o`: contradicts `o` true
      have ht2 : evalLit a (-o) = some true := ht
      rw [evalLit_neg, ho] at ht2
      simp at ht2
    · exact ⟨l, hm, ht⟩
  · intro hex
    obtain ⟨l, hl, htl⟩ := hex
    have hc := checkSat_mem a _ _
      (List.mem_map.mpr ⟨l, hl, rfl⟩) hA
    have hdisj := checkSat_pair_eval a (-l) o hc
    rcases hdisj with hnl | ho2
    · rw [evalLit_neg, htl] at hnl
      simp at hnl
    · exact ho2

/-- Tseitin NOT: `o ↔ ¬x`. -/
def notGateCNF (o x : Lit) : CNF := [[negLit o, negLit x], [o, x]]

/-- NOT-gate correctness. -/
theorem notGate_correct (a : Assignment) (o x : Lit)
    (h : checkSat (notGateCNF o x) a = true) :
    (evalLit a o = some true) ↔ (evalLit a x = some false) := by
  unfold notGateCNF at h
  have h1 : checkSat [[negLit o, negLit x]] a = true :=
    checkSat_cons a _ _ h
  have h2 : checkSat [[o, x]] a = true := by
    have ht : checkSat ([[negLit o, negLit x]] ++ [[o, x]]) a = true := h
    have h3 := checkSat_append a [[negLit o, negLit x]] [[o, x]]
    rw [h3] at ht
    exact (Bool.and_eq_true_iff.mp ht).2
  constructor
  · intro ho
    have hdisj := checkSat_pair_eval a (-o) (-x) h1
    rcases hdisj with hno | hnx
    · rw [evalLit_neg, ho] at hno
      simp at hno
    · rw [evalLit_neg] at hnx
      cases hev : evalLit a x with
      | none => simp [hev] at hnx
      | some b =>
        simp only [hev, Option.map_some] at hnx
        cases b <;> simp_all
  · intro hxf
    have hdisj := checkSat_pair_eval a o x h2
    rcases hdisj with ho2 | hx2
    · exact ho2
    · rw [hxf] at hx2
      simp at hx2

/-- Pairwise-AND rows with caller-supplied temp (plain def, no
matching — beta-reduces cleanly for membership proofs). -/
def mkAnds (t x y : Lit) : CNF :=
  [[negLit t, x], [negLit t, y], [t, negLit x, negLit y]]

/-- Disjunction-of-conjunctions: `o ↔ ∨ (x ∧ y)` over caller-built
triples. Covers one-hot equality (diagonal triples) and one-hot
ordering (`i<j` triples) with a single lemma. -/
def orOfAndsCNF (o : Lit) (trips : List (Lit × Lit × Lit)) : CNF :=
  (trips.flatMap fun tr => mkAnds tr.1 tr.2.1 tr.2.2) ++
  orGateCNF o (trips.map fun tr => tr.1)

/-- Disjunction-of-conjunctions correctness. -/
theorem orOfAnds_correct (a : Assignment) (o : Lit)
    (trips : List (Lit × Lit × Lit))
    (h : checkSat (orOfAndsCNF o trips) a = true) :
    (evalLit a o = some true) ↔
    (∃ t ∈ trips.map fun tr => tr.1, ∃ x y,
      (t, x, y) ∈ trips ∧ evalLit a x = some true ∧
      evalLit a y = some true) := by
  unfold orOfAndsCNF at h
  have hA : checkSat
      (trips.flatMap fun tr => mkAnds tr.1 tr.2.1 tr.2.2) a = true := by
    have h3 := checkSat_append a
      (trips.flatMap fun tr => mkAnds tr.1 tr.2.1 tr.2.2)
      (orGateCNF o (trips.map fun tr => tr.1))
    rw [h3] at h
    exact (Bool.and_eq_true_iff.mp h).1
  have hO : checkSat (orGateCNF o (trips.map fun tr => tr.1)) a = true := by
    have h3 := checkSat_append a
      (trips.flatMap fun tr => mkAnds tr.1 tr.2.1 tr.2.2)
      (orGateCNF o (trips.map fun tr => tr.1))
    rw [h3] at h
    exact (Bool.and_eq_true_iff.mp h).2
  constructor
  · intro ho
    obtain ⟨t, htm, htt⟩ := (orGate_correct a o _ hO).mp ho
    obtain ⟨tr, htr, hfst⟩ := List.mem_map.mp htm
    obtain ⟨t0, x0, y0⟩ := tr
    -- fold the projections: `t0 = t`, `htt` at `t0`
    have ht0 : t0 = t := hfst
    rw [← ht0] at htt
    -- AND-rows of this trip force the pair true
    have hm1 : [negLit t0, x0] ∈
        [[negLit t0, x0], [negLit t0, y0], [t0, negLit x0, negLit y0]] := by
      simp
    have m1 : [negLit t0, x0] ∈
        trips.flatMap fun tr => mkAnds tr.1 tr.2.1 tr.2.2 :=
      List.mem_flatMap.mpr ⟨(t0, x0, y0), htr, hm1⟩
    have hm2 : [negLit t0, y0] ∈
        [[negLit t0, x0], [negLit t0, y0], [t0, negLit x0, negLit y0]] := by
      simp
    have m2 : [negLit t0, y0] ∈
        trips.flatMap fun tr => mkAnds tr.1 tr.2.1 tr.2.2 :=
      List.mem_flatMap.mpr ⟨(t0, x0, y0), htr, hm2⟩
    have hx0 : evalLit a x0 = some true := by
      have hd := checkSat_pair_eval a (-t0) x0
        (checkSat_mem a _ _ m1 hA)
      rcases hd with hn | hx
      · rw [evalLit_neg, htt] at hn
        simp at hn
      · exact hx
    have hy0 : evalLit a y0 = some true := by
      have hd := checkSat_pair_eval a (-t0) y0
        (checkSat_mem a _ _ m2 hA)
      rcases hd with hn | hy
      · rw [evalLit_neg, htt] at hn
        simp at hn
      · exact hy
    exact ⟨t0, List.mem_map.mpr ⟨(t0, x0, y0), htr, rfl⟩,
      x0, y0, htr, hx0, hy0⟩
  · intro hex
    obtain ⟨t, htm, x, y, hmem, hxt, hyt⟩ := hex
    -- the trip's third row forces `t` true (other rows contradict)
    have hm3 : [t, negLit x, negLit y] ∈
        [[negLit t, x], [negLit t, y], [t, negLit x, negLit y]] := by
      simp
    have m3 : [t, negLit x, negLit y] ∈
        trips.flatMap fun tr => mkAnds tr.1 tr.2.1 tr.2.2 :=
      List.mem_flatMap.mpr ⟨(t, x, y), hmem, hm3⟩
    have hc3 := checkSat_mem a _ _ m3 hA
    have hdisj := atLeastOne_correct a [t, negLit x, negLit y] hc3
    obtain ⟨l, hm, ht⟩ := hdisj
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with h1 | h2 | h3
    · rw [h1] at ht
      have htt : evalLit a t = some true := ht
      exact (orGate_correct a o _ hO).mpr
        ⟨t, List.mem_map.mpr ⟨(t, x, y), hmem, rfl⟩, htt⟩
    · -- `l = ¬x`: contradicts `x` true
      rw [h2] at ht
      have hnx : evalLit a (-x) = some true := ht
      rw [evalLit_neg, hxt] at hnx
      simp at hnx
    · -- `l = ¬y`: contradicts `y` true
      rw [h3] at ht
      have hny : evalLit a (-y) = some true := ht
      rw [evalLit_neg, hyt] at hny
      simp at hny

end Lynth.Sat.Gates
