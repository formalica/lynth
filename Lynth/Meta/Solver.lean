/-!
Generic enumeration solver: total solver-functions from finite
candidate lists plus decidable checks.

No puzzle-specific content: `I` (input), `O` (output), `P` (validity)
are all parameters. Every meta solver-function (`Graph → Option
Coloring`, `PartialBoard → Option Board`, tours, Lights Out, …) is a
special case by instantiation — the construction and the three
correctness lemmas below are proved once with core axioms only.

- `enumSolve`: first candidate passing `check`, if any.
- Soundness / completeness / none-iff: from `check`-correctness plus
  enumeration-completeness (`Fintype.complete` at use sites).
-/
namespace Lynth.Meta.Solver

/-- First candidate passing the Boolean check, if any. -/
def enumSolve (elems : List O) (check : I → O → Bool) (input : I) :
    Option O :=
  elems.find? fun out => check input out

/-- Soundness: a returned candidate passed the check. -/
theorem enumSolve_sound (elems : List O) (check : I → O → Bool)
    (input : I) (out : O)
    (h : enumSolve elems check input = some out) :
    check input out = true := by
  unfold enumSolve at h
  exact (List.find?_eq_some_iff_append.mp h).1

/-- Membership: a returned candidate came from the list. -/
theorem enumSolve_mem (elems : List O) (check : I → O → Bool)
    (input : I) (out : O)
    (h : enumSolve elems check input = some out) :
    out ∈ elems :=
  List.mem_of_find?_eq_some h

/-- Completeness: when some list member passes, search succeeds. -/
theorem enumSolve_complete (elems : List O) (check : I → O → Bool)
    (input : I) (out : O) (hmem : out ∈ elems)
    (hpass : check input out = true) :
    ∃ out', enumSolve elems check input = some out' := by
  unfold enumSolve
  match hm : elems.find? (fun out => check input out) with
  | some _ => exact ⟨_, rfl⟩
  | none =>
    have hall := List.find?_eq_none.mp hm
    exact absurd hpass (hall out hmem)

/-- None-iff: search fails exactly when no list member passes. -/
theorem enumSolve_none_iff (elems : List O) (check : I → O → Bool)
    (input : I) :
    enumSolve elems check input = none ↔
    ∀ out ∈ elems, check input out = false := by
  constructor
  · intro h out hmem
    have hall := List.find?_eq_none.mp h
    have hnt := hall out hmem
    simpa using hnt
  · intro h
    match hm : elems.find? (fun out => check input out) with
    | some o =>
      have hmem := List.mem_of_find?_eq_some hm
      have hpass := (List.find?_eq_some_iff_append.mp hm).1
      have hfalse := h o hmem
      simp [hfalse] at hpass
    | none =>
      unfold enumSolve
      exact hm

end Lynth.Meta.Solver
