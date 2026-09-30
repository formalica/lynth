import Mathlib

/-!
# Alternative definitions: `List.attach`

`List.attach l` is the list of *subtype-witnessed* elements: `l.attach : List α →
List { x // x ∈ l }`.  Each element carries a proof that it occurs in `l`, and
this file is where the choice of proof becomes visible.  Three other routes:

* `byOfFnPair` — enumerate the positions as `Fin l.length` and build the witness
  from `List.getElem_mem`;
* `byRangeMap` — the same, but the bound comes from `Fin l.length` while the
  element is read with `List.get`, so the proof is obtained from the index rather
  than from the value;
* `byRec` — structural recursion in which the head's witness is `List.Mem.head`
  and the tail's witnesses are lifted by `List.mem_cons_of_mem`, so no index and
  no `getElem_mem` appears anywhere.

The subtlety is that a `Subtype` is a *pair* of a value and a proof, so two
routes agree only up to proof irrelevance; the equalities below therefore go
through `List.ext` rather than through `rfl`.
-/

namespace Alt.List.attach

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (l : List α) : List { x // x ∈ l } := l.attach

/-- Enumerate the positions as `Fin l.length` and build the witness from
`List.getElem_mem`.  This is the "position first, value and proof derived" shape.
-/
def byOfFnPair (l : List α) : List { x // x ∈ l } :=
  List.ofFn (fun i : Fin l.length => ⟨l.get i, List.getElem_mem (l := l) i.isLt⟩)

/-- The same positions, read with `List.get` rather than `List.ofFn`, so the
witness comes from the index alone and the element is fetched explicitly. -/
def byRangeMap (l : List α) : List { x // x ∈ l } :=
  (List.finRange l.length).map (fun i => ⟨l.get i, List.getElem_mem (l := l) i.isLt⟩)

/-- Structural recursion: the head's witness is `List.Mem.head` and the tail's
witnesses are lifted through `List.mem_cons_of_mem`.  No index, no `getElem_mem`,
and no finite enumeration appears at all. -/
def byRec : (l : List α) → List { x // x ∈ l }
  | [] => []
  | a :: t =>
    ⟨a, List.Mem.head t⟩ ::
      (byRec t).map (fun x : { y // y ∈ t } => ⟨x.1, List.mem_cons_of_mem a x.2⟩)

end Alt.List.attach
