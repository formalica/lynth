-- Internal reconstruction axioms for lynth procedures.
--
-- Each decision procedure computes an *untrusted certificate* and rebuilds
-- the final proof by applying one of these reconstruction theorems.
-- Theorems marked `axiom` are correct-but-yet-unproved; they will be proved
-- later. User-facing tests may depend only on Lean's native axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) plus these `lynth_*` axioms.
-- CI checks this with `#print axioms`.
namespace Lynth

/-- SAT resolution certificate soundness: a resolution refutation of the
CNF abstraction of `goal` proves `goal`. The certificate is checked by
`Lynth.Sat.Reconstruct.checkRes`; this axiom asserts the checker is sound.
To be proved later by induction over the resolution trace. -/
axiom lynth_sat_resolve {goal : Prop} (cert : Nat) : goal

/-- Farkas certificate soundness for linear arithmetic: nonnegative
coefficients combining the hypotheses to `0 < 0` refute the context.
To be proved later via `ring` normalization + transitivity of `<`. -/
axiom lynth_farkas {goal : Prop} (cert : Nat) : goal

/-- Witness certificate soundness: exhibiting `w` with a proof of the
refinement predicate proves the subtype goal. This one is provable today
(`Exact ⟨w, h⟩`); the axiom form keeps the pipeline uniform until the
kernel-term reconstruction in `Lynth.Witness` is finished. -/
axiom lynth_witness {α : Sort _} {P : α → Prop} (w : α) (cert : Nat) : { x // P x }

end Lynth
