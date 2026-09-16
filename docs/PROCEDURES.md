# Procedure registry

| Procedure | Internal language | Oracle | Reconstruction | Status |
|---|---|---|---|---|
| `Sat` (`Lynth/Sat`) | `CNF` (`Syntax.lean`), `PropForm` skeleton (`Encode.lean`) | DPLL+unit+pure (`Solver.lean`); Tseitin validity oracle over goal skeleton (`Abstract.lean`, hypotheses TODO) | oracle-guided `assumption/rfl/simp_all/grind/decide`; cert via `lynth_sat_resolve` (axiom) | basic |
| `Arith` (`Lynth/Arith`) | `LinSys` (`Linear.lean`) | FM-style stub; `omega` decides | kernel-checked `omega`; cert via `lynth_farkas` (axiom) | basic |
| `EUF` (`Lynth/Euf`) | equality graph over `Eq` hyps (`Closure.lean` union-find) | BFS path search | `Eq.trans`/`Eq.symm` proof terms, kernel-checked, zero axioms | trans/symm done; congruence over applications TODO |
| `Witness` (`Lynth/Witness`) | `Subtype` goals | bounded `Nat` enumeration (bound 64) | `refine ⟨w, ?_⟩` + `decide/omega/simp_all/rfl` | basic |
| EUF / congruence closure | — | — | — | TODO |
| Simplex core | — | — | — | TODO |
| CDCL(T) loop | — | — | — | TODO |

Reconstruction theorems that are correct but unproved live as axioms in
`Lynth/Axioms.lean` (`lynth_sat_resolve`, `lynth_farkas`, `lynth_witness`).
` sorry` is banned; use an axiom + a registry row instead.
