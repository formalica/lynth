import Lynth.Interval.Core.Ctx
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Constants and the standard evaluation context

`Ctx.make p` is the valid context used by all certificates.

**Current state (M3 bootstrap)**: `π` and `log 2` come from Mathlib's proven
decimal bounds (`Real.pi_gt_d20`, `Real.pi_lt_d20`, `Real.log_two_gt_d9`,
`Real.log_two_lt_d9`), i.e. ~20 and ~9 digits.  They are replaced by
arbitrary-precision series (Machin / atanh, `docs/interval/04 §2`) in
`Fns/Const.lean` once the series toolkit lands; only this file changes.
-/

namespace Lynth.Interval

/-- enclosure of `π` -/
def piIval (p : Nat) : Ival := Ival.ofRats p (314159265358979323846 / 10 ^ 20) (314159265358979323847 / 10 ^ 20)

/-- enclosure of `log 2` -/
def ln2Ival (p : Nat) : Ival := Ival.ofRats p (6931471803 / 10 ^ 10) (6931471808 / 10 ^ 10)

theorem mem_piIval (p : Nat) : Real.pi ∈ piIval p :=
  Ival.mem_ofRats (by have := Real.pi_gt_d20; norm_num at this ⊢; linarith)
    (by have := Real.pi_lt_d20; norm_num at this ⊢; linarith)

theorem mem_ln2Ival (p : Nat) : Real.log 2 ∈ ln2Ival p :=
  Ival.mem_ofRats (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith)
    (by have := Real.log_two_lt_d9; norm_num at this ⊢; linarith)

/-- the standard valid context at precision `p` -/
def Ctx.make (p : Nat) : Ctx := ⟨p, piIval p, ln2Ival p⟩

theorem Ctx.make_valid (p : Nat) : (Ctx.make p).Valid := ⟨mem_piIval p, mem_ln2Ival p⟩

end Lynth.Interval
