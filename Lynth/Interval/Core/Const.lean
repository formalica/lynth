import Lynth.Interval.Core.Ctx
import Lynth.Interval.Series.Arctan
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Constants and the standard evaluation context

`Ctx.make p` is the valid context used by all certificates.

`π` (Machin) and `log 2` (atanh series) are computed to the working precision.
-/

namespace Lynth.Interval

/-- enclosure of `π` (Machin series) -/
def piIval (p : Nat) : Ival := piSeries p

/-- enclosure of `log 2` (series `log 2 = log (4/3) - log (2/3)`) -/
def ln2Ival (p : Nat) : Ival := ln2Series p

theorem mem_piIval (p : Nat) : Real.pi ∈ piIval p := mem_piSeries p

theorem mem_ln2Ival (p : Nat) : Real.log 2 ∈ ln2Ival p := mem_ln2Series p

/-- the standard valid context at precision `p` -/
def Ctx.make (p : Nat) : Ctx := ⟨p, piIval p, ln2Ival p⟩

theorem Ctx.make_valid (p : Nat) : (Ctx.make p).Valid := ⟨mem_piIval p, mem_ln2Ival p⟩

end Lynth.Interval
