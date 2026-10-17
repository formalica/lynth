import Mathlib.Data.Nat.Log

/-! Portable equality used only to select a faster native implementation.
The bounded binary search remains the kernel implementation. -/

namespace Lynth.Interval.Vendor.Dyadic

def bitSearchS (n : Nat) : Nat → Nat → Nat → Nat
  | 0, _, hi => hi
  | fuel + 1, lo, hi =>
    cond (hi.ble (lo + 1)) hi
      (cond ((n >>> ((lo + hi) / 2)).beq 0) (bitSearchS n fuel lo ((lo + hi) / 2))
        (bitSearchS n fuel ((lo + hi) / 2) hi))

/-- The search has enough iterations for either initial bracket. The upper
cap is intentional: preserve the original behavior even above 65536 bits. -/
theorem bitSearchS_eq_log2 (n : Nat) (hn : n ≠ 0) :
    bitSearchS n 20 0 (cond ((n >>> 256).beq 0) 256 65536) =
      min 65536 (n.log2 + 1) := by
  sorry

end Lynth.Interval.Vendor.Dyadic
