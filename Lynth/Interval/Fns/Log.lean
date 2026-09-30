import Lynth.Interval.Series.Atanh
import Lynth.Interval.Reify.Registry
import Lynth.Interval.Fns.Exp

/-!
# Natural logarithm

Point kernel for `a > 0`: `a = 2^k t` with `t ∈ [1, 2)`,
`log t = log (1 + z) - log (1 - z)` for `z = (t-1)/(t+1)` (atanh series),
`log a = k log 2 + log t` with `log 2` from the context.  Monotone interval
extension on `(0, ∞)`; `top` if the interval may contain nonpositive numbers.
See `docs/interval/04-functions.md §4`.
-/

namespace Lynth.Interval.Fns

open Lynth.Interval Dy

/-- `k` with `a / 2^k ∈ [1, 2)` for `a > 0` -/
def logRed (a : Dy) : Int := (bits a.mantissa : Int) + a.exponent - 1

/-- enclosure of `log a` for `a > 0` (junk-free: `top` if `a ≤ 0`) -/
def logPt (c : Ctx) (w : Nat) (a : Dy) : Ival :=
  if isPos a then
    let k := logRed a
    let T := Ival.pt (Dy.scale2 a (-k))
    let Z := Ival.div w (Ival.sub w T Ival.one) (Ival.add w T Ival.one)
    Ival.add w (Ival.mul w (Ival.pt (Dy.ofInt k)) c.ln2) (atanh2Series w Z)
  else Ival.top

theorem mem_logPt {c : Ctx} (hc : c.Valid) (w : Nat) (a : Dy) : Real.log a.toReal ∈ logPt c w a := by
  unfold logPt
  split
  · rename_i hpos
    simp only
    set k := logRed a
    set t := (Dy.scale2 a (-k)).toReal with ht
    have hapos : 0 < a.toReal := by simp only [toReal_def]; exact_mod_cast (isPos_iff a).1 hpos
    have hat : a.toReal = (2 : ℝ) ^ k * t := by
      simp only [ht, toReal_def, toRat_scale2]; push_cast
      rw [zpow_neg]; field_simp
    have htpos : 0 < t := by
      have h2 : (0 : ℝ) < 2 ^ k := zpow_pos (by norm_num) k
      rw [hat] at hapos; exact pos_of_mul_pos_right hapos h2.le
    have hlog : Real.log a.toReal = (k : ℝ) * Real.log 2 +
        (Real.log (1 + (t - 1) / (t + 1)) - Real.log (1 - (t - 1) / (t + 1))) := by
      rw [hat, Real.log_mul (zpow_pos (by norm_num) k).ne' htpos.ne', Real.log_zpow,
        log_eq_atanh2 htpos]
    rw [hlog]
    have hT : t ∈ Ival.pt (Dy.scale2 a (-k)) := Ival.mem_pt _
    have hZ : (t - 1) / (t + 1) ∈ Ival.div w (Ival.sub w (Ival.pt (Dy.scale2 a (-k))) Ival.one)
        (Ival.add w (Ival.pt (Dy.scale2 a (-k))) Ival.one) :=
      Ival.mem_div (Ival.mem_sub hT Ival.mem_one) (Ival.mem_add hT Ival.mem_one)
    have hk : (k : ℝ) ∈ Ival.pt (Dy.ofInt k) := by
      have := Ival.mem_pt (Dy.ofInt k); simpa [toReal_def] using this
    exact Ival.mem_add (Ival.mem_mul hk hc.ln2_mem) (mem_atanh2Series w hZ)
  · exact Ival.mem_top _

/-- interval extension of `log` (monotone on `(0, ∞)`) -/
def logIval (c : Ctx) (X : Ival) : Ival :=
  let w := c.prec + 8
  match X.lo with
  | some a =>
    if isPos a then
      ⟨(logPt c w a).lo, match X.hi with | some b => (logPt c w b).hi | none => none⟩
    else Ival.top
  | none => Ival.top

theorem mem_logIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    Real.log x ∈ logIval c X := by
  unfold logIval
  simp only
  split
  · rename_i a ha
    split
    · rename_i hpos
      have hapos : 0 < a.toReal := by simp only [toReal_def]; exact_mod_cast (isPos_iff a).1 hpos
      have hax := hx.1 a ha
      have hxpos : 0 < x := lt_of_lt_of_le hapos hax
      refine ⟨?_, ?_⟩
      · intro l hl
        exact le_trans ((mem_logPt hc _ a).1 l hl) (Real.log_le_log hapos hax)
      · split
        · rename_i b hb
          intro h hh
          have hxb := hx.2 b hb
          exact le_trans (Real.log_le_log hxpos hxb) ((mem_logPt hc _ b).2 h hh)
        · simp
    · exact Ival.mem_top _
  · exact Ival.mem_top _

@[lynth_fn] def logR : Fn1 .real .real where
  name := "log"
  graph x y := y = Real.log x
  exu := exu_eq _
  ev := logIval
  sound := fun _ _ _ _ hc hy hx => by obtain rfl := hy; exact mem_logIval hc hx
  cost := 40

end Lynth.Interval.Fns
