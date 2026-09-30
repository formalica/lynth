# 02 — Numerics: dyadics, rounding, intervals, complex boxes

All computational types are plain inductive data (no proofs inside, no `Rat`),
so they reduce well in the kernel and compile to fast native code.

## 1. `Dy` — dyadic numbers (`Num/Dy.lean`, base vendored from LeanCert)

```lean
namespace Lynth.Interval
/-- `m * 2^e`.  Not normalized: several representations of one value exist. -/
structure Dy where
  m : Int
  e : Int
deriving Repr, DecidableEq, Inhabited
```

Vendored from `LeanCert/Core/Dyadic.lean` (fields `mantissa/exponent`,
functions `add mul neg sub abs scale2 shiftDown shiftUp normalize compare le lt
min max bitLength`, lemmas `toRat_add toRat_mul toRat_neg toRat_shiftDown_le
toRat_shiftUp_ge toRat_normalizeDown_le toRat_normalizeUp_ge le_iff_toRat_le
min/max lemmas`).  Keep the vendored file intact except namespace
(`Lynth.Interval.Vendor`) and imports; build `Dy` as an `abbrev` of it or
re-export.  Semantics:

```lean
def Dy.toRat (d : Dy) : ℚ          -- vendored
noncomputable def Dy.toReal (d : Dy) : ℝ := (d.toRat : ℝ)
@[simp] theorem Dy.toReal_def : d.toReal = d.m * (2:ℝ) ^ d.e   -- zpow
```

### 1.1 Precision and rounding (relative precision, `p` = mantissa bits)

```lean
/-- keep at most `p` significant bits, rounding toward -∞ / +∞ -/
def Dy.roundDown (p : Nat) (d : Dy) : Dy := normalize d p false   -- vendored normalize
def Dy.roundUp   (p : Nat) (d : Dy) : Dy := normalize d p true
theorem Dy.roundDown_le (p d) : (roundDown p d).toRat ≤ d.toRat
theorem Dy.le_roundUp  (p d) : d.toRat ≤ (roundUp p d).toRat
```

Rounded arithmetic used by intervals (all with proofs `≤`/`≥` of the exact op):

| function | meaning |
|---|---|
| `addDown p a b`, `addUp p a b` | round(a+b) |
| `mulDown p a b`, `mulUp p a b` | round(a·b) |
| `divDown p a b`, `divUp p a b` (b ≠ 0 as Bool guard inside; returns junk if b=0, lemmas assume `b.toRat ≠ 0`) | `a/b` via `((a.m <<< k) / b.m)` with floor/ceil fixups, `k := p + bits b.m` |
| `ofRatDown p q`, `ofRatUp p q` | nearest dyadics below/above a rational (`floor(q.num·2^k / q.den)`) |
| `ofIntDy n`, `pow2 k`, `half d` | exact |
| `sqrtDown p a`, `sqrtUp p a` (for `a ≥ 0`) | `Nat.sqrt` of `a.m·2^(2k + parity)` |
| `natAbs`, `sign`, `isZero`, `bits` | helpers |

Division lemma sketch: with `b > 0`, `q := Int.fdiv (a.m * 2^k) b.m`
(floor), `divDown = ⟨q, a.e - b.e - k⟩` and `q * b.m ≤ a.m * 2^k` gives
`toRat ≤ a/b`; `divUp` uses ceiling `-( (-a.m*2^k) fdiv b.m)`.  For `b < 0`
negate both.  Proofs via `Int.ediv_mul_le`, `Int.lt_ediv_add_one_mul_self`,
cast to ℚ, `div_le_iff₀`.

Square root: for `a = m·2^e`, `m ≥ 0`, pick `k` with `e - 2k` even... concretely
`s := Nat.sqrt (m.toNat <<< (2k + (e mod 2)))`, value `s · 2^((e - (e mod 2))/2 - k)`;
`sqrtDown` uses `s`, `sqrtUp` uses `s+1` unless `s*s` is exact.  Lemmas:
`Nat.sqrt_le'` (`sqrt n * sqrt n ≤ n`), `Nat.lt_succ_sqrt'`, then
`Real.sqrt_le_sqrt`, `Real.le_sqrt`, `Real.sqrt_le_left` (vendor LeanCert
`sqrtRatLowerPrec_le_sqrt`/`sqrt_le_sqrtRatUpperPrec` proofs as templates).

Comparison: vendored `Dy.le`, `Dy.lt` (Bool) with `le_iff_toRat_le`.

**Kernel performance rules**: every function here is non-recursive or
structurally recursive on a `Nat` fuel; `Nat.shiftLeft/shiftRight/log2/pow/
div/mod/gcd` are GMP-accelerated in the kernel; `Int` ops reduce to `Nat` ops.

## 2. `Ival` — extended real intervals (`Num/Ival.lean`)

```lean
/-- `lo = none` means -∞, `hi = none` means +∞.  Never stores proofs. -/
structure Ival where
  lo : Option Dy
  hi : Option Dy
deriving Repr, Inhabited

def Ival.top : Ival := ⟨none, none⟩
def Ival.pt (d : Dy) : Ival := ⟨some d, some d⟩

/-- membership (collection-first argument order as in Lean core `Membership`) -/
def Ival.Mem (I : Ival) (x : ℝ) : Prop :=
  (∀ l, I.lo = some l → l.toReal ≤ x) ∧ (∀ h, I.hi = some h → x ≤ h.toReal)
instance : Membership ℝ Ival := ⟨Ival.Mem⟩

theorem Ival.mem_top (x) : x ∈ Ival.top
def Ival.isFinite (I) : Bool := I.lo.isSome && I.hi.isSome
def Ival.width? (I) : Option Dy       -- hi - lo rounded up, none if infinite
```

Every operation takes the precision `p : Nat` (bits) when rounding is needed.
FTIA lemma shape (one per op):

```lean
theorem Ival.mem_add {p x y I J} (hx : x ∈ I) (hy : y ∈ J) : x + y ∈ Ival.add p I J
theorem Ival.mem_neg (hx : x ∈ I) : -x ∈ I.neg
theorem Ival.mem_sub (hx : x ∈ I) (hy : y ∈ J) : x - y ∈ Ival.sub p I J
theorem Ival.mem_mul (hx : x ∈ I) (hy : y ∈ J) : x * y ∈ Ival.mul p I J
theorem Ival.mem_inv (hx : x ∈ I) : x⁻¹ ∈ Ival.inv p I       -- Mathlib: 0⁻¹ = 0
theorem Ival.mem_div (hx : x ∈ I) (hy : y ∈ J) : x / y ∈ Ival.div p I J
theorem Ival.mem_sq (hx : x ∈ I) : x ^ 2 ∈ Ival.sq p I
theorem Ival.mem_npow (hx : x ∈ I) (n : ℕ) : x ^ n ∈ Ival.npow p I n
theorem Ival.mem_abs, mem_min, mem_max, mem_hull_left/right, mem_ofRat, mem_ofDy
theorem Ival.mem_bisect (hx : x ∈ I) : x ∈ (I.bisect).1 ∨ x ∈ (I.bisect).2
```

Algorithms (extended endpoints):

* `add`: `lo := lo₁ +↓ lo₂` (none if either none), `hi := hi₁ +↑ hi₂`.
* `neg`: `⟨hi.map neg, lo.map neg⟩`.
* `mul`: if both finite → classic min/max of the 4 rounded products
  (`mulDown` for min candidates, `mulUp` for max candidates — compute each
  product twice).  If some endpoint infinite: classify each operand as
  `nonneg` (`lo ≥ 0`), `nonpos` (`hi ≤ 0`) or `mixed`; for nonneg×nonneg:
  `[lo₁·lo₂, hi₁·hi₂]` with `none` propagating on the `hi` side; symmetric
  cases by negation; any `mixed` with an infinite endpoint → `top`.
  (Prove the finite case once via `min4/max4` lemmas vendored from LeanCert
  `IntervalRat.mul`; the sign cases via `mul_le_mul` families.)
* `inv`: if `lo > 0` → `[1/↑hi (0 if hi = +∞), 1/↓lo]`; if `hi < 0`
  symmetric; else `top`.  (Mathlib `inv_le_inv₀`, `inv_pos`.)
* `sq` (dependency-aware square): `nonneg → [lo², hi²]`, `nonpos → [hi², lo²]`,
  mixed → `[0, max(lo², hi²)]`.  `npow n`: even n like `sq`-shape via
  `pow_le_pow_left₀`, odd n monotone.  Implement by binary powering on
  intervals *only for odd/even-safe cases*; fallback repeated `mul`.
* `abs`, `min`, `max`, `hull`, `intersect?` (Option; used for refinement),
  `bisect` (at exact midpoint `(lo+hi)/2`, finite only), `mid` (finite only),
  `ofRat p q := ⟨ofRatDown p q, ofRatUp p q⟩`.
* Predicates returning `Bool` used by checkers: `le?`/`lt?` (certainly `≤`/`<`
  between two intervals: `I.hi ≤ J.lo`), `pos?` (`lo > 0`), `nonneg?`,
  `contains0?`, `subset?`.

Lemma for checkers:

```lean
theorem Ival.lt_of_lt? (hx : x ∈ I) (hy : y ∈ J) (h : I.lt? J = true) : x < y
theorem Ival.le_of_le? ... : x ≤ y
```

## 3. `NIval` — natural-number intervals (`Num/NIval.lean`)

```lean
structure NIval where
  lo : Nat
  hi : Option Nat       -- none = ∞
def NIval.Mem (I : NIval) (n : ℕ) : Prop := I.lo ≤ n ∧ ∀ h, I.hi = some h → n ≤ h
```

Ops: `add mul succ pred sub (truncated) min max`, `isPoint : Option Nat`,
`toIval` (cast to ℝ, exact since naturals are dyadic), monotone lifts
`mapMono (f : ℕ → ℕ)` (for `Nat.factorial`, `Nat.fib`, …) with lemma
`Monotone f → n ∈ I → f n ∈ I.mapMono f`.

## 4. `CBox` — complex rectangles (`Num/CBox.lean`)

```lean
structure CBox where
  re : Ival
  im : Ival
def CBox.Mem (B : CBox) (z : ℂ) : Prop := z.re ∈ B.re ∧ z.im ∈ B.im
```

Ops (all with FTIA lemmas via `Complex.add_re`, `Complex.mul_re`,
`Complex.mul_im`, `Complex.inv_re`, `Complex.inv_im`, `Complex.normSq_apply`):

* `add`, `neg`, `sub`, `ofReal (I : Ival) := ⟨I, pt 0⟩`, `I` = `⟨0, 1⟩`,
  `conj`, `re`/`im` projections (to `Ival`).
* `mul`: `re = a·c - b·d`, `im = a·d + b·c` with interval ops.
* `normSq := a² + b²` (use `Ival.sq`, dependency-aware), `norm := sqrt normSq`.
* `inv`: `re = a / normSq`, `im = -b / normSq`; if `normSq` contains 0 → top.
* `div := mul z (inv w)`.
* `npow`: repeated multiplication (binary powering).

Membership proof pattern:

```lean
theorem CBox.mem_mul (hz : z ∈ B) (hw : w ∈ C) : z * w ∈ CBox.mul p B C := by
  obtain ⟨hzr, hzi⟩ := hz; obtain ⟨hwr, hwi⟩ := hw
  refine ⟨?_, ?_⟩
  · simpa [Complex.mul_re] using Ival.mem_sub (Ival.mem_mul hzr hwr) (Ival.mem_mul hzi hwi)
  · simpa [Complex.mul_im] using Ival.mem_add (Ival.mem_mul hzr hwi) (Ival.mem_mul hzi hwr)
```

(Rectangles over-approximate rotations; this is acceptable at the precisions
used.  A disc/ball representation can be added later as a second complex
encoding behind the same `Ty.cplx` interface if needed.)

## 5. Proof-obligation checklist for `Num/` (Milestone M1)

- [ ] `Dy`: toReal lemmas, rounding (`roundDown_le`, `le_roundUp`), `addDown/Up`,
  `mulDown/Up`, `divDown/Up`, `ofRatDown/Up`, `sqrtDown/Up`, `le`/`lt` iff.
- [ ] `Ival`: `mem_top`, `mem_pt`, `mem_ofRat`, `mem_add/neg/sub/mul/inv/div/sq/npow/abs/min/max/hull`,
  `mem_bisect`, `lt_of_lt?`, `le_of_le?`, `pos_of_pos?`, `ne_of_…`.
- [ ] `NIval`: `mem_add/mul/succ`, `mem_mapMono`, `toIval`.
- [ ] `CBox`: `mem_add/neg/sub/mul/inv/div/ofReal/re/im/conj/normSq/norm/npow`.
- [ ] `#eval` smoke tests + `decide +kernel` smoke tests in `Test/Interval/Num.lean`.
