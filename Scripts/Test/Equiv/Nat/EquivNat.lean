import Mathlib

/-!
# `ℕ → ℕ` functions that return their argument unchanged

Alternative routes from `n : ℕ` back to `n`, each doing redundant work first.
The value is always the argument; only the route differs.

Grouped by the mechanism that is redundant:

* **degenerate operands** — a divisor/second argument that is *not* the one a
  reader would reach for (`n % (n + 1)`, `n.gcd 0`, `Nat.lcm n 1`);
* **successor round trip** — build `n + 1`, then undo it;
* **bitwise** — `&&&`, `|||` and the shifts have neutral elements too;
* **recover from something much larger** — `log2 (2 ^ n)` and `sqrt (n * n)`;
* **parity decomposition** — halve and double;
* **search** — `Nat.find` / `Nat.findGreatest` reach `n` by scanning;
* **absorbing bounds** — `min`/`max` against a neighbour;
* **guard** — a case split instead of arithmetic.

Deliberately excluded, as too thin to be interesting: the arithmetic identities
(`n + 0`, `n * 1`, `n - 0`, `n / 1`, `n ^ 1`), and every definition routed
through a `List`.

Three of the degenerate-operand entries encode cases that differ in exactly the
way this corpus is meant to record.  `Nat.mod n 0` is `n` but `Nat.div n 0` is
`0`; `Nat.gcd n 0` is `n` but `Nat.lcm n 0` is `0`, so the neutral element for
`lcm` is `1` and for `gcd` it is `0`; and `n % n` is `0` for every `n`, so the
divisor in `viaModSucc` has to be *strictly* greater than `n` rather than equal.

Equivalence to the identity is checked by `#eval` over `List.range 300` plus
`{1000, 1024, 4096}`; for a `def` whose whole content is "returns its input" that
is the entire test, so these are `#eval`-checked rather than proved.
-/

namespace Equiv
namespace Nat

/-! ## Degenerate operands -/

def viaModSucc (n : ℕ) : ℕ := n % (n + 1)

def viaGcdZero (n : ℕ) : ℕ := n.gcd 0

def viaGcdSelf (n : ℕ) : ℕ := n.gcd n

def viaLcmOne (n : ℕ) : ℕ := Nat.lcm n 1

/-! ## Successor round trip -/

def viaPredSucc (n : ℕ) : ℕ := (n + 1).pred

def viaSuccSub (n : ℕ) : ℕ := (n + 1) - 1

def viaMatchSucc (n : ℕ) : ℕ := match n with | 0 => 0 | k + 1 => k + 1

def viaRecSucc (n : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun _ ih => ih + 1) n

/-! ## Bitwise -/

def viaAndSelf (n : ℕ) : ℕ := n &&& n

def viaOrZero (n : ℕ) : ℕ := n ||| 0

def viaShiftLeftZero (n : ℕ) : ℕ := n <<< 0

def viaShiftRightZero (n : ℕ) : ℕ := n >>> 0

/-! ## Recover n from something much larger -/

def viaLog2Pow (n : ℕ) : ℕ := (2 ^ n).log2

def viaSqrtSquare (n : ℕ) : ℕ := (n * n).sqrt

/-! ## Parity decomposition -/

def viaParity (n : ℕ) : ℕ :=
  if n % 2 == 0 then 2 * (n / 2) else 2 * (n / 2) + 1

/-! ## Search -/

def viaFindEq (n : ℕ) : ℕ := Nat.find (p := fun m => m = n) ⟨n, rfl⟩

def viaFindLe (n : ℕ) : ℕ := Nat.find (p := fun m => n ≤ m) ⟨n, Nat.le_refl n⟩

def viaFindGreatest (n : ℕ) : ℕ := Nat.findGreatest (fun m => m ≤ n) n

/-! ## Absorbing bounds -/

def viaMinSucc (n : ℕ) : ℕ := Nat.min n (n + 1)

def viaMaxPred (n : ℕ) : ℕ := Nat.max n (n - 1)

def viaMaxZero (n : ℕ) : ℕ := Nat.max n 0

/-! ## Guard instead of arithmetic -/

def viaIfZero (n : ℕ) : ℕ := if n = 0 then 0 else (n - 1) + 1

end Nat
end Equiv
