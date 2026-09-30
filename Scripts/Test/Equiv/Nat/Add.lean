import Mathlib

/-!
# Alternative definitions: `Nat.add`

Five ways to add two naturals.  All of them must agree, including on `0`, which
is the case that separates the "peel one successor" schemes from the fold schemes.
-/

namespace Alt.Nat.add

/-- The original. -/
def orig (a b : ℕ) : ℕ := a + b

/-- Recursion on the first argument only, as `Nat.add` is itself defined.  Note
this recurses on `a` rather than `b`. -/
def recOnFirst : ℕ → ℕ → ℕ
  | 0, b => b
  | a + 1, b => (recOnFirst a b) + 1
termination_by a => a

/-- Recursion on the second argument instead, with `a` held fixed.  Same
function, opposite recursion scheme. -/
def recOnSecond (a : ℕ) : ℕ → ℕ
  | 0 => a
  | b + 1 => (recOnSecond a b) + 1
termination_by b => b

/-- `Nat.succ`-wrapping recursion: add by unfolding `b` into successors rather
than using `+ 1`, so the accumulator is built with `Nat.succ`. -/
def viaSucc : ℕ → ℕ → ℕ
  | 0, b => b
  | a + 1, b => Nat.succ (viaSucc a b)
termination_by a => a

/-- Both arguments recursed at once (double recursion).  Slower than the others
but it is a genuinely different shape. -/
def recBoth : ℕ → ℕ → ℕ
  | 0, 0 => 0
  | a + 1, 0 => Nat.succ (recBoth a 0)
  | 0, b + 1 => Nat.succ (recBoth 0 b)
  | a + 1, b + 1 => Nat.succ (Nat.succ (recBoth a b))
termination_by a b => a + b

/-- Addition as a fold: represent `a` as `a` copies of the unit and fold `+`.
This is the "repeated successor" reading of addition, straight from the monoid
presentation `ℕ ≅ Fin ⋃ n`. -/
def viaFoldr (a b : ℕ) : ℕ :=
  (List.replicate a 1).foldl (fun acc _ => acc + 1) b

/-- The same fold idea, but the list of units is produced by `List.range` rather
than `List.replicate`, and the accumulation is done by an explicit recursive
sweep rather than `List.foldl`. -/
def viaRange (a b : ℕ) : ℕ := addRange (List.range a) b
where
  addRange : List ℕ → ℕ → ℕ
  | [], acc => acc
  | _ :: t, acc => addRange t (acc + 1)

end Alt.Nat.add
