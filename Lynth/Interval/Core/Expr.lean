import Lynth.Interval.Core.Env
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Typed expression AST, denotation, evaluator, soundness

See `docs/interval/03-expr-registry.md §5`.
-/

namespace Lynth.Interval

/-- Typed expressions over the open function registry. -/
inductive Expr : Ty → Type where
  /-- exact rational constant -/
  | lit (q : ℚ) : Expr .real
  /-- natural number literal -/
  | natLit (n : ℕ) : Expr .nat
  /-- de Bruijn variable of the given type -/
  | var (t : Ty) (i : ℕ) : Expr t
  | c0 {r : Ty} (f : Fn0 r) : Expr r
  | c1 {a r : Ty} (f : Fn1 a r) (x : Expr a) : Expr r
  | c2 {a b r : Ty} (f : Fn2 a b r) (x : Expr a) (y : Expr b) : Expr r
  /-- `∑ k ∈ Finset.range n, body`; `body` binds a `.nat` variable (index 0) -/
  | sum (t : Ty) (n : Expr .nat) (body : Expr t) : Expr t

namespace Expr

/-- Denotation. -/
noncomputable def denote : {t : Ty} → Expr t → SEnv → t.Val
  | _, .lit q, _ => (q : ℝ)
  | _, .natLit n, _ => n
  | _, .var t i, ρ => ρ.get t i
  | _, .c0 f, _ => f.val
  | _, .c1 f x, ρ => f.fn (x.denote ρ)
  | _, .c2 f x y, ρ => f.fn (x.denote ρ) (y.denote ρ)
  | _, .sum t n body, ρ => ∑ k ∈ Finset.range (n.denote ρ), body.denote (ρ.push .nat k)

/-- `f lo + … + f (lo + n - 1)`, linear -/
def sumLin (t : Ty) (p : Nat) (f : Nat → t.Enc) (lo : Nat) : Nat → t.Enc
  | 0 => t.zeroE
  | n + 1 => t.addE p (sumLin t p f lo n) (f (lo + n))

/-- `f lo + … + f (lo + n - 1)`, balanced (kernel recursion depth `O(log n)`) -/
def sumBal (t : Ty) (p : Nat) (f : Nat → t.Enc) : Nat → Nat → Nat → t.Enc
  | 0, lo, n => sumLin t p f lo n
  | fuel + 1, lo, n =>
    if n ≤ 4 then sumLin t p f lo n
    else t.addE p (sumBal t p f fuel lo (n / 2)) (sumBal t p f fuel (lo + n / 2) (n - n / 2))

/-- `f 0 + … + f (N-1)` -/
def sumLoop (t : Ty) (p : Nat) (f : Nat → t.Enc) (N : Nat) : t.Enc := sumBal t p f 64 0 N

/-- Interval evaluation. -/
def eval (c : Ctx) : {t : Ty} → Expr t → IEnv → t.Enc
  | _, .lit q, _ => Ival.ofRat c.prec q
  | _, .natLit n, _ => NIval.pt n
  | _, .var t i, σ => σ.get t i
  | _, .c0 f, _ => f.ev c
  | _, .c1 f x, σ => f.ev c (x.eval c σ)
  | _, .c2 f x y, σ => f.ev c (x.eval c σ) (y.eval c σ)
  | _, .sum t n body, σ =>
    match NIval.isPoint (n.eval c σ) with
    | some N => sumLoop t c.prec (fun k => body.eval c (σ.push .nat (NIval.pt k))) N
    | none => t.top

theorem sumLin_sound (t : Ty) (p : Nat) (F : Nat → t.Enc) (f : ℕ → t.Val)
    (h : ∀ k, t.Mem (F k) (f k)) (lo : Nat) :
    ∀ n, t.Mem (sumLin t p F lo n) (∑ i ∈ Finset.range n, f (lo + i))
  | 0 => by simpa [sumLin] using t.mem_zeroE
  | n + 1 => by
    rw [Finset.sum_range_succ]
    exact t.mem_addE (sumLin_sound t p F f h lo n) (h _)

theorem sumBal_sound (t : Ty) (p : Nat) (F : Nat → t.Enc) (f : ℕ → t.Val)
    (h : ∀ k, t.Mem (F k) (f k)) :
    ∀ fuel lo n, t.Mem (sumBal t p F fuel lo n) (∑ i ∈ Finset.range n, f (lo + i))
  | 0, lo, n => sumLin_sound t p F f h lo n
  | fuel + 1, lo, n => by
    unfold sumBal
    split
    · exact sumLin_sound t p F f h lo n
    · have e := Finset.sum_range_add (fun i => f (lo + i)) (n / 2) (n - n / 2)
      rw [show n / 2 + (n - n / 2) = n by omega] at e
      rw [e]
      refine t.mem_addE (sumBal_sound t p F f h fuel lo (n / 2)) ?_
      simpa [add_assoc] using sumBal_sound t p F f h fuel (lo + n / 2) (n - n / 2)

theorem sumLoop_sound (t : Ty) (p : Nat) (F : Nat → t.Enc) (f : ℕ → t.Val)
    (h : ∀ k, t.Mem (F k) (f k)) (N : Nat) : t.Mem (sumLoop t p F N) (∑ k ∈ Finset.range N, f k) := by
  unfold sumLoop; simpa using sumBal_sound t p F f h 64 0 N

/-- **Soundness** of interval evaluation. -/
theorem eval_sound {c : Ctx} (hc : c.Valid) :
    ∀ {t : Ty} (e : Expr t) {ρ : SEnv} {σ : IEnv}, σ.Holds ρ → t.Mem (e.eval c σ) (e.denote ρ)
  | _, .lit q, _, _, _ => Ival.mem_ofRat _ _
  | _, .natLit n, _, _, _ => NIval.mem_pt n
  | _, .var t i, _, _, h => h t i
  | _, .c0 f, _, _, _ => f.sound c _ hc f.val_spec
  | _, .c1 f x, _, _, h => f.sound c _ _ _ hc (f.fn_spec _) (eval_sound hc x h)
  | _, .c2 f x y, _, _, h =>
    f.sound c _ _ _ _ _ hc (f.fn_spec _ _) (eval_sound hc x h) (eval_sound hc y h)
  | _, .sum t n body, ρ, σ, h => by
    show t.Mem (match NIval.isPoint (n.eval c σ) with
      | some N => sumLoop t c.prec (fun k => body.eval c (σ.push .nat (NIval.pt k))) N
      | none => t.top) (∑ k ∈ Finset.range (n.denote ρ), body.denote (ρ.push .nat k))
    split
    · rename_i N hN
      have hn : n.denote ρ = N := NIval.eq_of_isPoint (eval_sound hc n h) hN
      rw [hn]
      exact sumLoop_sound t c.prec _ _
        (fun k => eval_sound hc body (h.push (t := .nat) (NIval.mem_pt k))) N
    · exact t.mem_top _

/-! ### Reification lemmas (used to build `orig = e.denote ρ` proofs) -/

theorem c0_eq {r : Ty} (f : Fn0 r) (ρ : SEnv) {Y : r.Val} (hY : f.graph Y) :
    Y = (Expr.c0 f).denote ρ := f.eq_val hY

theorem c1_eq {a r : Ty} (f : Fn1 a r) (x : Expr a) (ρ : SEnv) {X : a.Val} {Y : r.Val}
    (hX : X = x.denote ρ) (hY : f.graph X Y) : Y = (Expr.c1 f x).denote ρ := by
  subst hX; exact f.eq_fn hY

theorem c2_eq {a b r : Ty} (f : Fn2 a b r) (x : Expr a) (y : Expr b) (ρ : SEnv)
    {X : a.Val} {Y : b.Val} {Z : r.Val}
    (hX : X = x.denote ρ) (hY : Y = y.denote ρ) (hZ : f.graph X Y Z) :
    Z = (Expr.c2 f x y).denote ρ := by
  subst hX; subst hY; exact f.eq_fn hZ

theorem lit_eq (q : ℚ) (ρ : SEnv) {X : ℝ} (h : X = (q : ℝ)) : X = (Expr.lit q).denote ρ := h

theorem natLit_eq (n : ℕ) (ρ : SEnv) {X : ℕ} (h : X = n) : X = (Expr.natLit n).denote ρ := h

theorem sum_eq (t : Ty) (n : Expr .nat) (body : Expr t) (ρ : SEnv) {N : ℕ} {f : ℕ → t.Val}
    (hN : N = n.denote ρ) (hf : ∀ k, f k = body.denote (ρ.push .nat k)) :
    ∑ k ∈ Finset.range N, f k = (Expr.sum t n body).denote ρ := by
  subst hN
  show _ = ∑ k ∈ Finset.range (n.denote ρ), body.denote (ρ.push .nat k)
  exact Finset.sum_congr rfl (fun k _ => hf k)

end Expr

end Lynth.Interval
