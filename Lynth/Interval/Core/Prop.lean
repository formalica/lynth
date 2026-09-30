import Lynth.Interval.Core.Expr

/-!
# Propositions over expressions

`PropExpr` is the fragment of closed/boxed propositions the checkers decide:
comparisons of real expressions combined with `∧ ∨ ¬ →`.  `eval3` is a
three-valued interval evaluation; `eval3_sound` is proved once.
See `docs/interval/03-expr-registry.md §6`.
-/

namespace Lynth.Interval

inductive PropExpr where
  | lt (a b : Expr .real)
  | le (a b : Expr .real)
  | and (p q : PropExpr)
  | or (p q : PropExpr)
  | not (p : PropExpr)
  | imp (p q : PropExpr)
  | tt
  | ff

inductive Tri | yes | no | unk
deriving DecidableEq, Repr, Inhabited

namespace PropExpr

noncomputable def denote : PropExpr → SEnv → Prop
  | .lt a b, ρ => a.denote ρ < b.denote ρ
  | .le a b, ρ => a.denote ρ ≤ b.denote ρ
  | .and p q, ρ => p.denote ρ ∧ q.denote ρ
  | .or p q, ρ => p.denote ρ ∨ q.denote ρ
  | .not p, ρ => ¬ p.denote ρ
  | .imp p q, ρ => p.denote ρ → q.denote ρ
  | .tt, _ => True
  | .ff, _ => False

def triAnd : Tri → Tri → Tri
  | .yes, .yes => .yes
  | .no, _ => .no
  | _, .no => .no
  | _, _ => .unk

def triOr : Tri → Tri → Tri
  | .no, .no => .no
  | .yes, _ => .yes
  | _, .yes => .yes
  | _, _ => .unk

def triNot : Tri → Tri
  | .yes => .no
  | .no => .yes
  | .unk => .unk

/-- three-valued interval evaluation -/
def eval3 (c : Ctx) : PropExpr → IEnv → Tri
  | .lt a b, σ =>
    let A : Ival := a.eval c σ
    let B : Ival := b.eval c σ
    if Ival.ltB A B then .yes else if Ival.leB B A then .no else .unk
  | .le a b, σ =>
    let A : Ival := a.eval c σ
    let B : Ival := b.eval c σ
    if Ival.leB A B then .yes else if Ival.ltB B A then .no else .unk
  | .and p q, σ => triAnd (p.eval3 c σ) (q.eval3 c σ)
  | .or p q, σ => triOr (p.eval3 c σ) (q.eval3 c σ)
  | .not p, σ => triNot (p.eval3 c σ)
  | .imp p q, σ => triOr (triNot (p.eval3 c σ)) (q.eval3 c σ)
  | .tt, _ => .yes
  | .ff, _ => .no

/-- certified truth -/
def check (c : Ctx) (p : PropExpr) (σ : IEnv) : Bool := p.eval3 c σ == .yes

theorem eval3_sound {c : Ctx} (hc : c.Valid) {ρ : SEnv} {σ : IEnv} (h : σ.Holds ρ) :
    ∀ p : PropExpr, (p.eval3 c σ = .yes → p.denote ρ) ∧ (p.eval3 c σ = .no → ¬ p.denote ρ)
  | .lt a b => by
    have ha : a.denote ρ ∈ (a.eval c σ : Ival) := Expr.eval_sound hc a h
    have hb : b.denote ρ ∈ (b.eval c σ : Ival) := Expr.eval_sound hc b h
    simp only [eval3, denote]
    refine ⟨fun hy => ?_, fun hn => ?_⟩
    · split at hy
      · rename_i h1; exact Ival.lt_of_ltB ha hb h1
      · split at hy <;> simp at hy
    · split at hn
      · simp at hn
      · split at hn
        · rename_i _ h2; exact not_lt.2 (Ival.le_of_leB hb ha h2)
        · simp at hn
  | .le a b => by
    have ha : a.denote ρ ∈ (a.eval c σ : Ival) := Expr.eval_sound hc a h
    have hb : b.denote ρ ∈ (b.eval c σ : Ival) := Expr.eval_sound hc b h
    simp only [eval3, denote]
    refine ⟨fun hy => ?_, fun hn => ?_⟩
    · split at hy
      · rename_i h1; exact Ival.le_of_leB ha hb h1
      · split at hy <;> simp at hy
    · split at hn
      · simp at hn
      · split at hn
        · rename_i _ h2; exact not_le.2 (Ival.lt_of_ltB hb ha h2)
        · simp at hn
  | .and p q => by
    have hp := eval3_sound hc h p; have hq := eval3_sound hc h q
    simp only [eval3, denote]
    constructor
    · intro hy
      cases h1 : p.eval3 c σ <;> cases h2 : q.eval3 c σ <;> simp [h1, h2, triAnd] at hy
      exact ⟨hp.1 h1, hq.1 h2⟩
    · intro hn ⟨h3, h4⟩
      cases h1 : p.eval3 c σ <;> cases h2 : q.eval3 c σ <;> simp [h1, h2, triAnd] at hn
      all_goals first | exact hp.2 h1 h3 | exact hq.2 h2 h4
  | .or p q => by
    have hp := eval3_sound hc h p; have hq := eval3_sound hc h q
    simp only [eval3, denote]
    constructor
    · intro hy
      cases h1 : p.eval3 c σ <;> cases h2 : q.eval3 c σ <;> simp [h1, h2, triOr] at hy
      all_goals first | exact Or.inl (hp.1 h1) | exact Or.inr (hq.1 h2)
    · intro hn h3
      cases h1 : p.eval3 c σ <;> cases h2 : q.eval3 c σ <;> simp [h1, h2, triOr] at hn
      rcases h3 with h3 | h3
      · exact hp.2 h1 h3
      · exact hq.2 h2 h3
  | .not p => by
    have hp := eval3_sound hc h p
    simp only [eval3, denote]
    constructor
    · intro hy
      cases h1 : p.eval3 c σ <;> simp [h1, triNot] at hy
      exact hp.2 h1
    · intro hn
      cases h1 : p.eval3 c σ <;> simp [h1, triNot] at hn
      exact fun h' => h' (hp.1 h1)
  | .imp p q => by
    have hp := eval3_sound hc h p; have hq := eval3_sound hc h q
    simp only [eval3, denote]
    constructor
    · intro hy hpd
      cases h1 : p.eval3 c σ <;> cases h2 : q.eval3 c σ <;> simp [h1, h2, triOr, triNot] at hy
      all_goals first | exact hq.1 h2 | exact absurd hpd (hp.2 h1)
    · intro hn himp
      cases h1 : p.eval3 c σ <;> cases h2 : q.eval3 c σ <;> simp [h1, h2, triOr, triNot] at hn
      exact hq.2 h2 (himp (hp.1 h1))
  | .tt => by simp [eval3, denote]
  | .ff => by simp [eval3, denote]

theorem check_sound {c : Ctx} (hc : c.Valid) {ρ : SEnv} {σ : IEnv} (h : σ.Holds ρ)
    {p : PropExpr} (hp : p.check c σ = true) : p.denote ρ :=
  (eval3_sound hc h p).1 (by simpa [check] using hp)

/-! ### Reification lemmas -/

theorem lt_eq (a b : Expr .real) (ρ : SEnv) {A B : ℝ} (hA : A = a.denote ρ) (hB : B = b.denote ρ) :
    (A < B) = (PropExpr.lt a b).denote ρ := by subst hA; subst hB; rfl
theorem le_eq (a b : Expr .real) (ρ : SEnv) {A B : ℝ} (hA : A = a.denote ρ) (hB : B = b.denote ρ) :
    (A ≤ B) = (PropExpr.le a b).denote ρ := by subst hA; subst hB; rfl
theorem and_eq (p q : PropExpr) (ρ : SEnv) {P Q : Prop} (hP : P = p.denote ρ) (hQ : Q = q.denote ρ) :
    (P ∧ Q) = (PropExpr.and p q).denote ρ := by subst hP; subst hQ; rfl
theorem or_eq (p q : PropExpr) (ρ : SEnv) {P Q : Prop} (hP : P = p.denote ρ) (hQ : Q = q.denote ρ) :
    (P ∨ Q) = (PropExpr.or p q).denote ρ := by subst hP; subst hQ; rfl
theorem not_eq (p : PropExpr) (ρ : SEnv) {P : Prop} (hP : P = p.denote ρ) :
    (¬ P) = (PropExpr.not p).denote ρ := by subst hP; rfl
theorem imp_eq (p q : PropExpr) (ρ : SEnv) {P Q : Prop} (hP : P = p.denote ρ) (hQ : Q = q.denote ρ) :
    (P → Q) = (PropExpr.imp p q).denote ρ := by subst hP; subst hQ; rfl
theorem tt_eq (ρ : SEnv) : True = PropExpr.tt.denote ρ := rfl
theorem ff_eq (ρ : SEnv) : False = PropExpr.ff.denote ρ := rfl

/-- closed propositions: from a certificate to the original statement -/
theorem of_check {P : Prop} {p : PropExpr} {c : Ctx} (hc : c.Valid) (hP : P = p.denote {})
    (h : p.check c {} = true) : P := hP ▸ check_sound hc IEnv.holds_empty h

end PropExpr

end Lynth.Interval
