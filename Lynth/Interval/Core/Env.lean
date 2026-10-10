import Lynth.Interval.Core.Fn

/-!
# Variable environments

Variables are de Bruijn indices per value type.  `SEnv` holds semantic
values, `IEnv` their enclosures; `IEnv.Holds σ ρ` says every value lies in its
enclosure (out-of-range lookups give `0` and `top`, which is consistent).
-/

namespace Lynth.Interval

structure SEnv where
  n : List ℕ := []
  z : List ℤ := []
  r : List ℝ := []
  c : List ℂ := []
  q : List ℚ := []

namespace SEnv

def get (ρ : SEnv) : (t : Ty) → ℕ → t.Val
  | .nat, i => ρ.n.getD i 0
  | .int, i => ρ.z.getD i 0
  | .real, i => ρ.r.getD i 0
  | .cplx, i => ρ.c.getD i 0
  | .rat, i => ρ.q.getD i 0
  | .list _, _ => []

def push (ρ : SEnv) : (t : Ty) → t.Val → SEnv
  | .nat, v => { ρ with n := v :: ρ.n }
  | .int, v => { ρ with z := v :: ρ.z }
  | .real, v => { ρ with r := v :: ρ.r }
  | .cplx, v => { ρ with c := v :: ρ.c }
  | .rat, v => { ρ with q := v :: ρ.q }
  | .list _, _ => ρ

end SEnv

structure IEnv where
  n : List NIval := []
  z : List ZIval := []
  r : List Ival := []
  c : List CBox := []
  q : List (Option ℚ) := []
deriving Inhabited

namespace IEnv

def get (σ : IEnv) : (t : Ty) → ℕ → t.Enc
  | .nat, i => σ.n.getD i NIval.top
  | .int, i => σ.z.getD i ZIval.top
  | .real, i => σ.r.getD i Ival.top
  | .cplx, i => σ.c.getD i CBox.top
  | .rat, i => σ.q.getD i none
  | .list _, _ => none

def push (σ : IEnv) : (t : Ty) → t.Enc → IEnv
  | .nat, v => { σ with n := v :: σ.n }
  | .int, v => { σ with z := v :: σ.z }
  | .real, v => { σ with r := v :: σ.r }
  | .cplx, v => { σ with c := v :: σ.c }
  | .rat, v => { σ with q := v :: σ.q }
  | .list _, _ => σ

/-- every variable value lies in its enclosure -/
def Holds (σ : IEnv) (ρ : SEnv) : Prop := ∀ (t : Ty) (i : ℕ), t.Mem (σ.get t i) (ρ.get t i)

private theorem getD_mem {α β : Type} {R : α → β → Prop} {l₁ : List β} {l₂ : List α} {d₁ : β} {d₂ : α}
    (hd : R d₂ d₁) (h : ∀ i, R (l₂.getD i d₂) (l₁.getD i d₁)) (x : β) (X : α) (hx : R X x) :
    ∀ i, R ((X :: l₂).getD i d₂) ((x :: l₁).getD i d₁)
  | 0 => by simpa using hx
  | i + 1 => by simpa using h i

theorem Holds.push {σ : IEnv} {ρ : SEnv} (h : σ.Holds ρ) {t : Ty} {X : t.Enc} {v : t.Val}
    (hv : t.Mem X v) : (σ.push t X).Holds (ρ.push t v) := by
  unfold Holds
  intro t' i
  cases t <;> cases t' <;> first
    | exact h _ i
    | exact getD_mem (R := fun (I : NIval) n => n ∈ I) (NIval.mem_top 0) (h .nat) v X hv i
    | exact getD_mem (R := fun (I : ZIval) z => z ∈ I) (ZIval.mem_top 0) (h .int) v X hv i
    | exact getD_mem (R := fun (I : Ival) x => x ∈ I) (Ival.mem_top 0) (h .real) v X hv i
    | exact getD_mem (R := fun (B : CBox) z => z ∈ B) (CBox.mem_top 0) (h .cplx) v X hv i
    | exact getD_mem (R := fun (o : Option ℚ) (q : ℚ) => ∀ q', o = some q' → q = q')
        (fun (q' : ℚ) (h : (none : Option ℚ) = some q') => nomatch h) (h .rat) v X hv i

theorem holds_empty : (({} : IEnv)).Holds ({} : SEnv) := by
  unfold Holds
  intro t i
  cases t
  · exact NIval.mem_top _
  · exact ZIval.mem_top _
  · exact Ival.mem_top _
  · exact CBox.mem_top _
  · exact fun _ h => nomatch h
  · trivial

end IEnv

end Lynth.Interval
