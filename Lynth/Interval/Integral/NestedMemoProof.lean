import Lynth.Interval.Integral.NestedExpr

/-! Preservation of stored assertions through memo lookup and resizing. -/
namespace Lynth.Interval.Integral.Nested

open private putBucket from Lynth.Interval.Integral.NestedExpr

def BucketsHold (P : Key → Ival → Prop) (bs : Array (List (Key × Ival))) : Prop :=
  ∀ bucket ∈ bs, ∀ kv ∈ bucket, P kv.1 kv.2

theorem bucketsHold_getElem! {P : Key → Ival → Prop} {bs : Array (List (Key × Ival))}
    (h : BucketsHold P bs) (i : Nat) : ∀ kv ∈ bs[i]!, P kv.1 kv.2 := by
  by_cases hi : i < bs.size
  · rw [getElem!_pos bs i hi]
    exact h _ (Array.getElem_mem hi)
  · simp [getElem!_neg bs i hi,default]

theorem bucketsHold_put {P : Key → Ival → Prop} {bs : Array (List (Key × Ival))}
    (h : BucketsHold P bs) {k : Key} {v : Ival} (hv : P k v) :
    BucketsHold P (putBucket bs k v) := by
  intro bucket hb kv hkv
  have hh := Array.mem_or_eq_of_mem_setIfInBounds hb
  rcases hh with hb | hb
  · exact h bucket hb kv hkv
  · subst bucket
    rcases List.mem_cons.mp hkv with hkv | hkv
    · simpa only [hkv] using hv
    · exact bucketsHold_getElem! h _ kv hkv

theorem bucketsHold_put_many {P : Key → Ival → Prop} {bs : Array (List (Key × Ival))}
    (h : BucketsHold P bs) (kvs : List (Key × Ival)) (hkvs : ∀ kv ∈ kvs, P kv.1 kv.2) :
    BucketsHold P (kvs.foldl (fun bs kv => putBucket bs kv.1 kv.2) bs) := by
  induction kvs generalizing bs with
  | nil => exact h
  | cons kv kvs ih =>
    exact ih (bucketsHold_put h (hkvs kv (by simp)))
      (fun q hq => hkvs q (List.mem_cons_of_mem _ hq))

theorem bucketsHold_empty (P : Key → Ival → Prop) (n : Nat) :
    BucketsHold P (Array.replicate n []) := by
  intro bucket hb kv hkv
  have he : bucket = [] := (Array.mem_replicate.mp hb).2
  simp only [he,List.not_mem_nil] at hkv

theorem bucketsHold_insert {P : Key → Ival → Prop} {m : Memo}
    (hm : BucketsHold P m.buckets) {k : Key} {v : Ival} (hv : P k v) :
    BucketsHold P (m.insert k v).buckets := by
  unfold Memo.insert
  simp only [Id.run,bind,pure]
  split
  · split
    · apply bucketsHold_put _ hv
      apply Array.foldl_induction (fun _ bs => BucketsHold P bs) (bucketsHold_empty P _)
      intro i bs hbs
      apply bucketsHold_put_many hbs
      intro kv hkv
      exact bucketsHold_empty P _ _ (Array.getElem_mem i.isLt) kv
        (List.mem_reverse.mp hkv)
    · exact bucketsHold_put (bucketsHold_empty P _) hv
  · split
    · apply bucketsHold_put _ hv
      apply Array.foldl_induction (fun _ bs => BucketsHold P bs) (bucketsHold_empty P _)
      intro i bs hbs
      apply bucketsHold_put_many hbs
      intro kv hkv
      exact hm _ (Array.getElem_mem i.isLt) kv (List.mem_reverse.mp hkv)
    · exact bucketsHold_put hm hv

theorem bucketsHold_find {P : Key → Ival → Prop} {m : Memo} (hm : BucketsHold P m.buckets)
    (hcongr : ∀ {a b : Key} {I : Ival}, (a == b) = true → P a I → P b I)
    {k : Key} {I : Ival} (h : m.find? k = some I) : P k I := by
  unfold Memo.find? at h
  split at h
  · simp at h
  · cases hf : (m.buckets[(hash k).toNat % m.buckets.size]!).find?
        (fun kv => kv.1 == k) with
    | none => simp [hf] at h
    | some kv =>
      have he : kv.2 = I := by simpa [hf] using h
      subst I
      exact hcongr (List.find?_some (p := fun kv : Key × Ival => kv.1 == k) hf)
        (bucketsHold_getElem! hm _ kv (List.mem_of_find?_eq_some hf))

theorem list_forIn_preserves {α β : Type} (P : β → Prop)
    (f : α → β → Option (ForInStep β)) (xs : List α)
    (hstep : ∀ x ∈ xs, ∀ b s, P b → f x b = some s → P s.value)
    {b r : β} (hb : P b) (h : forIn xs b f = some r) : P r := by
  induction xs generalizing b with
  | nil =>
    have he : b = r := by simpa using h
    exact he ▸ hb
  | cons x xs ih =>
    cases hs : f x b with
    | none => simp [List.forIn_cons,hs] at h
    | some step =>
      have hP := hstep x (by simp) b step hb hs
      cases step with
      | done r' =>
        have he : r' = r := by simpa [List.forIn_cons,hs] using h
        exact he ▸ hP
      | yield b' =>
        apply ih (fun y hy => hstep y (List.mem_cons_of_mem _ hy)) hP
        simpa [List.forIn_cons,hs] using h

end Lynth.Interval.Integral.Nested
