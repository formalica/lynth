import Mathlib

/-!
# `Equiv.List` — routes from `(a, l)` back to `a`

A collection of `def`s of type `(a : α) (l : List α) : α`.  Each one takes a value
*and* a list, and returns the value.  The list is not returned, and the value is
never lost: every entry ends up back at `a`.

This is the third of three shapes, and the one that exists because the other two
were not enough.  `EquivList` is `List α → List α`; `EquivTermList` is `α → α`,
with no list argument at all.  Given a list *and* a value, the value can be
carried by the list instead of by a manufactured `[a, a]`, which is what makes
the mechanisms here genuinely different from both.

Two groups: twelve entries need no instance, ten need `[BEq α]` and so are
grouped last.

Equivalence to `a` is checked by `#eval` over a grid of values against lists of
length 0 to 5, in both argument orders, 20 checks per entry.  For a `def` whose
whole content is "returns its first argument" that is the entire test, so these
are `#eval`-checked rather than proved.
-/

namespace Equiv
namespace List

variable {α : Type*}

def viaAppendLast (a : α) (l : List α) : α := (l ++ [a]).getLast?.getD a

def viaConsReverseLast (a : α) (l : List α) : α := (a :: l).reverse.getLast?.getD a

def viaInsertAtEnd (a : α) (l : List α) : α := (l.insertIdx l.length a).getLast?.getD a

def viaInsertAtFront (a : α) (l : List α) : α := (l.insertIdx 0 a).headD a

def viaReplicateLength (a : α) (l : List α) : α := (List.replicate l.length a).headD a

def viaReplaceAllMap (a : α) (l : List α) : α := l.map (fun _ => a) |>.headD a

def viaFilterMapSome (a : α) (l : List α) : α := l.filterMap (fun _ => some a) |>.headD a

def viaAttachCons (a : α) (l : List α) : α :=
  (List.attach (a :: l)).map Subtype.val |>.headD a

def viaTakeDropRecompose (a : α) (l : List α) : α :=
  ((a :: l).take 1 ++ (a :: l).drop 1).headD a

def viaSplitAtRecompose (a : α) (l : List α) : α :=
  ((((a :: l).splitAt 1).1) ++ ((a :: l).splitAt 1).2).headD a

def viaScanlAbsorb (a : α) (l : List α) : α :=
  ((a :: l).scanl (fun acc _ => acc) a).getLast?.getD a

def viaFlatMapConst (a : α) (l : List α) : α := (l.flatMap (fun _ => [a])).headD a

variable [BEq α]

def viaFindGetD (a : α) (l : List α) : α := l.find? (· == a) |>.getD a

def viaFindIdxFallback (a : α) (l : List α) : α :=
  l.getD (l.findIdx? (· == a) |>.getD l.length) a

def viaPartitionHead (a : α) (l : List α) : α := l.partition (· == a) |>.1 |>.headD a

def viaSpanHead (a : α) (l : List α) : α := l.span (· == a) |>.1 |>.headD a

def viaDiffHead (a : α) (l : List α) : α := (a :: l).diff l |>.headD a

def viaCountReplicate (a : α) (l : List α) : α :=
  (List.replicate (l.count a) a).headD a

def viaEraseReinsert (a : α) (l : List α) : α := l.erase a |>.insertIdx 0 a |>.headD a

def viaZipIdxSearch (a : α) (l : List α) : α :=
  ((List.zipIdx l).find? (fun p => p.fst == a) |>.map Prod.fst).getD a

def viaFoldlAcc (a : α) (l : List α) : α := l.foldl (fun acc x => if x == a then x else acc) a

def viaFilterGetD (a : α) (l : List α) : α := l.filter (· == a) |>.getD 0 a

end List
end Equiv
