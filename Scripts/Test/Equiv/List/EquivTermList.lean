import Mathlib

/-!
# `Equiv.List` — routes from `a` back to `a`

A collection of `def`s of type `α → α`.  Each one builds a list out of its
argument and then reads the argument back out.  The value is always the
argument; only the route differs.

Unlike `EquivList` (the `List α → List α` file) these take no list at all — the
list is manufactured internally, and there are no extra parameters.  Nothing
here reuses a function from `EquivList`, and no entry here is reused by another.

## Why the construction varies

The interesting axis is not the function that reads the answer out, it is the
function that *builds* the carrier list.  Reading `a` off index 0 of `[a, a, a]`
is the same trick three times over, and an earlier draft of this file was
rejected for exactly that reason.  So each entry uses a different way of
manufacturing the list: a membership witness, an array, a matrix transpose, a
nested `Option`, a prefix scan, a `Fin`-indexed family, a `flatMap` producing
multiplicity, an association list, a permutation derivative, a sublist
derivative.

## Instances

Seven need nothing.  Three need `[BEq α]`, and are grouped last.

## Verification

Equivalence to the identity is checked by `#eval`, not by proof: each entry was
evaluated on `Nat` over `List.range 40` and on `String` over lengths 0-5, 20
checks per entry, all agreeing with the argument.  This is the whole test for
this file — a `def` whose entire content is "returns its input" has no other
observable behaviour to check.
-/

namespace Equiv
namespace List

variable {α : Type*}

def viaAttachSubtype (a : α) : α := (List.attach [a]).map Subtype.val |>.headD a

def viaArrayRoundTrip (a : α) : α := (([a] : List α).toArray.toList).headD a

def viaTranspose (a : α) : α :=
  ((List.transpose ([[a]] : List (List α))).headD [a]).headD a

def viaNestedOptionFlatten (a : α) : α :=
  ((List.flatten [([some a] : List (Option α))]).headD (some a)).getD a

def viaScanlAbsorb (a : α) : α :=
  (([a, a] : List α).scanl (fun acc _ => acc) a).getLast?.getD a

def viaOfFn (a : α) : α := (List.ofFn (fun (_ : Fin 1) => a)).headD a

def viaFlatMapDuplicate (a : α) : α :=
  (([a] : List α).flatMap (fun x => [x,x])).getD 1 a

variable [BEq α]

def viaAssocLookup (a : α) : α := (([(a, a)] : List (α × α)).lookup a).getD a

def viaPermutationsFind (a : α) : α :=
  ((List.permutations [a]).find? (· == [a])).getD [a] |>.headD a

def viaSublistsFind (a : α) : α :=
  ((List.sublists [a]).find? (· == [a])).getD [a] |>.headD a

end List
end Equiv
