import Scripts.Test.Equiv.List.Foldr

/-!
# Proofs: `List.foldr` alternatives are equal to the original

Three of the four alternatives in `../Foldr.lean` are proved equal to `List.foldr`
here; only `byFinRange` is not.  See the note below.

As in `../Proofs/Foldl.lean`, everything proved here is valid for an arbitrary
`f : α → β → β`: no associativity, no commutativity, no reordering of the
elements.

`byTailLoop` used to be *wrong* and is now corrected; the counterexamples that
exposed it, and the shape of the fix, are recorded under that heading.
-/

namespace Alt.List.foldr

universe u v

variable {α : Type u} {β : Type v}

/-! ## `byRec` -/

/-- Structural recursion, the textbook definition.  The `congrArg (f a)` is
because the head is combined with the recursive result rather than the other way
round — the mirror image of the `byRec` proof in `../Proofs/Foldl.lean`. -/
theorem byRec_eq (f : α → β → β) (init : β) : ∀ (l : List α),
    byRec f init l = List.foldr f init l
  | [] => rfl
  | a :: t => by
    rw [show byRec f init (a :: t) = f a (byRec f init t) from rfl]
    exact congrArg (f a) (byRec_eq f init t)

/-! ## `byRevFoldl` -/

/-- The general fact, stated for a fixed seed: `List.foldl` consumes its argument
front to back, so feeding it `l.reverse` makes it visit `l` from the back while
threading the accumulator in the order `List.foldr` needs. -/
private theorem revfoldl_gen (f : α → β → β) (init : β) : ∀ (l : List α),
    List.foldl (fun acc a => f a acc) init l.reverse = List.foldr f init l
  | [] => by rfl
  | a :: t => by
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldr_cons, revfoldl_gen]

theorem byRevFoldl_eq (f : α → β → β) (init : β) (l : List α) :
    byRevFoldl f init l = List.foldr f init l := by
  simp only [byRevFoldl, revfoldl_gen]

/-! ## `byTailLoop`

`byTailLoop` was originally a **wrong** definition, and is worth recording because
the error is a common one.  It used to read

```
go : List α → β → β
  | [], acc => acc
  | a :: t, acc => go t (f a acc)
```

which threads the accumulator *inwards*, so it is a **left** fold, not a right one:

```
byTailLoop (fun a acc => acc ++ [a]) [] [1,2,3]  =  [1,2,3]
List.foldr   (fun a acc => acc ++ [a]) [] [1,2,3]  =  [3,2,1]
byTailLoop (fun a acc => acc * 10 + a) 5 [1,2]  =  512
List.foldr   (fun a acc => acc * 10 + a) 5 [1,2]  =  521
```

Note the two `f`s above are both commutative (`Nat.add` and `Nat.mul` in disguise),
and commutativity is precisely what made the mistake survive: threading an
accumulator inwards instead of outwards is invisible to any check built on `+`,
`*`, or `fun x => x < 2`, which is all the sample grid used.  A `#eval` grid only
rules out the errors it can think to probe for.  Lean's own equation lemma gave it
away without any probing: `byTailLoop.go.eq_2` was
`go f (a :: t) acc = go f t (f acc a)`, with the accumulator as the *first*
argument of `f`.

The docstring at the time claimed the loop accumulated "outward" and needed no
reversal of the output.  That claim is not available: a right fold over an
arbitrary `β` cannot be computed by a single tail-recursive loop with one
accumulator, because the head of the list must be applied *last*, after the tail
has been fully processed, and a loop walking front to back has already fixed the
accumulator by then.  The corrected definition therefore uses two tail loops and an
explicit pending stack — see `../Foldr.lean` — and is proved below.

The only difference between the two loops is which way the stack is walked, so the
whole proof is two auxiliary "unwind this stack" statements plus a re-indexing of
the stack at each cons. -/

/-- The single algebraic step the stack needs: seeding `List.foldr` with `f a acc`
is the same as folding over `s ++ [a]`, because `a` then ends up applied
outermost.  Everything else in the proof is bookkeeping about where the pending
elements sit. -/
private theorem foldr_push (f : α → β → β) (a : α) (acc : β) : ∀ (s : List α),
    List.foldr f (f a acc) s = List.foldr f acc (s ++ [a])
  | [] => by simp [List.foldr_nil]
  | b :: t => by
    rw [List.foldr_cons, List.cons_append, foldr_push]
    rw [List.foldr_cons]

/-- The pop phase, generalised over the accumulator: popping a stack one element
at a time and applying `f` is a `List.foldr` over the stack read back to front. -/
private theorem unwind_gen (f : α → β → β) (acc : β) : ∀ (stk : List α),
    byTailLoop.unwind f stk acc = List.foldr f acc (List.reverse stk)
  | [] => rfl
  | b :: t => by
    change byTailLoop.unwind f t (f b acc) = List.foldr f acc (List.reverse (b :: t))
    rw [unwind_gen f (f b acc) t, List.reverse_cons, foldr_push]

/-- The push phase, generalised over both the input and the stack: pushing `t`
onto `stk` makes `t` the outer part of the remaining fold.  The cons case is the
whole point of the definition — the element moves from the head of `t` to the head
of `stk`, and the induction hypothesis is re-instantiated at the grown stack. -/
private theorem go_gen (f : α → β → β) (acc : β) : ∀ (t stk : List α),
    byTailLoop.go f t stk acc = List.foldr f acc (List.reverse stk ++ t)
  | [], stk => by
    change byTailLoop.unwind f stk acc = List.foldr f acc (List.reverse stk ++ [])
    rw [unwind_gen f acc stk, List.append_nil]
  | b :: t, stk => by
    change byTailLoop.go f t (b :: stk) acc = List.foldr f acc (List.reverse stk ++ b :: t)
    rw [go_gen f acc t (b :: stk)]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem byTailLoop_eq (f : α → β → β) (init : β) (l : List α) :
    byTailLoop f init l = List.foldr f init l := by
  change byTailLoop.go f l [] init = _
  rw [go_gen f init l [], List.reverse_nil, List.nil_append]

/-! ## `byFinRange` -/

/-- `List.finRange l.length` visits every position once, so `List.get` reads at
each of them give `l` back as a `map`. -/
private theorem map_get_finRange (l : List α) :
    List.map l.get (List.finRange l.length) = l :=
  (List.ofFn_eq_map (f := l.get)).symm.trans (List.ofFn_get l)

/-- The fold here runs over the index list *reversed* with the arguments flipped,
so `List.foldl_reverse` turns it into a `foldr` and `List.foldr_map` then pulls
the `get` reads out into the list — at which point the index list is `l`. -/
private theorem foldl_reverse_finRange (h : α → β → β) (l : List α) (acc : β) :
    List.foldl (fun a i => h (l.get i) a) acc (List.finRange l.length).reverse
      = List.foldr h acc l := by
  rw [List.foldl_reverse, ← List.foldr_map, map_get_finRange]

theorem byFinRange_eq (f : α → β → β) (init : β) (l : List α) :
    byFinRange f init l = List.foldr f init l := by
  simp only [byFinRange]
  rw [foldl_reverse_finRange f l init]

/-! ## Against the original -/

theorem byRec_eq_orig (f : α → β → β) (init : β) (l : List α) : byRec f init l = orig f init l :=
  byRec_eq f init l

theorem byRevFoldl_eq_orig (f : α → β → β) (init : β) (l : List α) :
    byRevFoldl f init l = orig f init l := byRevFoldl_eq f init l

theorem byTailLoop_eq_orig (f : α → β → β) (init : β) (l : List α) :
    byTailLoop f init l = orig f init l := byTailLoop_eq f init l

theorem byFinRange_eq_orig (f : α → β → β) (init : β) (l : List α) :
    byFinRange f init l = orig f init l := byFinRange_eq f init l

end Alt.List.foldr
