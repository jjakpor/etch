import Etch.Verification.Semantics.SkipStream
import Etch.Basic
import Mathlib.Init.Algebra.Order

/- This file is an attempt to prove that the BSearch stream is strictly lawful. -/

namespace Etch.Verification
open Streams


variable (ι : Type) [Inhabited ι] [LinearOrder ι] [OrderTop ι] [OrderBot ι]

structure Arr where
  xs : List ι

def Arr.get (arr : Arr ι) (i : Int) : ι :=
  match i with
  | Int.ofNat n => if h : n < arr.xs.length then  arr.xs[n]'h else ⊤
  | _ => ⊥


variable (is : Arr ι) (mid : ℤ → ℤ → ℤ)
/-- A type representing a state in a binary search stream. -/
structure BSearchState  where
  left : ℤ
  right : ℤ

-- (is : Arr ι) (mid : ℤ → ℤ → ℤ) Don't use as parametesrs. well i know we'd said this, but I think we're fundamentally doing a different search if not



abbrev BSearchState.loopTest (q : BSearchState) : Prop := q.right - q.left > 1

/--- Carries out a step of binary search. -/
def bSearchStep (q : BSearchState) (p : ℤ → Prop) [DecidablePred p]:= -- incrementally designing
  if q.loopTest then
    let m : ℤ := mid q.left q.right
    if p m then {q with right := m} else {q with left := m}
  else q -- extract the lower and upper from this



-- Need to be careful here. Need to avoid changing predicate or middle function in the middle of a search

theorem t (q : BSearchState) (p : ℤ → Prop) : ¬p q.left ∧ p q.right ∧ ¬q.loopTest → q.right = q.left + 1 ∧  ¬p q.left ∧ p q.right := by
intro h
apply And.intro
. unfold BSearchState.loopTest at h
  sorry
  -- h sort of encodes the goal. We got here by calling mid, and mid is strictly between. how to show lean? DO on paper first I guess
. exact And.intro h.left h.right.left


 /-- A stream representing a binary search on an array. -/
def bSearch (is : Arr ι) : Stream ι (ℤ × ℤ)  where
  σ := BSearchState
  index q _ := is.get ι q.left
  value q _ := (q.left, q.right)
  ready q := ¬q.loopTest
  skip q _ prod := sorry -- skip' ι q prod.fst prod.snd
  valid q := sorry -- q.arrInd < is.length


/- I think when we reset the search we should start at the old left.
    But how do we keep monotonicity with pairs? OH, well have ordering lexicographic hwere if first part of pair greater than whole thing greater. Not eq

   -/

/- How do I enforce stream properties?
I guess if the pred were something like x <= a, then we would have to go to x <= the next thing in the array
Which I think I can do in my skip implementation but ignore in bsearchStep

That means BSearchState can't be parameterized in terms of the predicate. But I think I can have variable (is : Arr ι) (mid : ℤ → ℤ → ℤ) be params
-/
