import Etch.Verification.Semantics.SkipStream
import Etch.Basic
import Mathlib.Init.Algebra.Order

/- This file is an attempt to prove that the BSearch stream is strictly lawful. -/

namespace Etch.Verification
open Streams

variable (α : Type) [Inhabited α] [LinearOrder α]
/-- A type representing a state in a binary search stream. -/
  structure BSearchState (is : List α) where
    h_sorted : List.Sorted (. ≤ .) is
    h_nonempty : is ≠ [] 
    target : α -- The item to find
    currLo : ℕ  -- The lower boundary index for the subarray under consideration
    currHi : ℕ -- The upper boundary index for the subarray under consideration
    -- found  : Bool -- Represents whether the current search was successful
  deriving Repr


  /-- Computes midpoint of two array indices. -/
def mid (lo hi : ℕ) : ℕ := lo + (hi - lo) / 2  

def BSearchState.found (q : BSearchState α is) : Prop := (is[mid q.currLo q.currHi]! = q.target)
def BSearchState.arrInd  (q : BSearchState α is) :  ℕ := mid q.currLo q.currHi

abbrev BSearchState.done (q : BSearchState α is) : Prop := q.currLo > q.currHi ∨ q.currHi = 0 ∨ is[q.arrInd]! = q.target
-- ¬(q.currLo <= q.currHi ∧ q.currHi ≠ 0 ∧ ¬(is[mid q.currLo q.currHi]! = q.target))


def skip' (q : BSearchState α is) (i : α) (r : Bool): BSearchState α is :=
  if i > q.target then -- Reset search
    {q with target := i, currHi := is.length - 1}
    -- equivalent to ⟨q.is, i, q.currLo, q.is.length - 1⟩
  else if i < q.target then q -- No-op
  else if ¬q.done then  -- Continue search. Added q.currHi ≠ 0 to avoid infinite loop due to Nat bottoming out
    if q.target < is[q.arrInd]! then 
      {q with currHi := q.arrInd - 1}
    else if q.target > is[q.arrInd]! then
      {q with currLo := q.arrInd + 1}
    else q
  else -- We've found the target or gotten stuck
    if r then
      if h : q.arrInd + 1 < is.length then
      {q with 
          target := is[q.arrInd + 1]'h -- wrong
          currLo := q.arrInd + 1,
          currHi := q.arrInd + 1}
      else {q with currLo := q.arrInd + 1} -- aha, this case is problematic perhaps. unless we add the assumption that the next state is valid
    else
      q


 /-- A stream representing a binary search on an array. -/
def bSearch (is : List α) : Stream α ℕ where
  σ := BSearchState α is
  index q _ := q.target
  value q _ := q.arrInd
  ready q := q.found
  skip q _ prod := skip' α q prod.fst prod.snd
  valid q := q.arrInd < is.length




