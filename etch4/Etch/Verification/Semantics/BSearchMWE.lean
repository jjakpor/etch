import Etch.Verification.Semantics.SkipStream
import Etch.Basic
import Mathlib.Init.Algebra.Order

/- This file is an attempt to prove that the BSearch stream is strictly lawful. -/

namespace Etch.Verification
open Streams


/-- A type representing a state in a binary search stream. -/
  structure BSearchState (α : Type) where
    arrInd : ℕ -- The index in the array we're examining (middle)
    is     : Array α -- The array of indices
    h_set  : (hj : j < is.size) → (hk : k < is.size) → j ≠ k → is[j] ≠ is[k]
    target : α -- The item to find
    currLo : ℕ -- The lower boundary index for the subarray under consideration
    currHi : ℕ -- The upper boundary index for the subarray under consideration
    found  : Bool -- Represents whether the current search was successful
  deriving Repr

  /-- Computes midpoint of two array indices. -/
  def mid (lo hi : ℕ) : ℕ := lo + (hi - lo) / 2  


variable [Inhabited α] 
[LinearOrder α]
  def skip' (q : BSearchState α) (i : α) (r : Bool): BSearchState α :=
    if i > q.target then -- Reset search
      let midInd := mid q.currLo q.is.size - 1
      ⟨midInd, q.is, q.h_set, i, q.currLo, q.is.size - 1, false⟩
    else if i < q.target then q -- No-op
    else if q.currLo <= q.currHi ∧ ¬q.found then  -- Continue search
      if q.target < q.is[q.arrInd]! then 
        let newInd := mid q.currLo q.arrInd
        {q with arrInd := newInd, currHi := q.arrInd - 1}
      else if q.target > q.is[q.arrInd]! then
        let newInd := mid q.arrInd q.currHi
        {q with arrInd := newInd, currLo := q.arrInd + 1}
      else {q with found := true}
    else -- We've found the target or gotten stuck
      if r ∧ q.arrInd < q.is.size then -- this condition i added may be wonky
      -- Reread isstrictmono def
      -- I need to figure out what to do in the case that we finished a search and are now at the end of the array
        if h : q.arrInd + 1 < q.is.size then
        {q with 
           arrInd := q.arrInd + 1,
           target := q.is[q.arrInd + 1]'h
           currLo := q.arrInd + 1,
           currHi := q.arrInd
           found := false}
        else {q with arrInd := q.arrInd + 1}
      else
        q

variable (α)
variable [Inhabited α] 
[LinearOrder α]
 /-- A stream representing a binary search on an array. -/
def bSearch : Stream α ℕ where
  σ := BSearchState α
  index q _ := q.target
  value q _ := q.arrInd
  ready q := q.found
  skip q _ prod := skip' q prod.fst prod.snd
  valid q := q.arrInd < q.is.size

lemma stream_ready_when_at_target (q : BSearchState α) : ¬(q.currLo ≤ q.currHi ∧ ¬q.found = true) → (∃j, (h : j < q.is.size) → q.is[j] = q.target) → q.is[q.arrInd]! = q.target := by
  intros h_done h_exists
  sorry

theorem bsearch_is_mono : (bSearch α).IsMonotonic := by
  intros q hq i
  unfold Stream.index'
  split_ifs
  . rw [WithTop.coe_le_coe]
    dsimp only [bSearch, skip']
    split
    . apply le_of_lt ‹_›
    repeat first | rfl | split_ifs
    . simp only
      sorry
    repeat rfl
  . exact le_top

theorem bsearch_is_strict_mono : (bSearch α).IsStrictMono := by
  unfold Stream.IsStrictMono
  apply And.intro
  -- Prove monotonicity
  . exact bsearch_is_mono _
  -- Prove that progress is being made
  . intros q hq i hi h_ready
    unfold Stream.index'
    split_ifs
    rename Stream.valid _ _ => h_skip_valid
    dsimp only [bSearch, skip']
    split_ifs
    simp only [bSearch] at h_ready
    . simp only [ne_eq, WithTop.coe_eq_coe]
      rename i.fst > q.target => i_gt_tgt
      exact ne_of_lt i_gt_tgt
    . simp only [ne_eq]
      unfold Stream.toOrder at hi
      unfold bSearch at hi
      simp only [Bool.decide_coe] at hi
      rename i.fst < q.target => i_lt_tgt
      have coe_hi : toLex (q.target, q.found) ≤ toLex i := hi 
      have : (q.target, q.found).fst < i.fst ∨ (q.target, q.found).fst = i.fst ∧ (q.target, q.found).snd ≤ i.snd :=
       (Prod.Lex.le_iff (q.target, q.found) i).mp coe_hi
      cases this
      . contradiction
      . rename (q.target, q.found).fst = i.fst ∧ (q.target, q.found).snd ≤ i.snd => tgt_eq_i
        have : q.target = i.fst := tgt_eq_i.left
        exact absurd this (ne_of_gt i_lt_tgt)
    repeat rename q.currLo ≤ q.currHi ∧ ¬q.found = true => h_not_done <;> exact absurd h_ready h_not_done.right
    . simp only [ne_eq, WithTop.coe_eq_coe]
      -- If we're ready then moving past the current index makes us not ready
      have : q.target = q.is[q.arrInd] := sorry
      rw [this]
      sorry
    . unfold bSearch at h_skip_valid
      simp only at h_skip_valid
      unfold skip' at h_skip_valid
      split_ifs at h_skip_valid
      contradiction
    . rename ¬(q.currLo ≤ q.currHi ∧ ¬q.found = true) => h_done
      rename ¬(i.snd = true ∧ q.arrInd < Array.size q.is) => h 
      have r_false_or_invalid : ¬(i.snd = true) ∨ (¬q.arrInd < Array.size q.is) := (@not_and_or ((i.snd = true)) ((q.arrInd < Array.size q.is))).mp h
      cases r_false_or_invalid
      . unfold bSearch at hi
        unfold Stream.toOrder at hi
        simp only [Bool.decide_coe] at hi
        have coe_hi : toLex (q.target, q.found) ≤ toLex i := hi 
        have disj_hi : (q.target, q.found).fst < i.fst ∨ (q.target, q.found).fst = i.fst ∧ (q.target, q.found).snd ≤ i.snd :=
        (Prod.Lex.le_iff (q.target, q.found) i).mp coe_hi
        cases disj_hi
        . contradiction
        . rename (q.target, q.found).fst = i.fst ∧ (q.target, q.found).snd ≤ i.snd => snd_le
          unfold bSearch at h_ready
          simp only at h_ready
          have found_le_r : q.found ≤ i.snd := snd_le.right
          rename ¬i.snd = true => h_not_r
          simp only [Bool.not_eq_true] at h_not_r
          have : i.snd < q.found := -- This follows from the fact that i.snd is false and q.found is true
            calc 
              i.snd = false := by rw [h_not_r]
              false < true := by simp
              true = q.found := eq_comm.mp h_ready
          have : ¬i.snd < q.found := not_lt_of_ge found_le_r
          contradiction
      . contradiction
    . simp