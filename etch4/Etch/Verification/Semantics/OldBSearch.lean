import Etch.Verification.Semantics.SkipStream
import Etch.Basic
import Mathlib.Init.Algebra.Order

/- This file is an attempt to prove that the BSearch stream is strictly lawful. -/

namespace Etch.Verification
open Streams


/-- A type representing a state in a binary search stream. -/
  structure BSearchState (α : Type) where
    is     : List α -- The array of indices
    target : α -- The item to find
    currLo : ℕ  -- The lower boundary index for the subarray under consideration
    currHi : ℕ -- The upper boundary index for the subarray under consideration
    -- found  : Bool -- Represents whether the current search was successful
  deriving Repr

    /-- Computes midpoint of two array indices. -/
  def mid (lo hi : ℕ) : ℕ := lo + (hi - lo) / 2  

  def BSearchState.found [Inhabited α] [Preorder α] (q : BSearchState α) : Prop := (q.is[mid q.currLo q.currHi]! = q.target)
  def BSearchState.arrInd  (q : BSearchState α) :  ℕ := mid q.currLo q.currHi

def BSearchState.done [Inhabited α] (q : BSearchState α) : Prop := ¬(q.currLo <= q.currHi ∧ ¬(q.is[mid q.currLo q.currHi]! = q.target))


variable [Inhabited α] 
[LinearOrder α]
  def skip' (q : BSearchState α) (i : α) (r : Bool): BSearchState α :=
    if i > q.target then -- Reset search
      {q with target := i, currHi := q.is.length - 1}
      -- equivalent to ⟨q.is, i, q.currLo, q.is.length - 1⟩
    else if i < q.target then q -- No-op
    else if q.currLo <= q.currHi ∧ q.currHi ≠ 0 ∧ ¬(q.is[mid q.currLo q.currHi]! = q.target) then  -- Continue search. Added q.currHi ≠ 0 to avoid infinite loop due to Nat bottoming out
      if q.target < q.is[q.arrInd]! then 
        {q with currHi := q.arrInd - 1}
      else if q.target > q.is[q.arrInd]! then
        {q with currLo := q.arrInd + 1}
      else q
    else -- We've found the target or gotten stuck
      if r then
        if h : q.arrInd + 1 < q.is.length then
        {q with 
           target := q.is[q.arrInd + 1]'h
           currLo := q.arrInd + 1,
           currHi := q.arrInd + 1}
        else {q with currLo := q.arrInd + 1}
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
  valid q := q.arrInd < q.is.length

def inv_conj (q : BSearchState α) : Prop :=
 List.Sorted (. ≤ .) q.is → q.is ≠[]  → List.Mem q.target q.is → q.is[q.currLo]! ≤ q.target ∧ q.target ≤ q.is[q.currHi]!
#check inv_conj
theorem inv_init (q : BSearchState α) : q.currLo = 0 ∧ q.currHi = q.is.length - 1 → inv_conj α q := by --List.Sorted (. ≤ .) q.is → List.Mem q.target q.is → q.is[q.currLo]! ≤ q.target ∧ q.target ≤ q.is[q.currHi]! := by
  intros h_init h_sorted h_nonempty  h_mem
  have hal : q.currLo = 0 := h_init.left
  have har : q.currHi = q.is.length - 1 := h_init.right
  rw [hal, har]
  have list_eq_cons_head_tail : (h :q.is ≠ []) → (q.is = q.is.head h :: q.is.tail) := by sorry
  rw [list_eq_cons_head_tail h_nonempty] at h_sorted
  apply And.intro
  . sorry -- I think I want List.rel_of_sorted_cons


    -- exact List.rel_of_sorted_cons h_sorted q.target h_mem -- what's an easy way to say this list is nonempty
  . sorry

    
    -- why is lean being weird


theorem invariant (q : BSearchState α) : inv_conj α q := sorry -- this shouldn't actually be a universal i think, just for all q in the transition system

  

  


theorem bsearch_correctness (q : BSearchState α) : List.Sorted (. ≤ .) q.is → q.is ≠ [] → q.done → List.Mem q.target q.is → q.is[q.arrInd]! = q.target := by
  intros sorted nonempty done mem
  have inv := invariant α q
  unfold inv_conj at inv
  have tgt_between : q.is[q.currLo]! ≤ q.target ∧ q.target ≤ q.is[q.currHi]! := inv sorted nonempty mem
  unfold BSearchState.arrInd
  unfold BSearchState.done at done
  rw [not_and_or] at done
  cases done
  . rename ¬q.currLo ≤ q.currHi => h_lo_gt_hi
    have eq_tgt_or_not : q.is[mid q.currLo q.currHi]! = q.target ∨ ¬q.is[mid q.currLo q.currHi]! = q.target := or_not
    cases eq_tgt_or_not
    . assumption
    . sorry -- the goal is to show a contradiction
  . rename ¬¬_ => h_eq
    rw [not_not] at h_eq
    assumption

-- this is the same proof but based on the disjunction form of implication rather than introducing proof terms
theorem bsearch_correctness' (q : BSearchState α) : List.Sorted (. ≤ .) q.is → q.is ≠ [] → q.done → List.Mem q.target q.is → q.is[q.arrInd]! = q.target := by
  intros h_sorted h_nonempty h_done
  rw [imp_iff_not_or]
  unfold BSearchState.done at h_done
  rw [not_and_or] at h_done
  cases h_done
  . left
    have inv := invariant α q
    unfold inv_conj at inv
    have : List.Mem q.target q.is → q.is[q.currLo]! ≤ q.target ∧ q.target ≤ q.is[q.currHi]! := inv h_sorted h_nonempty
    rw [imp_iff_not_or] at this
    cases this
    . assumption
    . sorry
  . right
    rename ¬¬_ => h_eq
    rw [not_not] at h_eq
    assumption
    












theorem bsearch_is_mono : (bSearch α).IsMonotonic := by
  intros q hq i
  unfold Stream.index'
  split_ifs
  . rw [WithTop.coe_le_coe]
    dsimp only [bSearch, skip']
    split
    . apply le_of_lt ‹_›
    repeat first | rfl | split_ifs
    . simp only [BSearchState.arrInd, mid]
      have tgt_exists_or_not : List.Mem q.target q.is ∨ ¬List.Mem q.target q.is := or_not
      have h_sorted : List.Sorted (. ≤ .) q.is := by sorry
      rename ¬(q.currLo ≤ q.currHi ∧ q.currHi ≠ 0 ∧ ¬q.is[mid q.currLo q.currHi]! = q.target) => h_done
      cases tgt_exists_or_not
      . rename List.Mem q.target q.is => h_tgt_exists
        have : q.is[q.arrInd]! = q.target := sorry -- bsearch_correctness α q h_sorted h_done h_tgt_exists
        simp only [BSearchState.arrInd, mid] at this
        rw [←this]
         -- the new goal follows from the fact that it's sorted, but idk
        sorry
      . sorry -- Is it enough to show that q.is[q.currLo + (q.currHi - q.currLo) / 2] ≤ q.is[q.currLo + (q.currHi - q.currLo) / 2 + 1]
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