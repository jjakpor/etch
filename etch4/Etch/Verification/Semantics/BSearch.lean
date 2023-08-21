import Etch.Verification.Semantics.SkipStream
import Etch.Basic
import Mathlib.Init.Algebra.Order

/- This file is an attempt to prove that the BSearch stream is strictly lawful. -/





set_option linter.uppercaseLean3 false

open Classical

noncomputable section
namespace Etch.Verification
open Streams

 

section BSearchSec

variable {α : Type} 
[LT α] [DecidableLT α] 
[Inhabited α] [DecidableEq α]

  /-- A type representing a state in a binary search stream. -/
  structure BSearchState (α : Type) where
    arrInd : ℕ -- The index in the array we're examining (middle)
    is     : Array α -- The array ofindices
    target : α -- The item to find
    currLo : ℕ -- The lower boundary index for the subarray under consideration
    currHi : ℕ -- The upper boundary index for the subarray under consideration
    found  : Bool -- Represents whether the current search was successful
  deriving Repr, BEq

  /-- Computes midpoint of two array indices. -/
  def mid (lo hi : ℕ) : ℕ := lo + (hi - lo) / 2  

  /-- Implementation of skip for binary search.
  TODO: write further documentation
  -/
  def skip' (q : BSearchState α) (i : α) (r : Bool): BSearchState α :=
    if i > q.target then -- Reset search
      let midInd := mid q.currLo q.is.size - 1
      ⟨midInd, q.is, i, q.currLo, q.is.size - 1, false⟩
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
      if r ∧ q.arrInd < q.is.size then 
        -- Move on by scooting the low pointer past where the target would be if it exists
        -- If the is are unique (which they are, right?), this means δ will trigger a search that will fail.
        {q with currLo := q.arrInd + 1, found := false}
      else
        q

   /-- A stream representing a binary search on an array. -/
  def bSearch : Stream α ℕ where
    σ := BSearchState α
    index q _ := q.target
    value q _ := q.arrInd
    ready q := q.found
    skip q _ prod := skip' q prod.fst prod.snd
    valid q := q.arrInd < q.is.size


lemma search_succ_is_increasing (q : BSearchState α) (is : Array α) (target : α) : let search := bSearch is target
  search.index' q ≤ search.index' (searchSucc is target q) := 
  by
    simp
    unfold Stream.index'
    split
    -- Assume q is valid
    rename Stream.valid (bSearch is target) q => h_valid
    unfold Stream.index
    unfold bSearch
    simp
    split
    -- Assume succssor is also valid
    rename ¬(searchSucc is target q).arrVal = target ∧ ¬searchSucc is target (searchSucc is target q) = searchSucc is target q => h_succ_valid
    unfold bSearch at h_valid
    simp at h_valid
    unfold searchSucc
    split
    -- Assume the search is not yet done
    rename q.lo ≠ q.hi ∧ q.arrVal ≠ target => not_done
    split
    -- Assume target < q.arrVal
    simp
    split
    -- Assume curr = target. Then succ's index is q.searchIndex + 1. Close goal
    simp
    -- Now assume curr != target. Then succ's index = index. Close goal
    simp

    
    rename ¬target < q.arrVal => tgt_ge_curr-- Now assume target >= arrval
    simp
    split -- Assume the next is equal to target
    simp -- Then result's searchIndex is searchIndex + 1. Trivially close goal
    simp -- Now assume is[mid q.arrInd q.hi]! ≠  target. Then searchIndex is unchanged

    simp -- Now assume we're done with the search  ¬(q.lo ≠ q.hi ∧ q.arrVal ≠ target). Easy to show!
    
    simp -- Now assume successor is not valid. Any num is less than top?

    rename ¬Stream.valid (bSearch is target) q => h_invalid
    simp -- Want to show searchSucc is invalid
    intro h_succ_valid
    unfold bSearch at h_invalid
    unfold bSearch at h_succ_valid
    simp at *

    have succ_invalid : ¬Stream.valid (bSearch is target) (searchSucc is target q) := by
      have eq_or_ne : q.arrVal = target ∨ ¬q.arrVal = target  := Classical.em (q.arrVal = target)
      cases eq_or_ne with
      | inl => 
        unfold bSearch
        simp
        rename q.arrVal = target => curr_eq_tgt
        intro succ_ne_tgt
        unfold searchSucc at succ_ne_tgt
        split at succ_ne_tgt
        rename q.lo ≠ q.hi ∧ q.arrVal ≠ target => not_done
        exact absurd curr_eq_tgt not_done.right
        contradiction
      | inr => 
        rename ¬q.arrVal = target => curr_ne_tgt
        have fp : searchSucc is target q = q := h_invalid curr_ne_tgt
        rw [fp] at h_succ_valid
        have not_fp : searchSucc is target q ≠ q := h_succ_valid.right
        exact absurd fp not_fp
    unfold Stream.valid at succ_invalid
    unfold bSearch at succ_invalid
    simp at succ_invalid
    exact absurd (succ_invalid h_succ_valid.left) h_succ_valid.right


lemma skip_to_succ_monotone (is : Array α) (target : α) (x : BSearchState α) (i : ℕ) : x.searchIndex ≤ (skipTo is target (searchSucc is target x) x i).searchIndex := by
    unfold skipTo
    simp
    split
    


lemma skip_to_is_increasing (is : Array α) (target : α) (q : BSearchState α) (pred : BSearchState α) (i : ℕ) : let search := bSearch is target
  search.index' q ≤ search.index' (skipTo is target q q i) := by
  simp
  unfold Stream.index'
  split
  rename Stream.valid (bSearch is target) q => h_valid
  split
  rename Stream.valid (bSearch is target) (skipTo is target q q i) => h_succ_valid
  unfold skipTo
  simp
  split
  rename q.searchIndex < i ∧ ¬searchSucc is target q = q => h_not_done_skipping
  unfold bSearch
  simp
  


  
  
  
  
  
  
  -- have : ∃x, (skipTo is target q q i) = searchSucc is target x := sorry -- how to show this?
  -- maybe write an inductive proof like this https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Guidance.20on.20proof.20methods.3A.20pattern.20matching.20vs.2E.20induction/near/384492767






theorem bSearchIsMonotonic [LT α] [DecidableLT α] [Inhabited α] [BEq α] (is : Array α) (target : α) : (bSearch is target).IsMonotonic := by 
  intro q hv i
  simp
  -- how to break this if/then?
  split
  rename q.searchIndex < i.fst => indexLtI
  unfold Stream.index'
  split
  rename Stream.valid (bSearch is target) q => hqValid
  split
  unfold skipTo
  repeat simp
  split
  sorry

  -- hmm, maybe i need to prove that skipTo is increasing





  
    



  
  
  

  
  






variable {ι : Type} [LinearOrder ι] {α : Type _}

@[simps]
def Stream.add [Zero α] [Add α] (a b : Stream ι α) : Stream ι α
    where
  σ := a.σ × b.σ
  valid s := a.valid s.1 ∨ b.valid s.2
  ready s :=
    a.toOrder' s.1 ≤ b.toOrder' s.2 ∧ a.ready s.1 ∨ b.toOrder' s.2 ≤ a.toOrder' s.1 ∧ b.ready s.2
  skip p _hp i := (a.skip' p.1 i, b.skip' p.2 i)
  index s h := Option.get (min (α := WithTop ι) (a.index' s.1) (b.index' s.2)) (by simpa)
  value s _h :=
    (if a.toOrder' s.1 ≤ b.toOrder' s.2 then a.value' s.1 else 0) +
      if b.toOrder' s.2 ≤ a.toOrder' s.1 then b.value' s.2 else 0
#align Stream.add Etch.Verification.Stream.add

/- These two are necessary for `ext` to work on Lean 4… -/
@[ext]
theorem Prod.Lex.ext {α β} {p q : α ×ₗ β} (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) :
    p = q := Prod.ext h₁ h₂
@[ext]
def Stream.add_σ_ext [Zero α] [Add α] (a b : Stream ι α) (p q : (a.add b).σ) (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) :
    p = q := Prod.ext h₁ h₂

section IndexLemmas

variable [Zero α] [Add α]

@[simp]
theorem add_index_eq_min {a b : Stream ι α} (q : (a.add b).σ) :
    (a.add b).index' q = min (a.index' q.1) (b.index' q.2) := by
  by_cases H : (a.add b).valid q
  · rw [Stream.index'_val H, Stream.add_index]
    exact Option.coe_get _
  · simp [H, not_or.mp H]
#align add_index_eq_min Etch.Verification.add_index_eq_min

theorem valid_of_toOrder_lt {a b : Stream ι α} {qa : a.σ} {qb : b.σ}
    (h : a.toOrder' qa < b.toOrder' qb) : a.valid qa := by
  contrapose! h
  by_cases hb : b.valid qb
  · rw [Prod.Lex.le_iff']
    left
    simpa [h]
  · simp [Stream.toOrder', h, hb]
#align valid_of_to_order_lt Etch.Verification.valid_of_toOrder_lt

@[simp]
theorem add_skip_fst {a b : Stream ι α} (q i) : ((a.add b).skip' q i).fst = a.skip' q.1 i := by
  simp only [Stream.skip']
  split_ifs with h₁ h₂ h₂
  · simp [h₂]
  · simp [h₂]
  · cases h₁ (Or.inl h₂)
  · rfl
#align add_skip_fst Etch.Verification.add_skip_fst

@[simp]
theorem add_skip_snd {a b : Stream ι α} (q i) : ((a.add b).skip' q i).snd = b.skip' q.2 i := by
  simp only [Stream.skip']
  split_ifs with h₁ h₂ h₂
  · simp [h₂]
  · simp [h₂]
  · cases h₁ (Or.inr h₂)
  · rfl
#align add_skip_snd Etch.Verification.add_skip_snd

theorem of_toOrder_eq {a b : Stream ι α} (q : (a.add b).σ) (h : a.toOrder' q.1 = b.toOrder' q.2) :
    (¬(a.add b).valid q ∧ ¬a.valid q.1 ∧ ¬b.valid q.2) ∨
      ((a.add b).valid q ∧ a.valid q.1 ∧ b.valid q.2 ∧
        (a.ready q.1 ↔ b.ready q.2) ∧ a.index' q.1 = b.index' q.2) := by
  have : a.index' q.1 = b.index' q.2 := by simpa using congr_arg Prod.fst h
  by_cases H : (a.add b).valid q
  · right
    obtain ⟨hv₁, hv₂⟩ : a.valid q.1 ∧ b.valid q.2 := by
      simp only [← Stream.index'_lt_top_iff] at H⊢
      simpa [this, -Stream.index'_lt_top_iff] using H
    refine ⟨H, hv₁, hv₂, ?_, this⟩
    simpa [hv₁, hv₂] using congr_arg Prod.snd h
  · left
    exact ⟨H, not_or.mp H⟩
#align of_to_order_eq Etch.Verification.of_toOrder_eq

theorem add_toOrder_eq_min {a b : Stream ι α} (q : (a.add b).σ) :
    (a.add b).toOrder' q = min (a.toOrder' q.1) (b.toOrder' q.2) := by
  rcases lt_trichotomy (a.toOrder' q.1) (b.toOrder' q.2) with h | h | h
  · rw [min_eq_left h.le]
    have := Prod.Lex.fst_le_of_le h.le
    ext : 1
    · simpa using Prod.Lex.fst_le_of_le h.le
    · simp [valid_of_toOrder_lt h, h.le, h.not_le]
  · rcases of_toOrder_eq _ h with (⟨H, hv₁, hv₂⟩ | ⟨H, _hv₁, hv₂, hr, hi⟩)
    · simp [Stream.toOrder', H, hv₁, hv₂]
    ext : 1
    · simp [h, hi]
    simp [Stream.toOrder'_val_snd H, h, Stream.toOrder'_val_snd hv₂, hr]
  · rw [min_eq_right h.le]
    ext : 1
    · simpa using Prod.Lex.fst_le_of_le h.le
    · simp [valid_of_toOrder_lt h, h.le, h.not_le]
#align add_to_order_eq_min Etch.Verification.add_toOrder_eq_min

theorem add_toOrder_left {a b : Stream ι α} {q : (a.add b).σ} (hq hq')
    (ha : a.toOrder' q.1 ≤ b.toOrder' q.2) : (a.add b).toOrder q hq = a.toOrder q.1 hq' :=
  coeLex_injective (by simpa [add_toOrder_eq_min] )
#align add_to_order_left Etch.Verification.add_toOrder_left

theorem add_toOrder_right {a b : Stream ι α} {q : (a.add b).σ} (hq hq')
    (ha : b.toOrder' q.2 ≤ a.toOrder' q.1) : (a.add b).toOrder q hq = b.toOrder q.2 hq' :=
  coeLex_injective (by simpa [add_toOrder_eq_min] )
#align add_to_order_right Etch.Verification.add_toOrder_right

instance Stream.add.isBounded (a b : Stream ι α) [IsBounded a] [IsBounded b] :
    IsBounded (a.add b) :=
  IsBounded.mk'
    ⟨Prod.rprodEq a.wfRel b.wfRel,
      fun q i => by
      rcases a.wf_valid' q.1 i with (h | ⟨ha₁, ha₂⟩)
      · left
        left
        simp only [add_skip_fst, add_skip_snd]
        exact ⟨h, (b.wf_valid' q.2 i).imp_right And.right⟩
      rcases b.wf_valid' q.2 i with (h | ⟨hb₁, hb₂⟩)
      · left
        right
        simp only [add_skip_fst, add_skip_snd]
        exact ⟨h, (a.wf_valid' q.1 i).imp_right And.right⟩
      right; constructor
      · rw [add_toOrder_eq_min, lt_min_iff]
        constructor <;> assumption
      · ext <;> simpa⟩
#align Stream.add.is_bounded Etch.Verification.Stream.add.isBounded

theorem add_mono {a b : Stream ι α} (ha : a.IsMonotonic) (hb : b.IsMonotonic) :
    (a.add b).IsMonotonic := by
  intro q hv i
  simp only [add_index_eq_min]
  exact min_le_min (ha.skip' _ _) (hb.skip' _ _)
#align add_mono Etch.Verification.add_mono

theorem add_strict_mono {a b : Stream ι α} (ha : a.IsStrictMono) (hb : b.IsStrictMono) :
    (a.add b).IsStrictMono :=
  ⟨add_mono ha.1 hb.1, fun q hq i hi hr =>
    ne_of_lt
      (by
        replace hi : min (a.toOrder' q.1) (b.toOrder' q.2) ≤ coeLex i;
        · rwa [← add_toOrder_eq_min, ← Stream.coeLex_toOrder hq, coeLex_le_iff]
        rcases lt_trichotomy (a.toOrder' q.1) (b.toOrder' q.2) with (h | h | h)
        · replace hr : a.ready q.1 := by simpa [h.le, h.not_le] using hr
          have hqa : a.valid q.1 := valid_of_toOrder_lt h
          replace hi : a.toOrder q.1 hqa ≤ i
          · rw [min_eq_left h.le] at hi
            rwa [← coeLex_le_iff, Stream.coeLex_toOrder]
          have : a.index' q.1 < b.index' q.2 := by
            refine' Prod.Lex.fst_lt_of_lt_of_le h _
            simp [hqa, hr]
          simp only [add_index_eq_min, min_eq_left this.le, Stream.add_skip, add_index_eq_min,
            lt_min_iff, Stream.skip'_val hqa]
          constructor
          · exact ha.lt _ _ _ hi hr
          · refine' this.trans_le _
            apply hb.1.skip'
        · obtain ⟨hv₀, hv₁, hv₂, hr_iff, hind⟩ :=
            (of_toOrder_eq _ h).resolve_left fun h' => h'.1 hq
          simp only [add_index_eq_min, hind, min_self, Stream.add_skip, lt_min_iff]
          obtain ⟨hr₁, hr₂⟩ : a.ready q.1 ∧ b.ready q.2 := by
            constructor <;> simpa [h, hr_iff] using hr
          constructor
          · rw [← hind, Stream.skip'_val hv₁]
            rw [← h, min_self, ← Stream.coeLex_toOrder hv₁, coeLex_le_iff] at hi
            exact ha.lt _ _ _ hi hr₁
          · rw [Stream.skip'_val hv₂]
            rw [h, min_self, ← Stream.coeLex_toOrder hv₂, coeLex_le_iff] at hi
            exact hb.lt _ _ _ hi hr₂
        · replace hr : b.ready q.2 := by simpa [h.le, h.not_le] using hr
          have hqb : b.valid q.2 := valid_of_toOrder_lt h
          replace hi : b.toOrder q.2 hqb ≤ i
          · rw [min_eq_right h.le] at hi
            rwa [← coeLex_le_iff, Stream.coeLex_toOrder]
          have : b.index' q.2 < a.index' q.1 := by
            refine' Prod.Lex.fst_lt_of_lt_of_le h _
            simp [hqb, hr]
          simp only [add_index_eq_min, min_eq_right this.le, Stream.add_skip, add_index_eq_min,
            lt_min_iff, Stream.skip'_val hqb]
          constructor
          swap
          · exact hb.lt _ _ _ hi hr
          · refine' this.trans_le _
            apply ha.1.skip')⟩
#align add_strict_mono Etch.Verification.add_strict_mono

theorem Stream.add_map {β : Type _} [Zero β] [Add β] (f : α → β)
    (f_add : ∀ x y, f (x + y) = f x + f y) (f_zero : f 0 = 0) (q r : Stream ι α) :
    (q.add r).map f = (q.map f).add (r.map f) := by
  ext <;> solve_refl
  simp only [f_add, apply_ite f, f_zero, Stream.map_value' f f_zero]
#align Stream.add_map Etch.Verification.Stream.add_map

end IndexLemmas

section ValueLemmas

variable [AddCommMonoid α]

theorem Stream.add.eval₀_eq_left {a b : Stream ι α} {q : (a.add b).σ} (hq : (a.add b).valid q)
    (H : a.toOrder' q.1 < b.toOrder' q.2) :
    (a.add b).eval₀ q hq = a.eval₀ q.1 (valid_of_toOrder_lt H) := by
  have := add_toOrder_left hq (valid_of_toOrder_lt H) H.le
  have hr : (a.add b).ready q ↔ a.ready q.1 := by simpa [-add_ready] using congr_arg Prod.snd this
  simp only [Stream.eval₀, ← Stream.value'_val, dite_eq_ite]
  rw [hr]
  split_ifs with hr'
  swap
  · rfl
  · congr 1
    · simpa using congr_arg Prod.fst this
    · simp [(a.add b).value'_val (Or.inl ⟨H.le, hr'⟩), H.le, H.not_le]
#align Stream.add.eval₀_eq_left Etch.Verification.Stream.add.eval₀_eq_left

theorem Stream.add.eval₀_eq_right {a b : Stream ι α} {q : (a.add b).σ} (hq : (a.add b).valid q)
    (H : b.toOrder' q.2 < a.toOrder' q.1) :
    (a.add b).eval₀ q hq = b.eval₀ q.2 (valid_of_toOrder_lt H) := by
  have := add_toOrder_right hq (valid_of_toOrder_lt H) H.le
  have hr : (a.add b).ready q ↔ b.ready q.2 := by simpa [-add_ready] using congr_arg Prod.snd this
  simp only [Stream.eval₀, ← Stream.value'_val, dite_eq_ite]
  rw [hr]
  split_ifs with hr'
  swap
  · rfl
  · congr 1
    · simpa using congr_arg Prod.fst this
    · simp [(a.add b).value'_val (Or.inr ⟨H.le, hr'⟩), H.le, H.not_le]
#align Stream.add.eval₀_eq_right Etch.Verification.Stream.add.eval₀_eq_right

lemma Stream.add_vlaue' {a b : Stream ι α} {q : (a.add b).σ}
  (H : a.toOrder' q.1 = b.toOrder' q.2) (hr₁ : a.ready q.1) (hr₂ : b.ready q.2) :
    (a.add b).value' q = a.value' q.1 + b.value' q.2 := by
  simp [value', H, hr₁, hr₂]
  

theorem Stream.add.eval₀_eq_both {a b : Stream ι α} {q : (a.add b).σ} (hq : (a.add b).valid q)
    (H : a.toOrder' q.1 = b.toOrder' q.2) (hv₁ hv₂) (hr : a.ready q.1 ↔ b.ready q.2)
    (hi : a.index q.1 hv₁ = b.index q.2 hv₂) :
    (a.add b).eval₀ q hq = a.eval₀ q.1 hv₁ + b.eval₀ q.2 hv₂ := by
  have : (a.add b).ready q ↔ b.ready q.2 := by simp [H, hr]
  simp only [Stream.eval₀, ← Stream.value'_val, dite_eq_ite]
  rw [this, hr]
  split_ifs with hr'
  swap
  · simp
  · rw [hi, ← Finsupp.single_add]
    congr 1
    · simp only [add_index, Stream.index'_val hv₁, hi, Stream.index'_val hv₂, min_self]
      exact Option.get_some _ _
    · rw [Stream.add_vlaue' H (hr.mpr hr') hr']
      
#align Stream.add.eval₀_eq_both Etch.Verification.Stream.add.eval₀_eq_both

theorem add_spec (a b : Stream ι α) [IsLawful a] [IsLawful b] (q : (a.add b).σ) :
    (a.add b).eval q = a.eval q.1 + b.eval q.2 := by
  apply (a.add b).wf.induction q
  clear q; intro q ih
  rcases lt_trichotomy (a.toOrder' q.1) (b.toOrder' q.2) with (h | h | h)
  · have hv : a.valid q.1 := valid_of_toOrder_lt h
    have hq : (a.add b).valid q := Or.inl hv
    rw [(a.add b).eval_valid q hq, ih _ ((a.add b).next_wf _ hq), Stream.next_val hq,
      Stream.add_skip, b.skip'_lt_toOrder, add_toOrder_left hq hv h.le,
      Stream.skip'_val hv, a.eval_valid _ hv, add_assoc, Stream.add.eval₀_eq_left hq h,
      Stream.next_val hv]
    simpa [add_toOrder_eq_min]
  · rcases of_toOrder_eq _ h with (⟨H, hv₁, hv₂⟩ | ⟨hq, hv₁, hv₂, hr, hi⟩)
    · simp [H, hv₁, hv₂]
    obtain ⟨t₀, t₁⟩ :
      (a.add b).toOrder q hq = a.toOrder q.1 hv₁ ∧ (a.add b).toOrder q hq = b.toOrder q.2 hv₂ :=
      by constructor <;> apply_fun coeLex using coeLex_injective <;> simp [add_toOrder_eq_min, h]
    simp only [Stream.index'_val, hv₁, hv₂, WithTop.coe_eq_coe] at hi
    rw [(a.add b).eval_valid q hq, ih _ ((a.add b).next_wf _ hq), Stream.next_val hq,
      Stream.add_skip, Stream.add.eval₀_eq_both hq h hv₁ hv₂ hr hi,
      show ∀ w x y z : ι →₀ α, w + x + (y + z) = w + y + (x + z) by intros; abel]
    dsimp only
    congr 1
    · rw [a.eval_valid _ hv₁, Stream.next_val hv₁, t₀, Stream.skip'_val hv₁]
    · rw [b.eval_valid _ hv₂, Stream.next_val hv₂, t₁, Stream.skip'_val hv₂]
  · have hv : b.valid q.2 := valid_of_toOrder_lt h
    have hq : (a.add b).valid q := Or.inr hv
    rw [(a.add b).eval_valid q hq, ih _ ((a.add b).next_wf _ hq), Stream.next_val hq,
      Stream.add_skip, a.skip'_lt_toOrder, add_toOrder_right hq hv h.le,
      Stream.skip'_val hv, b.eval_valid _ hv, add_left_comm, Stream.add.eval₀_eq_right hq h,
      Stream.next_val hv]
    simpa [add_toOrder_eq_min]
#align add_spec Etch.Verification.add_spec

instance (a b : Stream ι α) [IsLawful a] [IsLawful b] : IsLawful (a.add b) where
  mono := add_mono a.mono b.mono
  skip_spec q hq i j hj := by
    simp only [add_spec]; dsimp
    congr 1 <;> rwa [Stream.skip'_spec]

instance (a b : Stream ι α) [IsStrictLawful a] [IsStrictLawful b] :
    IsStrictLawful (a.add b) where
  strictMono := add_strict_mono a.strictMono b.strictMono

end ValueLemmas

end
end Etch.Verification
