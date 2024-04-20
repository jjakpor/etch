import Mathlib.Order.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Aesop

abbrev Pair := ℕ × ℕ

abbrev Proper (pair : Pair) := pair.1 < pair.2
abbrev Between (pair : Pair) m := pair.1 < m ∧ m < pair.2

def size : Pair → ℕ := fun p => p.2 - p.1

variable (pred : ℕ → Bool)

def searchStep (pair : Pair) (h : pair.fst < m ∧ m < pair.snd) : { p : Pair // size p < size pair } :=
  if pred m
    then ⟨(pair.fst, m), let ⟨a, b⟩ := h; tsub_lt_tsub_right_of_le (Nat.le_of_lt a) b⟩
    else ⟨(m, pair.snd), let ⟨a, b⟩ := h; Nat.sub_lt_sub_left (a.trans b) a⟩

variable (mid' : (p : Pair) → Option { m // Between p m })

def binarySearch (pair : Pair) : Pair :=
  match mid' pair with
  | none => pair
  | some ⟨_, hm⟩ =>
      let ⟨new, _⟩ := searchStep pred pair hm
      binarySearch new
termination_by _ pair => pair.snd - pair.fst

def mid'_spec_converse := ∀ p, mid' p = none → p.2 ≤ p.1 + 1

theorem searchStep_lt_of_lt {pred pair between} (h : Proper pair) : Proper (searchStep pred pair between (m := m)) := by
  unfold searchStep; aesop

theorem adjacent (hmid : mid'_spec_converse mid') (pair : Pair) (lt : Proper pair) : ∃ n, binarySearch pred mid' pair = (n, n + 1) := by
  revert lt
  have size_wf := InvImage.wf size WellFoundedRelation.wf
  induction pair using WellFounded.induction
  . exact size_wf
  . rename_i pair h
    intro lt
    unfold binarySearch
    cases hm : mid' pair with
    | none => exact ⟨pair.1, by simp only [← Nat.le_antisymm (hmid _ hm) lt]⟩
    | some new =>  apply h _ (searchStep _ _ new.property).property (searchStep_lt_of_lt lt)

abbrev Invariant (pred : ℕ → Bool) (pair : Pair) := ¬pred pair.fst ∧ pred pair.snd

theorem invariant (inv : Invariant pred pair) : Invariant pred (binarySearch pred mid' pair) := by
  revert inv
  have size_wf := InvImage.wf size WellFoundedRelation.wf

  induction pair using WellFounded.induction
  . exact size_wf
  . rename_i pair h
    unfold binarySearch
    cases hm : mid' pair with
    | none => intro; assumption
    | some m =>
      simp only [hm]
      intro inv
      apply h
      -- decreasing_tactic
      . exact (searchStep pred pair m.property).property
      . unfold searchStep
        split <;> dsimp only
        . rename_i pred_m
          exact ⟨inv.left, pred_m⟩
        . rename_i not_pred_m
          exact ⟨not_pred_m, inv.right⟩

-- searching for target x, using predicate y > x, first elem of returned pair is last value <= x, second elem is virst val > x
def searchPred [LinearOrder α] (arr : List α) (target : α) (i : ℕ) : Bool :=
  match i with
  | 0 => false
  | i + 1 => if h: i < arr.length then arr[i]'h > target else true


lemma sum_div {a b c : ℕ} : a/c + b/c ≤ (a + b) / c  := sorry -- TODO: find in mathlib or prove manually (as an exercise)

def searchMid (p : Pair) : Option { m // Between p m } := if h : p.snd - p.fst > 1 then some ⟨p.fst + (p.snd - p.fst) / 2, by
    unfold Between
    simp
    apply And.intro
    . have ⟨n, hn⟩: ∃n, p.snd - p.fst = 2 + n := sorry
      rw [hn]
      have := @sum_div 2 n 2
      rw [Nat.div_self] at this
      . calc
          0 < 1 := by simp
          _ ≤ 1 + n /2 := by simp
          1 + n / 2 ≤ (2 + n) / 2 := this
        done
      . simp
      done
    . sorry
  ⟩ else none

inductive SearchPosition
| before
| index (i : ℕ)
| after

def returnIndex [LinearOrder α] (arr : List α) (target : α) :=
  (binarySearch (searchPred arr target) searchMid (0, arr.length + 1)).fst

/-
def searchPred [LinearOrder α] (arr : List α) (target : α) (i : ℕ) : Bool :=
  match i with
  | 0 => false
  | i + 1 => if h: i < arr.length then arr[i]'h > target else true
-/
def returnIndex' [LinearOrder α] (arr : List α) (target : α) : SearchPosition :=
  let encoded := (binarySearch (searchPred arr target) searchMid (0, arr.length + 1)).fst
  match encoded with
  | 0 => .before
  | i + 1 => if i < arr.length then .index i else .after

abbrev InBoundsEq' (arr : List α) (target : α)

theorem Nat.pred_lt_of_le {n m : ℕ } (gt_zero : 0 < n) (h : n ≤ m) : n.pred < m := by
  cases Nat.pred n with
  | zero => calc
      0 < n := gt_zero
      n ≤ m := h
  | succ x => sorry


abbrev InBoundsEq (arr : List α) (target : α) (j : ℕ) : Prop :=
  0 < j ∧ j ≤ arr.length ∧ arr[j-1]'(by sorry) = target


abbrev Sorted [LinearOrder α] (arr : List α) : Prop :=
  ∀(i j : Nat) (h : i < arr.length ∧ j < arr.length), arr[i]'h.left ≤ arr[j]'h.right

variable [LinearOrder α] (arr : List α) (target : α)

lemma inv_ret_pair : Invariant (searchPred arr target) (binarySearch (searchPred arr target) searchMid (0, List.length arr + 1)) := by
  have inv_in : Invariant (searchPred arr target) (0, List.length arr + 1) := by
    unfold Invariant
    apply And.intro
    . simp only [Bool.not_eq_true]
      rfl
    . unfold searchPred
      simp only [Nat.add_eq, add_zero, lt_self_iff_false, List.getElem_eq_get, gt_iff_lt, dite_false]
  exact @invariant (searchPred arr target) (searchMid) (0, List.length arr + 1) inv_in


lemma not_search_pred_ret : ¬searchPred arr target (returnIndex arr target) := (inv_ret_pair arr target).left

lemma search_pred_succ_ret : searchPred arr target (returnIndex arr target + 1) := by
  unfold returnIndex
  sorry
  -- use adjacent



lemma arr_at_succ_ret_gt_arr_at_target [LinearOrder α] (arr : List α) (target : α) : arr[(returnIndex arr target) + 1]'sorry > target := by
  unfold returnIndex
  dsimp only [gt_iff_lt]
  sorry



-- lemma not_eq_of_not_in_bounds_eq_in_bounds [LinearOrder α] (arr : List α) (target : α) (j : ℕ) :

theorem  bsearch_finds_target_if_target_exists' [LinearOrder α] (arr : List α) (target : α) : -- This is to try SearchPosition
Sorted arr → (∃j, InBoundsEq arr target j)
→ InBoundsEq arr target (returnIndex arr target) := by
  intro sorted
  contrapose
  intro not_in_bounds_eq_result
  rw [not_exists]
  intro j
  obtain j_in_bounds | j_not_in_bounds := Classical.em (j < arr.length)
  . obtain j_lt_ret | j_eq_ret | ret_lt_j := Nat.lt_trichotomy j (returnIndex arr target)
    . obtain ret_in_bounds | ret_not_in_bounds := Classical.em (returnIndex arr target < arr.length)
      . unfold Sorted at sorted
        have h : arr[j]'j_in_bounds ≤ arr[returnIndex arr target]'ret_in_bounds := sorted j (returnIndex arr target) ⟨j_in_bounds, ret_in_bounds⟩
        have h' : arr[returnIndex arr target] ≠ target := sorry -- finish lemma above
        have not_search_pred_ret := not_search_pred_ret arr target
        /-
        def searchPred [LinearOrder α] (arr : List α) (target : α) (i : ℕ) : Bool :=
        match i with
        | 0 => false
        | i + 1 => if h: i < arr.length then arr[i]'h > target else true
        -/
        unfold InBoundsEq
        rw [not_and_or]
        right
        rw [not_and_or]
        right
        -- oops, maybe off by one
      . sorry
    . conv in j => rw [j_eq_ret]
      assumption
    . have ret_in_bounds : (returnIndex arr target) + 1 ≤ arr.length :=
        calc
        returnIndex arr target ≤ j := Nat.le_of_lt ret_lt_j
        j < List.length arr := j_in_bounds
      unfold InBoundsEq
      rw [not_and_or]
      rw [not_and_or]
      right
      right
      unfold InBoundsEq at not_in_bounds_eq_result
      rw [not_and_or] at not_in_bounds_eq_result
      rw [not_and_or] at not_in_bounds_eq_result
      cases not_in_bounds_eq_result
      . sorry
      . rename_i not_in_bounds_or_not_eq
        cases not_in_bounds_or_not_eq
        . sorry -- calc proof here
        . sorry
  . sorry


theorem  bsearch_finds_target_if_target_exists [LinearOrder α] (arr : List α) (target : α) :
Sorted arr → (∃j, InBoundsEq arr target j)
→ InBoundsEq arr target (returnIndex arr target) := by
  intro sorted
  contrapose
  intro not_in_bounds_eq_result
  rw [not_exists]
  intro j
  obtain j_in_bounds | j_not_in_bounds := Classical.em (j < arr.length)
  . obtain j_lt_ret | j_eq_ret | ret_lt_j := Nat.lt_trichotomy j (returnIndex arr target)
    . obtain ret_in_bounds | ret_not_in_bounds := Classical.em (returnIndex arr target < arr.length)
      . unfold Sorted at sorted
        have h : arr[j]'j_in_bounds ≤ arr[returnIndex arr target]'ret_in_bounds := sorted j (returnIndex arr target) ⟨j_in_bounds, ret_in_bounds⟩
        have h' : arr[returnIndex arr target] ≠ target := sorry -- finish lemma above
        have not_search_pred_ret := not_search_pred_ret arr target
        /-
        def searchPred [LinearOrder α] (arr : List α) (target : α) (i : ℕ) : Bool :=
        match i with
        | 0 => false
        | i + 1 => if h: i < arr.length then arr[i]'h > target else true
        -/
        unfold InBoundsEq
        rw [not_and_or]
        right
        rw [not_and_or]
        right
        -- oops, maybe off by one
      . sorry
    . conv in j => rw [j_eq_ret]
      assumption
    . have ret_in_bounds : (returnIndex arr target) + 1 ≤ arr.length :=
        calc
        returnIndex arr target ≤ j := Nat.le_of_lt ret_lt_j
        j < List.length arr := j_in_bounds
      unfold InBoundsEq
      rw [not_and_or]
      rw [not_and_or]
      right
      right
      unfold InBoundsEq at not_in_bounds_eq_result
      rw [not_and_or] at not_in_bounds_eq_result
      rw [not_and_or] at not_in_bounds_eq_result
      cases not_in_bounds_eq_result
      . sorry
      . rename_i not_in_bounds_or_not_eq
        cases not_in_bounds_or_not_eq
        . sorry -- calc proof here
        . sorry
  . sorry
