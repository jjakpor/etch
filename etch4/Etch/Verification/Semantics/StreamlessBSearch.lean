import Mathlib.Order.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Aesop

abbrev Pair := ℕ × ℕ

variable (pair : Pair)

abbrev Proper := pair.1 < pair.2
abbrev Between m := pair.1 < m ∧ m < pair.2

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
    | none => simp only [imp_self]
    | some m =>
      simp only [hm]
      intro inv
      apply h
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

lemma not_pred_zero [LinearOrder α] (arr : List α) (target : α) : searchPred arr target 0 = false := rfl

lemma pred_size [LinearOrder α] (arr : List α) (target : α) : searchPred arr target (arr.length + 1) = true := by
  simp [searchPred]

def searchMid (p : Pair) : Option { m // Between p m } := if h : p.snd - p.fst > 1 then some ⟨p.fst + (p.snd - p.fst) / 2, by
    unfold Between
    simp
    apply And.intro
    -- I can tell that h is important, which is why I named it, but I don't know how to manipulate these inequalities
    . sorry
    . sorry
  ⟩ else none

def returnIndex [LinearOrder α] (arr : List α) (target : α) := (binarySearch (searchPred arr target) searchMid (0, arr.length + 1)).fst


structure InBoundsEq (arr : List α) (target : α) (j : ℕ) : Prop where
  inBounds : j < arr.length
  eq : arr[j] = target
-- Assuming return index is in bounds

/- Todo: prove on paper-/
theorem bsearch_finds_target_if_target_exists [LinearOrder α] (arr : List α) (target : α) : (∃j, InBoundsEq arr target j) → InBoundsEq arr target (returnIndex arr target) := by
  intro exists_j
  constructor
  . unfold returnIndex
    done
  . unfold returnIndex
    done
