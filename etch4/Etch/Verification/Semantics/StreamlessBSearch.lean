import Mathlib.Order.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

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
  unfold searchStep
  split
  . dsimp only [gt_iff_lt]
    exact between.left -- why doesn't assumption work?
  . dsimp only [gt_iff_lt]
    exact between.right

theorem adjacent (hmid : mid'_spec_converse mid') (pair : Pair) (lt : Proper pair) : ∃ n, binarySearch pred mid' pair = (n, n + 1) := by
  revert lt
  have := InvImage.wf size WellFoundedRelation.wf
  induction pair using WellFounded.induction
  . exact this
  . rename_i pair h
    intro lt
    have h' := h pair
    unfold binarySearch
    split
    . rename_i mid_is_none
      have snd_le_fst : pair.2 ≤ pair.1 + 1 := hmid pair mid_is_none
      unfold Proper at lt
      use pair.fst
      have lt_or_eq := Nat.eq_or_lt_of_le snd_le_fst
      cases lt_or_eq
      . rename_i snd_is_fst_succ
        have :  pair = (pair.fst, pair.snd) := by simp
        rw [snd_is_fst_succ] at this
        assumption
      . rename_i snd_lt_fst_succ
        have snd_eq_fst : pair.fst = pair.snd := by
          have snd_le_fst := Nat.le_of_lt_succ snd_lt_fst_succ
          have := (@Nat.not_lt pair.fst pair.snd).mpr snd_le_fst
          contradiction
        have snd_ne_fst : pair.fst ≠ pair.snd := ne_of_lt lt
        contradiction
    . dsimp only
      sorry
