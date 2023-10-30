import Mathlib.Init.Algebra.Order
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

variable (mid : Int → Int → Option Int) (p : Int → Bool)

def binarySearchStep (pair : ℤ × ℤ) : ℤ × ℤ :=
  match mid pair.fst pair.snd with
  | none => pair
  | some m => if p m then (pair.fst, m) else (m, pair.snd)

def mid_spec := ∀l r m, mid l r = some m → l < m ∧ m < r

structure invariant (pair : ℤ × ℤ) : Prop where
  lt : pair.fst < pair.snd
  not_pl : ¬p pair.fst
  pr : p pair.snd

theorem bsearch_preserves_invariant (l : ℤ) (r : ℤ) :
  invariant p (l, r) → mid_spec mid → invariant p (binarySearchStep mid p (l, r)) := by
  intros hinv hmid
  dsimp only [binarySearchStep]
  set optM := mid l r
  cases h : optM
  . dsimp
    assumption
  . dsimp
    rename_i m
    have mid_between := hmid l r m h
    split
    . constructor
      . dsimp
        exact mid_between.left
      . dsimp
        cases hinv with
        | mk lt not_pl pr => assumption
      . assumption
    . constructor
      . dsimp
        exact mid_between.right
      . assumption
      . dsimp
        cases hinv with
        | mk lt not_pl pr => assumption
