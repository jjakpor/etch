import Mathlib.Order.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

abbrev i := ℕ
variable (mid : i → i → Option i) (p : i → Bool)

def mid_spec := ∀ l r m, mid l r = some m → l < m ∧ m < r
def mid_spec_converse := ∀l r, (∃m, l < m ∧ m < r) → ∃m', mid l r = some m'
variable (hmid : mid_spec mid)


def binarySearch (pair : i × i) : i × i :=
  match mid_is_some_m : mid pair.fst pair.snd with
  | none => pair
  | some m =>
      let ⟨a, b⟩ : pair.fst < m ∧ m < pair.snd := hmid pair.fst pair.snd m mid_is_some_m
      let lt := a.trans b
      have : m - pair.fst < pair.snd - pair.fst := tsub_lt_tsub_right_of_le (Nat.le_of_lt a) b
      have : pair.snd - m < pair.snd - pair.fst := Nat.sub_lt_sub_left lt a
      if p m then binarySearch (pair.fst, m) else binarySearch (m, pair.snd)
termination_by _ pair => pair.snd - pair.fst


def zMid (a b : i):=
  let m := a + (b - a) / 2
  if a < m ∧ m < b then some m else none
-- #eval binarySearch zMid (fun x => x > 7) sorry (1, 6)

def has_between (pair : i × i) := ∃m, pair.fst < m ∧ m < pair.snd


lemma not_mid_spec_converse_antecedent_on_termination :
  ∀l r, (has_between (binarySearch mid p hmid (l, r)))

theorem adjacent (pair : i × i) : ∃n, binarySearch mid p hmid pair = (n, n + 1) := by
  sorry



structure result_spec (pair : i × i) where
  snd_eq_succ_fst : pair.snd = pair.fst + 1
  not_p_fst : ¬p pair.fst
  p_snd : p pair.snd

def midFloat  (l : Float)  (r : Float): Option Float := if (r - l < 0.001) then none else some ((l + r) / 2)
-- #eval binarySearch midFloat (fun x => x^2 >= 2) (1.0, 2.0)




structure invariant (pair : i × i) : Prop where
  lt : pair.fst < pair.snd
  not_pl : ¬p pair.fst
  pr : p pair.snd


-- TODO: fix later
theorem bsearch_preserves_invariant (l : i) (r : i) :
  invariant p (l, r) → mid_spec mid → invariant p (binarySearch mid p (l, r)) := by
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
