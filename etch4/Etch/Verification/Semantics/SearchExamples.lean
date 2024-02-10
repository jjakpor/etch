/- These definitions are less pedantic than those in Streamless BSearch-/
import Mathlib.Order.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Aesop

/- The domain of the function we're scanning. -/
variable (ι : Type) [LinearOrder ι]

/- The predicate being used by the binary search. -/
variable (pred : ι → Bool)
abbrev Pair' := ι × ι

/- A single step of binary search. -/
def searchStep' (pair : Pair' ι) (m : ι): Pair' ι :=
  if pred m
    then (pair.fst, m)
    else (m, pair.snd)

/- A function that optionally returns some m between the elements of a pair.
   This function should satisfy mid' p = some m ↔ p.2 > p1
-/
variable (mid' : (p : Pair' ι) → Option ι)

partial def binarySearch' (pair : Pair' ι) : Pair' ι :=
  match mid' pair with
  | none => pair
  | some m =>
    binarySearch' (searchStep' ι pred pair m)

def searchPred [LinearOrder α] (arr : List α) (target : α) (i : ℕ) : Bool :=
  match i with
  | 0 => false
  | i + 1 => if h: i < arr.length then arr[i]'h > target else true


def searchMid (p : Pair' ℕ) : Option ℕ :=
  if h : p.snd - p.fst > 1 then some (p.fst + (p.snd - p.fst) / 2) else none

def exampleArr : List ℕ := [1, 2, 4, 8, 16]

#eval binarySearch' ℕ (searchPred exampleArr 2) searchMid (0, exampleArr.length + 1)

def floatMid (ε : Float) (p : Pair' Float) : Option Float :=
  if p.snd - p.fst > ε then some (p.fst + (p.snd - p.fst) / 2) else none
def floatPred (target : Float) (x : Float) : Bool := x * x > target

def ratMid (ε : ℚ) (p : Pair' ℚ) : Option ℚ :=
  if p.snd - p.fst > ε then some (p.fst + (p.snd - p.fst) / 2) else none
def ratPred (target : ℚ) (x : ℚ) : Bool := x * x > target

#eval (binarySearch' ℚ (ratPred 9) (ratMid (1/1000)) (1, 4))

#eval 12289.0/2048
