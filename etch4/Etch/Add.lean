import Etch.Stream

variable {ι : Type} {α : Type _} [Tagged ι] [TaggedC ι] [DecidableEq ι]
  [LT ι] [LE ι] [DecidableRel (LT.lt : ι → ι → Prop)]
  [DecidableRel (LE.le : ι → ι → _)]

-- `guard v b s` returns a stream which returns `0` (empty stream) if `b` is false
--  and acts identically to `s` if `b` is true. `v` is supposed to be a variable that `guard`
--  can use for storage.
class Guard (α : Type _) where
  guard : Var Bool → E Bool → α → α

instance [Tagged α] [OfNat α (nat_lit 0)] : Guard (E α) where
  guard := λ _ b v => .call Op.ternary ![b, v, (0 : E α)]

instance : Guard (S ι α) where guard := λ v b s =>
{s with
   init := λ n => (s.init n).map (λ p => .decl v b;; p) id
   valid := λ l => b * s.valid l}

-- Returns an expression which evaluates to `true` iff `a.index' ≤ b.index'`
def S_le (a : S ι α) (b : S ι β) (l : a.σ × b.σ) : E Bool :=
  (.call Op.neg ![b.valid l.2]) + (a.valid l.1 * (a.index l.1 <= b.index l.2))

infixr:40 "≤ₛ" => S_le

def Prod.symm (f : α × β) := (f.2, f.1)

-- Local temporary variables for `add`
structure AddTmp (ι : Type) [TaggedC ι] where
(cv₁ : Var Bool)
(cv₂ : Var Bool)
(ci : Var ι)

def AddTmp.ofName (n : Name) : AddTmp ι :=
⟨(Var.mk "cv1__").fresh n, (Var.mk "cv2__").fresh n, (Var.mk "ci").fresh n⟩

def S.add [HAdd α β γ] [Guard α] [Guard β] (a : S ι α) (b : S ι β) : S ι γ where
  σ := (a.σ × b.σ) × AddTmp ι
  value := λ (p, t) =>
             (Guard.guard t.cv₁ ((S_le a b p) * a.ready p.1) $ a.value p.1) +
             (Guard.guard t.cv₂ ((S_le b a p.symm) * b.ready p.2) $ b.value p.2)
  skip  := λ (p, _) i => a.skip p.1 i ;; b.skip p.2 i
  succ  := λ (p, t) i =>
    t.ci.decl i;;
    a.succ p.1 t.ci;; b.succ p.2 t.ci
  ready := λ (p, _) => (S_le a b p) * a.ready p.1 + (S_le b a p.symm) * b.ready p.2
  index := λ (p, _) => .call Op.ternary ![S_le a b p, a.index p.1, b.index p.2]
  valid := λ (p, _) => a.valid p.1 + b.valid p.2
  init  := λ n => let (i, s) := seqInit a b n; (i, (s, .ofName n))

instance [Add α] [Guard α] : Add (ι →ₛ α) := ⟨S.add⟩
instance [HAdd α β γ] [Guard α] [Guard β] : HAdd (S ι α) (S ι β) (S ι γ) := ⟨S.add⟩
instance [HAdd α β γ] : HAdd (ι →ₐ α) (ι →ₐ β) (ι →ₐ γ) where hAdd a b := λ v => a v + b v
instance [HAdd α β γ] : HAdd (ι →ₛ α) (ι →ₐ β) (ι →ₛ γ) where hAdd a b := {a with value := λ s => a.value s + b (a.index s)}
instance [HAdd β α γ] : HAdd (ι →ₐ β) (ι →ₛ α) (ι →ₛ γ) where hAdd b a := {a with value := λ s => b (a.index s) + a.value s}


section new
def S_le' (a : S' ι α) (b : S' ι β) : E Bool :=
  (.call Op.neg ![b.valid]) + (a.valid * (a.index <= b.index))

def S'.weakAdd [HAdd α β γ] [Guard α] [Guard β] (a : S' ι α) (b : S' ι β) (n : Name) : S' ι γ  :=
  let p := (a.state, b.state)
  let t := .ofName n
  { σ := (a.σ × b.σ) × AddTmp ι
    state := (p, t)
    value :=
               HAdd.hAdd
               (Guard.guard t.cv₁ ((S_le' a b) * a.ready) $ a.value)
               (Guard.guard t.cv₂ ((S_le' b a) * b.ready) $ b.value)
    skip  := fun e r ↦ a.skip e r ;; b.skip e r
    ready := (S_le' a b) * a.ready + (S_le' b a ) * b.ready
    index := .call Op.ternary ![S_le' a b , a.index, b.index]
    valid := a.valid * b.valid
  }

def S'.add [HAdd α β γ] [Guard α] [Guard β] [Zero α] [Zero β]
    (a : S' ι α) (b : S' ι β) : Name → Then (S' ι γ) (Then (S' ι γ) (S' ι γ)) :=
  fun n ↦ (a.weakAdd b n, (. + (0 : β)) <$> a, ((0 : α) + .) <$> b)

variable
  [HAdd α β γ] [Guard α] [Guard β] [Zero α] [Zero β]

instance  : HAdd (S' ι α) (S' ι β) (Name → (S' ι γ) <;;> (S' ι γ) <;;> (S' ι γ)) := ⟨ S'.add ⟩

end new
