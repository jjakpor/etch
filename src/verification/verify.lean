import data.vector
import data.fin.vec_notation
import data.fin.tuple.basic
import data.list.of_fn
import data.list.alist
import data.finsupp.basic
import control.bifunctor
import tactic.derive_fintype
import tactic.fin_cases
import finsupp_lemmas
import frames
import verification.vars
import verification.misc
import verification.stream
import data.pfun

section

parameters (R : Type)
[add_zero_class R] [has_one R] [has_mul R]


open Types (nn rr bb)

@[reducible]
def ExprVal : Types → Type
| nn := ℕ
| rr := R
| bb := bool

parameter {R}
namespace ExprVal

instance : ∀ b, inhabited (ExprVal b)
| nn := ⟨0⟩
| rr := ⟨0⟩
| bb := ⟨ff⟩

instance [has_to_string R] :
∀ b, has_to_string (ExprVal b)
| nn := infer_instance
| rr := infer_instance
| bb := infer_instance

end ExprVal

@[derive decidable_eq]
inductive Op : Types → Type
| nadd : Op nn | radd : Op rr
| nmul : Op nn | rmul : Op rr
| nsub : Op nn
| and : Op bb
| or : Op bb
| not : Op bb
| nat_eq : Op bb
| lt : Op bb
| le : Op bb
| cast_r : Op rr

namespace Op
instance : ∀ b, has_to_string (Op b)
| rr := ⟨λ v, match v with
| radd := "+"
| rmul := "*"
| cast_r := "cast"
end⟩
| nn := ⟨λ v, match v with
| nadd := "+"
| nmul := "*"
| nsub := "-"
end⟩
| bb := ⟨λ v, match v with
| and := "&&"
| or := "||"
| not := "!"
| nat_eq := "="
| lt := "<"
| le := "<="
end⟩

@[reducible]
def arity : ∀ {b}, Op b → ℕ
| _ nadd := 2
| _ radd := 2
| _ nmul := 2
| _ rmul := 2
| _ nsub := 2
| _ and := 2 | _ or := 2 | _ not := 1 | _ nat_eq := 2 | _ lt := 2 | _ le := 2
| _ cast_r := 1

def is_not_infix : finset (Σ b, Op b) :=
{⟨_, Op.cast_r⟩}

def to_str_with_args {b} (o : Op b) (args : list string) : string :=
if H : (sigma.mk b o) ∈ is_not_infix ∨ 3 ≤ o.arity then
  (to_string o) ++ "(" ++ ", ".intercalate args ++ ")"
else match o.arity, (show ¬(3 ≤ o.arity), by tauto!) with
  0, _ := (to_string o),
  1, _ := (to_string o) ++ args.head,
  2, _ := "(" ++ (args.inth 0) ++ " " ++ (to_string o) ++ " " ++ (args.inth 1) ++ ")",
  (n + 3), h := by { exfalso, simpa using h, }
end

@[reducible]
def signature : ∀ {b} (o : Op b), (fin o.arity → Types)
| _ nadd := ![nn, nn] | _ radd := ![rr, rr]
| _ nmul := ![nn, nn] | _ rmul := ![rr, rr]
| _ nsub := ![nn, nn]
| _ and := ![bb, bb] | _ or := ![bb, bb] | _ not := ![bb]
| _ nat_eq := ![nn, nn] | _ lt := ![nn, nn] | _ le := ![nn, nn]
| _ cast_r := ![nn]

@[simp]
def eval : ∀ {b} (o : Op b), (Π (n : fin o.arity), ExprVal (o.signature n)) → ExprVal b
| _ nadd := λ args, ((+) : ℕ → ℕ → ℕ) (args 0) (args 1)
| _ radd := λ args, ((+) : R → R → R) (args 0) (args 1)
| _ nmul := λ args, ((*) : ℕ → ℕ → ℕ) (args 0) (args 1)
| _ rmul := λ args, ((*) : R → R → R) (args 0) (args 1)
| _ nsub := λ args, nat.sub (args 0) (args 1)
| _ and := λ args, (args 0 : bool) && (args 1 : bool)
| _ or := λ args, (args 0 : bool) || (args 1 : bool)
| _ not := λ args, bnot (args 0)
| _ nat_eq := λ args, args 0 = args 1
| _ lt := λ args, (show ℕ, from args 0) < args 1
| _ le := λ args, (show ℕ, from args 0) ≤ args 1
| _ cast_r := λ args, show ℕ, from args 0

end Op

parameter (R)
inductive Expr : Types → Type
| lit {b} : ExprVal b → Expr b
| ident {b} : Ident b → Expr b
| access {b} : Ident b → Expr nn → Expr b
| call {b} : ∀ o : Op b, (Π (n : fin o.arity), Expr (o.signature n)) → Expr b
| ternary {b} : Expr bb → Expr b → Expr b → Expr b


abbreviation EContext := HeapContext ExprVal
abbreviation Frame := finset (Σ b, Ident b)
instance : inhabited Frame := ⟨(default : finset (Σ b, Ident b))⟩

parameter {R}

def Expr.eval (ctx : EContext) : ∀ {b}, Expr b → option (ExprVal b)
| _ (Expr.lit r) := some r
| b (Expr.ident x) := some (ctx.store.get x)
| b (Expr.access x i) := i.eval >>= λ i', (ctx.heap.get x).nth i'
| _ (Expr.call o args) := fin.tuple_some (λ i, (args i).eval) >>= λ r, some (o.eval r)
| _ (Expr.ternary c e₁ e₂) := c.eval >>= λ r, cond r e₁.eval e₂.eval

@[simp] def Expr.frame : ∀ {b}, Expr b → Frame
| _ (Expr.lit r) := ∅
| _ (Expr.ident x) := {sigma.mk _ x}
| _ (Expr.access x i) := insert (sigma.mk _ x) i.frame
| _ (Expr.call o args) := finset.bUnion finset.univ (λ i, (args i).frame)
| _ (Expr.ternary c e₁ e₂) := c.frame ∪ e₁.frame ∪ e₂.frame

-- local notation a ` ⟪<⟫ ` b := Expr.call Op.lt (fin.cons (a : Expr nn) (fin.cons (b : Expr nn) default))

class has_comp (α : Type*) (β : out_param Type*) :=
(eq : α → α → β)
(le : α → α → β)
(lt : α → α → β)
(ge : α → α → β)
(gt : α → α → β)

infix ` ⟪≤⟫ `:50   := has_comp.le
infix ` ⟪<⟫ `:50   := has_comp.lt
infix ` ⟪≥⟫ `:50   := has_comp.ge
infix ` ⟪>⟫ `:50   := has_comp.gt
infix ` ⟪=⟫ `:50   := has_comp.eq

@[simps { attrs := [] }] instance Expr.has_comp : has_comp (Expr nn) (Expr bb) :=
{ eq := λ a b, Expr.call Op.nat_eq $ fin.cons a $ fin.cons b default,
  lt := λ a b, Expr.call Op.lt $ fin.cons a $ fin.cons b default,
  le := λ a b, Expr.call Op.le $ fin.cons a $ fin.cons b default,
  ge := λ a b, Expr.call Op.le $ fin.cons b $ fin.cons a default,
  gt := λ a b, Expr.call Op.lt $ fin.cons b $ fin.cons a default }

section Expr

def expr_repr [has_to_string R] : ∀ {b : Types}, (Expr b) → string
| _ (Expr.lit r) := to_string r
| _ (Expr.ident x) := to_string x
| _ (Expr.access x i) := (to_string x) ++ "[" ++ (expr_repr i) ++ "]"
| _ (Expr.call o args) := o.to_str_with_args (vector.of_fn (λ i, expr_repr $ args i)).to_list
| _ (Expr.ternary c e₁ e₂) := (expr_repr c) ++ " ? " ++ (expr_repr e₁) ++ " : " ++ (expr_repr e₂)

instance {b : Types} [has_to_string R] : has_to_string (Expr b) := ⟨expr_repr⟩

instance Expr.zero_nn : has_zero (Expr nn) := ⟨Expr.lit (0 : ℕ)⟩
instance Expr.one_nn : has_one (Expr nn) := ⟨Expr.lit (1 : ℕ)⟩
instance Expr.zero_rr : has_zero (Expr rr) := ⟨Expr.lit (0 : R)⟩
instance Expr.one_rr : has_one (Expr rr) := ⟨Expr.lit (1 : R)⟩

instance Expr.has_coe_from_nat : has_coe ℕ (Expr nn) := ⟨λ n, Expr.lit n⟩
instance Expr.has_coe_from_R : has_coe R (Expr rr) := ⟨λ r, Expr.lit r⟩

@[simp] lemma Expr_frame_coe_nat (n : ℕ) : (n : Expr nn).frame = ∅ := rfl
@[simp] lemma Expr_frame_coe_R (r : R) : (r : Expr rr).frame = ∅ := rfl
@[simp] lemma Expr_frame_zero_nat : (0 : Expr nn).frame = ∅ := rfl
@[simp] lemma Expr_frame_one_nat : (1 : Expr nn).frame = ∅ := rfl

@[simps { attrs := [] }] instance add_nn : has_add (Expr nn) :=
⟨λ a b, Expr.call Op.nadd (fin.cons a (fin.cons b default))⟩
@[simps { attrs := [] }] instance add_rr : has_add (Expr rr) :=
⟨λ a b, Expr.call Op.radd (fin.cons a (fin.cons b default))⟩
@[simps { attrs := [] }] instance mul_nn : has_mul (Expr nn) :=
⟨λ a b, Expr.call Op.nmul (fin.cons a (fin.cons b default))⟩
@[simps { attrs := [] }] instance mul_rr : has_mul (Expr rr) :=
⟨λ a b, Expr.call Op.rmul (fin.cons a (fin.cons b default))⟩
@[simps { attrs := [] }] instance sub_nn : has_sub (Expr nn) :=
⟨λ a b, Expr.call Op.nsub (fin.cons a (fin.cons b default))⟩

instance inf_bb : has_inf (Expr bb) :=
⟨λ a b, Expr.call Op.and (fin.cons a (fin.cons b default))⟩

instance sup_bb : has_sup (Expr bb) :=
⟨λ a b, Expr.call Op.or (fin.cons a (fin.cons b default))⟩

def Expr.not : Expr bb → Expr bb := λ e, Expr.call Op.not (fin.cons e default)

instance has_coe_to_expr {b : Types} : has_coe (Ident b) (Expr b) := ⟨Expr.ident⟩

@[reducible] def Ident.to_expr {b} : Ident b → Expr b := Expr.ident
@[simp] lemma Expr_frame_coe_ident {b} (i : Ident b) : (i : Expr b).frame = {sigma.mk _ i} := rfl

/- Warning! Lean 3 uses zero, add, one instead of coe from ℕ for numerals -/
example : (3 : Expr nn) = 1 + 1 + 1 := rfl
example : (3 : Expr nn) ≠ Expr.lit 3 := by trivial
example : ((3 : ℕ) : Expr nn) = Expr.lit 3 := rfl

@[simp] lemma Expr.eval_lit {b : Types} (x : ExprVal b) (ctx : EContext) :
  (Expr.lit x).eval ctx = some x := rfl
@[simp] lemma Expr.lit_eq_nn (x : ℕ) : @Expr.lit nn x = ↑x := rfl
@[simp] lemma Expr.lit_eq_rr (x : R) : @Expr.lit rr x = ↑x := rfl
@[simp] lemma Expr.eval_lit_nn (x : ℕ) (ctx : EContext) :
  (x : Expr nn).eval ctx = some x := rfl
@[simp] lemma Expr.eval_lit_rr (x : R) (ctx : EContext) :
  (x : Expr rr).eval ctx = some x := rfl
@[simp] lemma Expr.eval_zero_nn (ctx : EContext) : (0 : Expr nn).eval ctx = some 0 := rfl
@[simp] lemma Expr.eval_zero_rr (ctx : EContext) : (0 : Expr rr).eval ctx = some 0 := rfl
@[simp] lemma Expr.eval_one_nn (ctx : EContext) : (1 : Expr nn).eval ctx = some 1 := rfl
@[simp] lemma Expr.eval_one_rr (ctx : EContext) : (1 : Expr rr).eval ctx = some 1 := rfl
@[simp] lemma Expr.eval_ident {b : Types} (x : Ident b) (ctx : EContext) :
  (Expr.ident x).eval ctx = some (ctx.store.get x) := rfl
@[simp] lemma Expr.eval_ident' {b : Types} (x : Ident b) (ctx : EContext) :
  (x : Expr b).eval ctx = some (ctx.store.get x) := rfl
@[simp] lemma Expr.eval_access {b : Types} (x : Ident b) (ind : Expr nn) (ctx : EContext) :
  (Expr.access x ind).eval ctx = ind.eval ctx >>= λ i, (ctx.heap.get x).nth i := rfl

@[simp] lemma Expr.eval_nadd (e₁ e₂ : Expr nn) (ctx : EContext) :
  (e₁ + e₂).eval ctx = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n + m) :=
by { simp [add_nn_add, Expr.eval, fin.tuple_some] with functor_norm, refl, }
@[simp] lemma Expr.eval_radd (e₁ e₂ : Expr rr) (ctx : EContext) :
  (e₁ + e₂).eval ctx = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n + m) :=
by { simp [add_rr_add, Expr.eval, fin.tuple_some] with functor_norm, refl, }
@[simp] lemma Expr.eval_nmul (e₁ e₂ : Expr nn) (ctx : EContext) :
  (e₁ * e₂).eval ctx = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n * m) :=
by { simp [mul_nn_mul, Expr.eval, fin.tuple_some] with functor_norm, refl, }
@[simp] lemma Expr.eval_rmul (e₁ e₂ : Expr rr) (ctx : EContext) :
  (e₁ * e₂).eval ctx = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n * m) :=
by { simp [mul_rr_mul, Expr.eval, fin.tuple_some] with functor_norm, refl, }

@[simp] lemma Expr.eval_lt (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪<⟫ e₂) = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n < m : bool) :=
by { simp [(⟪<⟫), Expr.eval, fin.tuple_some] with functor_norm, refl, }
@[simp] lemma Expr.eval_le (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪≤⟫ e₂) = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n ≤ m : bool) :=
by { simp [(⟪≤⟫), Expr.eval, fin.tuple_some] with functor_norm, refl, }
-- todo: consider less surprising evaluation order
@[simp] lemma Expr.eval_gt (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪>⟫ e₂) = (e₂.eval ctx) >>= λ n, e₁.eval ctx >>= λ m, some (n < m : bool) :=
by { simp [(⟪>⟫), Expr.eval, fin.tuple_some] with functor_norm, refl, }
@[simp] lemma Expr.eval_ge (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪≥⟫ e₂) = (e₂.eval ctx) >>= λ n, e₁.eval ctx >>= λ m, some (m ≥ n : bool) :=
by { simp [(⟪≥⟫), Expr.eval, fin.tuple_some] with functor_norm, refl, }

@[simp] lemma Expr.eval_eq (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪=⟫ e₂) = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n = m : bool) :=
by { simp [(⟪=⟫), Expr.eval, fin.tuple_some] with functor_norm, refl, }

@[simp] lemma Expr.eval_and (e₁ e₂ : Expr bb) (ctx : EContext) :
  (e₁ ⊓ e₂).eval ctx = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n && m : bool) :=
by { simp [has_inf.inf, Expr.eval, fin.tuple_some] with functor_norm, refl }
@[simp] lemma Expr.eval_or  (e₁ e₂ : Expr bb) (ctx : EContext) :
  (e₁ ⊔ e₂).eval ctx = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n || m : bool) :=
by { simp [has_sup.sup, Expr.eval, fin.tuple_some] with functor_norm, refl }

@[simp] lemma Expr.eval_ident_is_some {b : Types} {ctx : EContext} (i : Ident b) :
  (Expr.eval ctx (i : Expr b)).is_some := by simp

@[simp] lemma Expr.eval_not (e : Expr bb) (ctx : EContext) :
  e.not.eval ctx = (e.eval ctx) >>= λ v, some (bnot v) :=
by { simp [Expr.not, Expr.eval, fin.tuple_some] with functor_norm, refl, }

@[simp] def EContext.is_length {b : Types} (ctx : EContext) (arr : Ident b) (len : Ident nn) : Prop :=
(ctx.heap.get arr).length = ctx.store.get len

-- lemma get_arr_some {b : Types} {ctx : EContext} {arr : Ident b} {len : Expr nn}
--   (h₁ : ctx.is_length arr len) {i : ℕ} (h₂ : ∀ n, len.eval ctx = some n → i < n) :
--   ((ctx.get arr).get_arr i).is_some :=
-- by { }

-- @[simp] lemma get_arr_is_some_iff {b : Types} {ctx : EContext} {arr : Ident b} {i} :
--   ((ctx.heap.get arr).nth i).is_some ↔ i < (ctx.heap.get arr).length :=
-- by { simp, }

end Expr

parameter (R)
structure LoopBound :=
(frame : Frame)
(to_fun : EContext → ℕ)
(has_frame : true /- TODO: function.has_frame to_fun frame -/)

section LoopBound

instance : has_coe_to_fun LoopBound (λ _, EContext → ℕ) :=
⟨LoopBound.to_fun⟩
instance has_coe_from_nat : has_coe ℕ LoopBound := ⟨λ n, ⟨finset.empty, (λ _, n), true.intro⟩⟩

end LoopBound

parameter (R)
inductive Prog
| skip : Prog
| store {b : Types} (dst : Ident b) (val : Expr b)
| store_arr {b : Types} (dst : Ident b) (ind : Expr nn) (val : Expr b)
| seq (a : Prog) (b : Prog)
| branch (cond : Expr bb) (a : Prog) (b : Prog)
| loop (n : LoopBound) (cond : Expr bb) (b : Prog)

section Prog

parameter {R}
def prog_repr [has_to_string R] : Prog → list string
| Prog.skip := ["pass"]
| (Prog.store dst val) := [(to_string dst) ++ " := " ++ (to_string val)]
| (Prog.store_arr dst ind val) := [(to_string dst) ++ ("[" ++ to_string ind ++ "]") ++ " := " ++ (to_string val)]
| (Prog.seq a b) := (prog_repr a) ++ (prog_repr b)
| (Prog.branch c a b) := ["if " ++ (to_string c) ++ ":"]
    ++ (prog_repr a).map (λ s, "  " ++ s)
    ++ ["else:"]
    ++ (prog_repr b).map (λ s, "  " ++ s)
| (Prog.loop n cond b) := ["while " ++ (to_string cond) ++ ":"]
    ++ (prog_repr b).map (λ s, "  " ++ s)

instance [has_to_string R] : has_to_string Prog :=
⟨λ p, "\n".intercalate (prog_repr p)⟩

def Prog.eval : Prog → EContext → option EContext
| Prog.skip ctx := some ctx
| (Prog.store dst val) ctx := (val.eval ctx) >>= λ r, some (ctx.update dst r)
| (Prog.store_arr dst ind val) ctx := ind.eval ctx >>= λ i, val.eval ctx >>= λ v,
  if i < (ctx.heap.get dst).length then some (ctx.update_arr dst i v) else none
| (Prog.seq a b) ctx := (a.eval ctx) >>= b.eval
| (Prog.branch condition a b) ctx := (Expr.eval ctx condition) >>= λ c : bool, cond c (a.eval ctx) (b.eval ctx)
| (Prog.loop n c b) ctx := (iterate_while b.eval
      (λ ctx : EContext, c.eval ctx)
      (n ctx)) ctx

@[simp] def Prog.frame : Prog → Frame
| Prog.skip := ∅
| (Prog.store dst val) := insert (sigma.mk _ dst) val.frame
| (Prog.store_arr dst ind val) := insert (sigma.mk _ dst) (ind.frame ∪ val.frame)
| (Prog.seq a b) := a.frame ∪ b.frame
| (Prog.branch c a b) := c.frame ∪ a.frame ∪ b.frame
| (Prog.loop n c b) := c.frame ∪ b.frame  

@[simp] lemma Prog.eval_skip_is_some (ctx : EContext) : (Prog.skip.eval ctx).is_some := by simp [Prog.eval]
@[simp] lemma Prog.store_is_some_iff {b : Types} {ctx : EContext} {dst : Ident b} {val : Expr b} :
  ((Prog.store dst val).eval ctx).is_some ↔ (val.eval ctx).is_some :=
by simp [Prog.eval]

end Prog

local infixr ` <;> `:1 := Prog.seq
local notation a ` ::= `:20 c := Prog.store a c
local notation a ` ⟬ `:9000 i ` ⟭ ` ` ::= `:20 c := Prog.store_arr a i c
local notation x ` ⟬ `:9000 i ` ⟭ ` := Expr.access x i

class Evalable (α : Type) (β : out_param Type) :=
(eval : EContext → α →. /- partial function -/ β)

@[simps]
instance eval_expr_nn : Evalable (Expr nn) ℕ :=
{ eval := λ ctx e, e.eval ctx }

@[simps]
instance eval_expr_rr : Evalable (Expr rr) R :=
{ eval := λ ctx e, e.eval ctx }

section stream

parameter (R)
structure BoundedStreamGen (ι α : Type) :=
(current : ι)
(value : α)
(ready : Expr bb)
(next : Prog)
(valid : Expr bb)
(bound : LoopBound)
(initialize : Prog)
(ctx_inv : EContext → Prop)

parameter {R}
variables {ι α ι' β : Type}

@[ext]
lemma BoundedStreamGen.ext {s₁ s₂ : BoundedStreamGen ι α} (h₁ : s₁.current = s₂.current)
  (h₂ : s₁.value = s₂.value) (h₃ : s₁.ready = s₂.ready) (h₄ : s₁.next = s₂.next) (h₅ : s₁.valid = s₂.valid)
  (h₆ : s₁.bound = s₂.bound) (h₇ : s₁.initialize = s₂.initialize) (h₈ : s₁.ctx_inv = s₂.ctx_inv) : s₁ = s₂ :=
by { cases s₁, cases s₂, dsimp only at *, subst_vars, }

section functorality

@[simps]
instance : bifunctor BoundedStreamGen :=
{ bimap := λ _ _ _ _ f g s, { s with current := f s.current, value := g s.value } }

instance : is_lawful_bifunctor BoundedStreamGen :=
{ id_bimap := by { intros, ext; simp, },
  bimap_bimap := by { intros, ext; simp, } }

end functorality

def BoundedStreamGen.inv_valid_at (s : BoundedStreamGen ι α) (ctx : EContext) : Prop :=
s.ctx_inv ctx ∧ s.valid.eval ctx = some tt

def BoundedStreamGen.ready_at (s : BoundedStreamGen ι α) (ctx : EContext) : Prop :=
s.inv_valid_at ctx ∧ s.ready.eval ctx = some tt

@[simp] lemma BoundedStreamGen.bimap_inv_valid_at {s : BoundedStreamGen ι α} {ctx : EContext} (f : ι → ι') (g : α → β) :
  (bimap f g s).inv_valid_at ctx ↔ s.inv_valid_at ctx := iff.rfl

@[simp] lemma BoundedStreamGen.ready_inv_valid_at {s : BoundedStreamGen ι α} {ctx : EContext} (f : ι → ι') (g : α → β) :
  (bimap f g s).ready_at ctx ↔ s.ready_at ctx := iff.rfl

def preserves (s : BoundedStreamGen ι α) (ctx : EContext) (p : EContext → Prop) : Prop :=
p ctx → ∀ {c}, s.next.eval ctx = some c → p c

section preserves
variables {s : BoundedStreamGen ι α} {ctx : EContext} {p₁ p₂ : EContext → Prop}
lemma preserves.and (h₀ : preserves s ctx p₁) (h₁ : preserves s ctx p₂) : (preserves s ctx (λ c, p₁ c ∧ p₂ c)) :=
by { simp only [preserves] at *, tauto, }

lemma preserves.is_length {b : Types} (v : Ident b) (e : Ident nn)  (h : (sigma.mk nn e) ∉ s.next.frame) :
  preserves s ctx (λ c, c.is_length v e) := sorry

end preserves

structure is_defined [Evalable ι ι'] [Evalable α β] (s : BoundedStreamGen ι α) (ctx : EContext) : Prop :=
(hvalid : s.ctx_inv ctx → (s.valid.eval ctx).is_some)
(hready : s.inv_valid_at ctx → (s.ready.eval ctx).is_some)
(hnext : s.inv_valid_at ctx → (s.next.eval ctx).is_some)
(hinit : s.ctx_inv ctx → (s.initialize.eval ctx).is_some)
(hcurr : s.inv_valid_at ctx → (Evalable.eval ctx s.current).dom)
(hval : s.ready_at ctx → (Evalable.eval ctx s.value).dom)
(hstep : preserves s ctx s.ctx_inv)

@[simps]
def to_stream_of_is_defined_aux  [Evalable ι ι'] [Evalable α β] (s : BoundedStreamGen ι α)
  (hs : ∀ ctx, is_defined s ctx) : Stream EContext ι' β :=
{ valid := s.inv_valid_at,
  ready := s.ready_at,
  next := λ ctx h, option.get ((hs ctx).hnext h),
  index := λ ctx h, part.get _ ((hs ctx).hcurr h),
  value := λ ctx h, part.get _ ((hs ctx).hval h) }

@[simps]
def BoundedStreamGen.to_stream_of_is_defined [Evalable ι ι'] [Evalable α β] (s : BoundedStreamGen ι α)
  (hs : ∀ ctx, is_defined s ctx) (ctx₀ : EContext) (hctx₀ : s.ctx_inv ctx₀) : StreamExec EContext ι' β :=
{ stream := to_stream_of_is_defined_aux s hs,
  bound := s.bound ctx₀,
  state := option.get ((hs ctx₀).hinit hctx₀) }

instance eval_stream [Evalable ι ι'] [Evalable α β] : Evalable (BoundedStreamGen ι α) (StreamExec EContext ι' β) :=
{ eval := λ ctx s, ⟨s.ctx_inv ctx ∧ ∀ c, is_defined s c, λ H, (s.to_stream_of_is_defined H.2 ctx H.1)⟩ }

@[simp] lemma eval_stream_is_some_iff [Evalable ι ι'] [Evalable α β] (s : BoundedStreamGen ι α) {c₀} :
  (Evalable.eval c₀ s).dom ↔ (s.ctx_inv c₀ ∧ ∀ c, is_defined s c) := iff.rfl

section translate
open_locale classical

structure tr_to {σ'} [Evalable ι ι'] [Evalable α β] (s : BoundedStreamGen ι α)
  (t : StreamExec σ' ι' β) (f : EContext → σ') (ctx : EContext) : Prop :=
(hvalid : s.ctx_inv ctx → s.valid.eval ctx = some (t.stream.valid (f ctx)))
(hready : s.inv_valid_at ctx → s.ready.eval ctx = some (t.stream.ready (f ctx)))
(hnext : s.inv_valid_at ctx → ∀ h, (f <$> s.next.eval ctx) = some (t.stream.next (f ctx) h))
(hinit : s.ctx_inv ctx → (f <$> s.initialize.eval ctx) = some t.state)
(hcurr : s.inv_valid_at ctx → ∀ h, Evalable.eval ctx s.current = part.some (t.stream.index (f ctx) h))
(hval : s.ready_at ctx → ∀ h, Evalable.eval ctx s.value = part.some (t.stream.value (f ctx) h))
(hstep : preserves s ctx s.ctx_inv)
(hbound : s.bound ctx = t.bound)

lemma tr_to.is_def {σ'} [Evalable ι ι'] [Evalable α β] {s : BoundedStreamGen ι α}
  {t : StreamExec σ' ι' β} {f : EContext → σ'} {ctx : EContext} (h : tr_to s t f ctx) :
  is_defined s ctx :=
{ hvalid := λ H, by simp [h.hvalid H],
  hready := λ H, by simp [h.hready H],
  hnext := λ H, by { have := h.hnext H (by simpa [H.2] using h.hvalid H.1), simpa using congr_arg option.is_some this, },
  hinit := λ H, by simpa using congr_arg option.is_some (h.hinit H),
  hcurr := λ H, by { rw h.hcurr H (by simpa [H.2] using h.hvalid H.1), trivial, },
  hval := λ H, by { rw h.hval H (by simpa [H.2] using h.hready H.1), trivial, },
  hstep := h.hstep }

lemma tr_to.eval_finsupp_eq {β σ'} [add_zero_class β] [Evalable ι ι'] [Evalable α β] {s : BoundedStreamGen ι α}
  {t : StreamExec σ' ι' β} {f : EContext → σ'} (h : ∀ ctx, tr_to s t f ctx) (ctx : EContext) 
  (hctx : s.ctx_inv ctx) :
  ((Evalable.eval ctx s).get ⟨hctx, λ c, (h c).is_def⟩).eval = t.eval :=
sorry

end translate
#exit


instance eval_unit : Evalable unit unit := ⟨λ _, part.some⟩
@[simp] lemma eval_unit_dom (c) : (Evalable.eval c ()).dom := trivial

def singleton (x : α) : BoundedStreamGen unit α := sorry

def range_nn (n : Expr nn) : BoundedStreamGen (Expr nn) (Expr nn) := sorry

def range_rr (n : Expr nn) : BoundedStreamGen (Expr nn) (Expr rr) := sorry

def externSparseVec (scratch : NameSpace) : BoundedStreamGen (Expr nn) (Expr rr) :=
let i : Ident nn := scratch∷Vars.i,
    len : Ident nn := NameSpace.reserved∷Vars.len,
    inds : Ident nn := NameSpace.reserved∷Vars.ind₀,
    vals : Ident rr := NameSpace.reserved∷Vars.vals in
{ current := inds⟬i⟭,
  value := vals⟬i⟭,
  ready := Expr.lit tt,
  next := i ::= i + 1,
  valid := (i : Expr nn) ⟪<⟫ len,
  bound := ⟨default, λ ctx, ctx.store.get len, /- TODO: Frame -/ trivial⟩,
  initialize := i ::= 0,
  ctx_inv := λ ctx, ctx.is_length inds len ∧ ctx.is_length vals len }

def contract (x : BoundedStreamGen ι α) : BoundedStreamGen unit α :=
default <$₁> x

section functor_is_defined
variables {ι₁ ι₁' ι₂ ι₂' α' β' : Type} [Evalable ι₁ ι₂] [Evalable α β]
  {x : BoundedStreamGen ι₁ α} {c : EContext} (hx : is_defined x c)
  (f : ι₁ → ι₁') (g : α → α')
include hx

@[simp] lemma bimap_is_defined [Evalable ι₁' ι₂'] [Evalable α' β'] :
  is_defined (bifunctor.bimap f g x) c ↔ ((x.inv_valid_at c → (Evalable.eval c (f x.current)).dom) ∧ (x.ready_at c → (Evalable.eval c (g x.value)).dom)) :=
⟨λ ⟨hv, hr, hn, hi, hc, hl, hs⟩, ⟨hc, hl⟩, λ ⟨H₁, H₂⟩, ⟨hx.hvalid, hx.hready, hx.hnext, hx.hinit, H₁, H₂, hx.hstep⟩⟩

@[simp] lemma imap_is_defined [Evalable ι₁' ι₂'] :
  is_defined (f <$₁> x) c ↔ (x.inv_valid_at c → (Evalable.eval c (f x.current)).dom) :=
by { rw bimap_is_defined hx, have := hx.hval, simp [imp_iff_distrib], tauto, }

@[simp] lemma vmap_is_defined [Evalable α' β'] :
  is_defined (g <$₂> x) c ↔ (x.ready_at c → (Evalable.eval c (g x.value)).dom) :=
by { rw bimap_is_defined hx, have := hx.hcurr, simp [imp_iff_distrib], tauto, }

end functor_is_defined

lemma contract_tr [Evalable ι ι'] [Evalable α β] (x : BoundedStreamGen ι α)
  (ctx : EContext) (hctx : x.ctx_inv ctx)
  (h : ∀ c, is_defined x c) :
  Evalable.eval ctx (contract x) = part.some (contract_stream ((Evalable.eval ctx x).get ⟨hctx, h⟩)) :=
by { rw ← part.get_eq_iff_eq_some, swap, { simp [contract, h, hctx], }, refl, }

section sparse_vectors
open NameSpace (reserved) Vars (ind₀ vals len)

def list_to_sparse_inds [decidable_eq R] (ls : list R) : list ℕ :=
ls.find_indexes (≠0)

def list_to_sparse_vals [decidable_eq R] (ls : list R) : list R :=
ls.filter (≠0)

lemma externSparseVec_is_defined (scratch : NameSpace) (c : EContext) :
  is_defined (externSparseVec scratch) c :=
begin
  split,
  iterate 4 { simp [externSparseVec], }, -- hvalid to hinit
  focus { rintros ⟨⟨hl₁, hl₂⟩, hv⟩, }, swap, focus { rintros ⟨⟨⟨hl₁, hl₂⟩, hv⟩, _⟩, },
  iterate 2 { simp at hl₁ hl₂, simpa [externSparseVec, BoundedStreamGen.valid_at, hl₁, hl₂] using hv, },
  apply preserves.and;
  apply preserves.is_length;
  simp [externSparseVec, has_add.add, fin.forall_fin_two],
end

#check λ (scratch : NameSpace) (ctx), (Evalable.eval ctx (externSparseVec scratch)).get ⟨_, externSparseVec_is_defined _⟩

-- lemma externSparseVec_tr (scratch : NameSpace) :


end sparse_vectors

def compile_scalar (x : BoundedStreamGen unit (Expr rr)) : Prog :=
let out : Ident rr := NameSpace.reserved∷Vars.output in
x.initialize <;>
Prog.loop x.bound x.valid $
  Prog.branch x.ready (out ::= out + x.value) Prog.skip <;>
  x.next

-- Final theorem will be something like:
-- ∀ (x : BoundedStreamGen ι α) [Evalable ι → ι'] [Evalable α → β] [FinsuppEval (StreamExec EContext ι' β)]
--  (hind₁ : ι compiles correctly) (hind₂ : α compiles correctly) : BoundedStreamGen ι α compiles correctly


-- structure tr {ι ι' σ α β} (x : BoundedStreamGen ι α) (y : Stream σ ι' β) :=
-- (tr_ι : EContext → ι → ι')
-- (tr_α : EContext → α → β)
-- (tr_ctx : EContext → σ)
-- -- (hcurr : ∀ ctx : EContext, y.stream.valid (tr_ctx ctx) = tt → )
-- (hvalid : ∀ ctx : EContext, ∃ n : ℕ, n ∈ x.valid.eval ctx ∧ (0 < n ↔ y.valid (tr_ctx ctx) = tt))
-- (hready : ∀ ctx : EContext, ∃ n : ℕ, n ∈ x.ready.eval ctx ∧ (0 < n ↔ y.ready (tr_ctx ctx) = tt))
-- (hnext : ∀ ctx : EContext, ∃ ctx' ∈ x.next.eval ctx, y.next (tr_ctx ctx) = tr_ctx ctx')
-- (hval : ∀ ctx : EContext, ∃ n : ℕ, )
-- etc. ℕ



-- (N : Expr nn)
-- tr (range_nn N) (range ?)

-- range_nn (n : Expr nn) ∼ range_nn
-- singleton (range_nn (n : Expr nn))  ∼ singleton (range )


end stream


end

section examples
open Types

notation ` Σ_c ` := contract
@[derive [add_comm_monoid, has_one, has_mul, has_to_string], irreducible]
def R := ℤ
abbreviation compile := @compile_scalar R

def sum_vec : BoundedStreamGen R unit (Expr R rr) :=
Σ_c (externSparseVec (fresh ∅))

#eval do io.print_ln (compile sum_vec)

end examples

#exit

@[simp]
def add : ExprVal → ExprVal → ExprVal
| (nat n₁) (nat n₂) := nat (n₁ + n₂)
| (rval f₁) (rval f₂) := rval (f₁ + f₂)
| _ _ := arbitrary _

@[simp]
def and : ExprVal → ExprVal → ExprVal
| (nat n₁) (nat n₂) := if n₁ = 0 then nat 0 else nat n₂
| _ _ := arbitrary _

@[simp]
def mul : ExprVal → ExprVal → ExprVal
| (nat n₁) (nat n₂) := nat (n₁ * n₂)
| (rval f₁) (rval f₂) := rval (f₁ * f₂)
| _ _ := arbitrary _

@[simp]
def not : ExprVal → ExprVal
| (nat n₁) := if n₁ = 0 then nat 1 else nat 0
| _ := arbitrary _

@[simp]
def to_nat : ExprVal → ℕ
| (nat n₁) := n₁
| _ := arbitrary _

@[simp]
def eq : ExprVal → ExprVal → ExprVal
| (nat n₁) (nat n₂) := if n₁ = n₂ then nat 1 else nat 0
| _ _ := arbitrary _

@[simp]
def lt : ExprVal → ExprVal → ExprVal
| (nat n₁) (nat n₂) := if n₁ < n₂ then nat 1 else nat 0
| _ _ := arbitrary _

@[simp]
def to_r : ExprVal → R
| (nat n) := n
| (rval r) := r

@[simp]
def cast_r (v : ExprVal) : ExprVal := rval v.to_r

end ExprVal
parameter (R)
inductive IdentVal
| base (val : ExprVal) : IdentVal
| arr (val : list (ExprVal)) : IdentVal
instance : inhabited IdentVal := ⟨IdentVal.base default⟩

parameter {R}
def IdentVal.get : IdentVal → option ℕ → ExprVal
| (IdentVal.base val) none := val
| (IdentVal.arr val) (some i) := val.inth i
| _ _ := arbitrary _

@[simp] lemma IdentVal.get_none (b : ExprVal) : (IdentVal.base b).get none = b := rfl
@[simp] lemma IdentVal.get_ind (arr : list ExprVal) (n : ℕ) :
  (IdentVal.arr arr).get (some n) = arr.inth n := rfl

def IdentVal.update : IdentVal → option ℕ → ExprVal → IdentVal
| (IdentVal.arr val) (some i) newval := IdentVal.arr (val.modify_nth (λ _, newval) i)
| _ none newval := IdentVal.base newval
| _ _ _ := arbitrary _

@[simp] lemma IdentVal.update_none (i : IdentVal) (x : ExprVal) :
  i.update none x = IdentVal.base x := by cases i; simp [IdentVal.update]
@[simp] lemma IdentVal.update_ind (arr : list ExprVal) (n : ℕ) (x : ExprVal) :
  (IdentVal.arr arr).update (some n) x = IdentVal.arr (arr.modify_nth (λ _, x) n) := rfl

end Ident


inductive Op
| add | mul | and | or | not | eq | lt | cast_r

namespace Op
instance : has_to_string Op := ⟨λ v, match v with
| add := "add"
| mul := "mul"
| and := "and"
| or := "or"
| not := "not"
| eq := "eq"
| lt := "lt"
| cast_r := "cast"
end⟩

@[reducible] def arity : Op → ℕ
| Op.add := 2
| Op.mul := 2
| Op.and := 2
| Op.or := 2
| Op.not := 1
| Op.eq := 2
| Op.lt := 2
| Op.cast_r := 1

@[simp]
def eval : ∀ o : Op, (fin o.arity → ExprVal) → ExprVal
| add := λ x, (x 0).add (x 1)
| mul := λ x, (x 0).mul (x 1)
| and := λ x, (x 0).and (x 1)
| or := λ x, ((x 0).not.and $ (x 1).not).not -- TODO
| not := λ x, (x 0).not
| eq := λ x, (x 0).eq (x 1)
| lt := λ x, (x 0).lt (x 1)
| cast_r := λ x, (x 0).cast_r
end Op

parameter (R)
inductive Expr
| lit : ExprVal → Expr
| ident : Ident → Expr
| access : Ident → Expr → Expr
| call : ∀ o : Op, (fin o.arity → Expr) → Expr

parameter {R}
local notation a ` ⟪+⟫ `:80 b := Expr.call Op.add ![a, b]
local notation a ` ⟪*⟫ `:80 b := Expr.call Op.mul ![a, b]
local notation a ` ⟪&&⟫ `:80 b := Expr.call Op.and ![a, b]
local notation a ` ⟪||⟫ `:80 b := Expr.call Op.or ![a, b]
local notation a ` ⟪<⟫ `:80 b := Expr.call Op.lt ![a, b]
local notation a ` ⟪=⟫ `:80 b := Expr.call Op.eq ![a, b]

@[simp]
def Expr.eval  (ctx : Ident → IdentVal) : Expr → ExprVal
| (Expr.lit r) := r
| (Expr.ident x) := (ctx x).get none
| (Expr.access x i) := (ctx x).get (some i.eval.to_nat)
| (Expr.call o args) := o.eval (λ i, (args i).eval)

instance has_coe_from_nat : has_coe ℕ Expr := ⟨λ n, Expr.lit $ ExprVal.nat n⟩
instance has_coe_from_R : has_coe R Expr := ⟨λ r, Expr.lit $ ExprVal.rval r⟩
instance has_coe_from_Ident : has_coe Ident Expr := ⟨Expr.ident⟩

example : Expr := (0 : ℕ)
example : Expr := (0 : R)

@[simp] lemma Expr.eval_const_nat (ctx : Ident → IdentVal) (n : ℕ) :
  Expr.eval ctx n = ExprVal.nat n := rfl

@[simp] lemma Expr.eval_const_r (ctx : Ident → IdentVal) (r : R) :
  Expr.eval ctx r = ExprVal.rval r := rfl

@[simp] lemma Expr.eval_coe_ident (ctx : Ident → IdentVal) (i : Ident) :
  Expr.eval ctx i = (ctx i).get none := rfl

/-- Pretty print repr of indices; ignores [] (scalar), represents only
    vector indices -/
-- def idcs_repr (idcs : list string) : string :=
-- if idcs.length = 0 then "" else "[" ++ ", ".intercalate idcs ++ "]"

def expr_repr [has_to_string R] : Expr → string
| (Expr.lit r) := to_string r
| (Expr.ident x) := to_string x
| (Expr.access x i) := (to_string x) ++ "[" ++ (expr_repr i) ++ "]"
| (Expr.call o args) := (to_string o) ++ "(" ++ ", ".intercalate (vector.of_fn (λ i, expr_repr $ args i)).to_list ++ ")"

instance [has_to_string R] : has_to_string Expr := ⟨expr_repr⟩
-- Because ambiguous whether R or ℕ
-- instance : has_zero (Expr R) := ⟨Expr.lit 0⟩
-- instance : has_one (Expr R) := ⟨Expr.lit 1⟩

parameter (R)
structure LoopBound :=
(frame : finset Ident)
(to_fun : (Ident → IdentVal) → ℕ)
(has_frame : function.has_frame to_fun frame)

parameter {R}
instance : has_coe_to_fun LoopBound (λ _, (Ident → IdentVal) → ℕ) :=
⟨LoopBound.to_fun⟩

@[simp] lemma to_fun_eq_coe (f : LoopBound) (ctx : Ident → IdentVal) : f.to_fun = ⇑f := rfl

@[simp] lemma to_fun_apply (frame : finset Ident) (to_fun : (Ident → IdentVal) → ℕ) (h) (ctx : Ident → IdentVal) :
  (LoopBound.mk frame to_fun h) ctx = to_fun ctx := rfl

theorem LoopBound.frame_sound (f : LoopBound) {ctx₀ ctx₁ : Ident → IdentVal} (h : ∀ v ∈ f.frame, ctx₀ v = ctx₁ v) :
  f ctx₀ = f ctx₁ := function.has_frame_iff.mp f.has_frame h

parameter (R)
inductive Prog
| skip : Prog
| store (dst : Ident) (ind : option Expr) (val : Expr)
| seq (a : Prog) (b : Prog)
| branch (cond : Expr) (a : Prog) (b : Prog)
| loop (n : LoopBound) (b : Prog)

parameter {R}
def prog_repr [has_to_string R] : Prog → list string
| Prog.skip := [";"]
| (Prog.store dst ind val) := [(to_string dst) ++ (ind.elim "" (λ i, "[" ++ to_string i ++ "]")) ++ " := " ++ (to_string val) ++ ";"]
| (Prog.seq a b) := (prog_repr a) ++ (prog_repr b)
| (Prog.branch c a b) := ["if " ++ (to_string c)]
    ++ (prog_repr a).map (λ s, "  " ++ s)
    ++ ["else"]
    ++ (prog_repr b).map (λ s, "  " ++ s)
| (Prog.loop n b) := ["for at most some bounded # of times"]
    ++ (prog_repr b).map (λ s, "  " ++ s)

instance [has_to_string R] prog_to_string : has_to_string Prog := ⟨λ p, "\n".intercalate (prog_repr p)⟩



def Prog.eval : Prog → (Ident → IdentVal) → (Ident → IdentVal)
| Prog.skip ctx := ctx
| (Prog.store dst ind val) ctx := function.update ctx dst ((ctx dst).update (ind.map (λ i : Expr, (i.eval ctx).to_nat)) (val.eval ctx))
| (Prog.seq a b) ctx := b.eval (a.eval ctx)
| (Prog.branch cond a b) ctx := if 0 < (Expr.eval ctx cond).to_nat then a.eval ctx else b.eval ctx
| (Prog.loop n b) ctx := (nat.iterate b.eval (n ctx)) ctx

def alist.ilookup {α β : Type*} [decidable_eq α] [inhabited β] (s : alist (λ _ : α, β)) (a : α) : β :=
(s.lookup a).iget

-- Faster version of eval
-- TODO: which one should be the "main" one
def Prog.eval' : Prog → (alist (λ _ : Ident, IdentVal)) → (alist (λ _ : Ident, IdentVal))
| Prog.skip ctx := ctx
| (Prog.store dst ind val) ctx := ctx.insert dst ((ctx.ilookup dst).update (ind.map (λ i : Expr, (i.eval ctx.ilookup).to_nat)) (val.eval ctx.ilookup))
| (Prog.seq a b) ctx := b.eval' (a.eval' ctx)
| (Prog.branch cond a b) ctx := if 0 < (cond.eval ctx.ilookup).to_nat then a.eval' ctx else b.eval' ctx
| (Prog.loop n b) ctx := (nat.iterate b.eval' (n ctx.ilookup)) ctx

section frame

@[simp] def Expr.frame : Expr → finset Ident
| (Expr.lit r) := ∅
| (Expr.ident i) := {i}
| (Expr.access x n) := insert x n.frame
| (Expr.call o args) := finset.bUnion finset.univ (λ i, (args i).frame)

@[simp] lemma Expr_frame_coe_nat (n : ℕ) : (n : Expr).frame = ∅ := rfl
@[simp] lemma Expr_frame_coe_R (r : R) : (r : Expr).frame = ∅ := rfl
@[simp] lemma Expr_frame_coe_ident (i : Ident) : (i : Expr).frame = {i} := rfl


/-- The evaluation of an Expr depends only on the values in its frame -/
theorem frame_sound_Expr {e : Expr} {ctx₀ ctx₁ : Ident → IdentVal}
  (h : ∀ v ∈ e.frame, ctx₀ v = ctx₁ v) : e.eval ctx₀ = e.eval ctx₁ :=
begin
  induction e,
  case Expr.lit : { simp, },
  case Expr.ident : i { simp [h i _], },
  case Expr.access : x n ih { simp at h ⊢, specialize ih h.2, simp [ih, h.1], },
  case Expr.call : o args ih
  { simp, congr, ext i, apply ih, refine (λ v hv, h v _), simp, refine ⟨_, hv⟩, }
end

theorem Expr.has_frame (e : Expr) : function.has_frame (λ ctx, e.eval ctx : (Ident → IdentVal) → ExprVal) e.frame :=
by { rw function.has_frame_iff, intros c₁ c₂, apply frame_sound_Expr, }

@[simp]
def Prog.frame : Prog → finset Ident
| Prog.skip := ∅
| (Prog.store dst none val) := insert dst val.frame
| (Prog.store dst (some ind) val) := insert dst (ind.frame ∪ val.frame)
| (Prog.seq a b) := a.frame ∪ b.frame
| (Prog.branch cond a b) := cond.frame ∪ a.frame ∪ b.frame
| (Prog.loop n b) := n.frame ∪ b.frame

/-- Ident's not in the frame remain unchanged -/
theorem not_mem_Prog_frame {p : Prog} {s} (hs : s ∉ p.frame) (ctx : Ident → IdentVal) :
  p.eval ctx s = ctx s :=
begin
  induction p generalizing ctx,
  case Prog.skip : { simp [Prog.eval], },
  case Prog.store : dst ind val
  { suffices : s ≠ dst, { simp [Prog.eval, this] },
    rintro rfl, cases ind; simpa using hs, },
  case Prog.seq : a b ih₁ ih₂
  { simp [decidable.not_or_iff_and_not] at hs,
    simp [Prog.eval, ih₂ hs.2, ih₁ hs.1], },
  case Prog.branch : cond a b ih₁ ih₂
  { simp [decidable.not_or_iff_and_not] at hs,
    simp [Prog.eval], split_ifs, exacts [ih₁ hs.2.1 _, ih₂ hs.2.2 _], },
  case Prog.loop : n b ih
  { simp [Prog.eval],
    generalize : n ctx = n',
    induction n' with n' ihn', { refl, },
    simp [function.iterate_succ_apply'],
    rwa ih, simp [decidable.not_or_iff_and_not] at hs, exact hs.2, }
end

/-- If two contexts agree on a set S ⊇ p.frame, then they agree after the evaluation as well. -/
theorem frame_sound_Prog {p : Prog} {ctx₀ ctx₁ : Ident → IdentVal} {S : finset Ident} (hS : p.frame ⊆ S)
  (h : ∀ v ∈ S, ctx₀ v = ctx₁ v) {s} (hs : s ∈ S) : p.eval ctx₀ s = p.eval ctx₁ s :=
begin
  induction p generalizing ctx₀ ctx₁ s,
  case Prog.skip : { simpa [Prog.eval] using h _ hs, },
  case Prog.store : dst ind val
  { by_cases s_eq : s = dst, swap, { simpa [Prog.eval, s_eq] using h _ hs, },
    subst s_eq, simp [Prog.eval], congr' 1, { exact h _ hs, },
    { cases ind; simp, congr' 1, apply frame_sound_Expr, refine λ v hv, h v _, simp [finset.subset_iff] at hS, apply hS.2, left, exact hv, },
    apply frame_sound_Expr, refine λ v hv, h v _, cases ind; simp [finset.subset_iff] at hS, exacts [hS.2 _ hv, hS.2 _ (or.inr hv)], },
  case Prog.seq : a b ih₁ ih₂
  { simp [Prog.eval],
    simp at hS, refine ih₂ (finset.union_subset_right hS) _ hs,
    intros v hv, exact ih₁ (finset.union_subset_left hS) h hv, },
  case Prog.branch : cond a b ih₁ ih₂
  { have : cond.eval ctx₀ = cond.eval ctx₁,
    { apply frame_sound_Expr, refine λ v hv, h v _,
      simp [finset.subset_iff] at hS, exact hS (or.inl hv), },
    simp [Prog.eval, this], simp at hS, split_ifs,
    { exact ih₁ (finset.union_subset_left (finset.union_subset_right hS)) h hs, },
    exact ih₂ (finset.union_subset_right (finset.union_subset_right hS)) h hs, },
  case Prog.loop : n b ih
  { have : n ctx₀ = n ctx₁,
    { apply LoopBound.frame_sound, refine λ v hv, h v _, simp [finset.subset_iff] at hS, exact hS (or.inl hv), },
    simp [Prog.eval, this],
    generalize : n ctx₁ = n',
    induction n' with n' ihn generalizing s, { exact h _ hs, },
    simp [function.iterate_succ_apply'],
    refine ih _ @ihn hs, simp at hS, exact finset.union_subset_right hS, }
end

def Expr.to_loop_bound (e : Expr) : LoopBound :=
{ frame := e.frame,
  to_fun := λ ctx, (e.eval ctx).to_nat,
  has_frame := (Expr.has_frame e).postcomp _ }

@[simp] lemma Expr.to_loop_bound_to_fun (e : Expr) (ctx : Ident → IdentVal) : e.to_loop_bound ctx = (e.eval ctx).to_nat :=
by simp [Expr.to_loop_bound]


end frame

local infixr ` <;> `:1 := Prog.seq
local notation a ` ::= `:20 c := Prog.store a none c
local notation a ` ⟬ `:9000 i ` ⟭ ` ` ::= `:20 c := Prog.store a (some i) c
local notation x ` ⟬ `:9000 i ` ⟭ ` := Expr.access x i

parameter (R)
structure BoundedStreamGen (ι α : Type) :=
(current : ι)
(value : α)
(ready : Expr)
(next : Prog)
(valid : Expr)
(bound : LoopBound)
(initialize : Prog)

parameter {R}
@[ext]
theorem BoundedStreamGen.ext {ι α} {x y : BoundedStreamGen ι α} (h₀ : x.current = y.current)
  (h₁ : x.value = y.value) (h₂ : x.ready = y.ready) (h₃ : x.next = y.next) (h₄ : x.valid = y.valid)
  (h₅ : x.bound = y.bound) (h₆ : x.initialize = y.initialize) : x = y :=
by { cases x, cases y, dsimp only at *, subst_vars, }

variables {ι α : Type}

section functorality

@[simps]
instance : bifunctor BoundedStreamGen :=
{ bimap := λ _ _ _ _ i v g, { g with value := v g.value, current := i g.current } }

instance : is_lawful_bifunctor BoundedStreamGen :=
{ id_bimap := λ _ _ g, by ext; simp [bimap],
  bimap_bimap := λ _ _ _ _ _ _ i i' v v' g, by ext; simp [bimap] }

infixr ` <$₁> `:1 := bifunctor.fst
infixr ` <$₂> `:1 := bifunctor.snd

-- TODO: find a better way
variables {ι' α' : Type} (f : ι → ι') (g : α → α') (s : BoundedStreamGen ι α)
@[simp] lemma BSG_fst_value : (f <$₁> s).value = s.value := rfl
@[simp] lemma BSG_fst_ready : (f <$₁> s).ready = s.ready := rfl
@[simp] lemma BSG_fst_next : (f <$₁> s).next = s.next := rfl
@[simp] lemma BSG_fst_valid : (f <$₁> s).valid = s.valid := rfl
@[simp] lemma BSG_fst_bound : (f <$₁> s).bound = s.bound := rfl
@[simp] lemma BSG_fst_init : (f <$₁> s).initialize = s.initialize := rfl
@[simp] lemma BSG_snd_current : (g <$₂> s).current = s.current := rfl
@[simp] lemma BSG_snd_ready : (g <$₂> s).ready = s.ready := rfl
@[simp] lemma BSG_snd_next : (g <$₂> s).next = s.next := rfl
@[simp] lemma BSG_snd_valid : (g <$₂> s).valid = s.valid := rfl
@[simp] lemma BSG_snd_bound : (g <$₂> s).bound = s.bound := rfl
@[simp] lemma BSG_snd_init : (g <$₂> s).initialize = s.initialize := rfl

@[simp] lemma BSG_fst_current : (f <$₁> s).current = f s.current := rfl
@[simp] lemma BSG_snd_value : (g <$₂> s).value = g s.value := rfl

attribute [functor_norm] bifunctor.fst_snd bifunctor.snd_fst

end functorality

@[pattern]
def Prog.if1 (cond : Expr) (b : Prog) := Prog.branch cond b Prog.skip

def BoundedStreamGen.compile (g : BoundedStreamGen unit Prog) : Prog :=
g.initialize <;>
Ident.mk default Vars.break ::= (0 : ℕ) <;>
Prog.loop g.bound $
  Prog.if1 (Expr.call Op.not ![Ident.mk default Vars.break]) $
    Prog.if1 g.ready g.value <;>
    Prog.branch g.valid g.next (Ident.mk default Vars.break ::= (1 : ℕ))

parameter (R)
/-- Indicates that things of type α (which typically involve Expr R)'s can eval
  to things of type β given a context ctx : Ident → IdentVal R -/
class StreamEval (α β: Type) :=
(eval : α → (Ident → IdentVal) → β)

/-- An Compileable.compile (f, e) indicates that f describes how to compile e to a program -/
class Compileable (α β : Type) :=
(compile : α → β → Prog)

parameter {R}
-- This is ind_eval, but we need to support recursion so we extract it specifically
-- Mathlib's lack of computability bites here;
-- since finsupp is noncomputable (this is actually a controversial-ish decision from what I gather from the Zulip)
-- it poisons "eval_stream"
-- We only use +, finsupp.single and finsupp.zero (zero is computable), so maybe a TODO is a computable implementation
@[simp]
noncomputable def eval_stream {ι β : Type} [add_zero_class β] :
  ℕ → (Ident → IdentVal) → (BoundedStreamGen ((Ident → IdentVal) → ι) ((Ident → IdentVal) → β)) → (ι →₀ β)
| 0 _ _ := 0
| (n+1) ctx s :=
if (s.valid.eval ctx).to_nat = 1 then
  (if (s.ready.eval ctx).to_nat = 1 then finsupp.single (s.current ctx) (s.value ctx) else 0)
    + (eval_stream n (s.next.eval ctx) s)
else 0

instance base_eval : StreamEval Expr ExprVal :=
⟨λ e ctx, e.eval ctx⟩

instance base_eval_nat : StreamEval Expr ℕ :=
⟨λ e ctx, (e.eval ctx).to_nat⟩

instance base_eval_R : StreamEval Expr R :=
⟨λ e ctx, (e.eval ctx).to_r⟩

instance refl_eval {α : Type} : StreamEval α α := ⟨λ x _, x⟩

noncomputable instance ind_eval {ι ι' α β : Type} [StreamEval ι ι'] [StreamEval α β] [add_zero_class β] :
  StreamEval (BoundedStreamGen ι α) (ι' →₀ β) :=
{ eval := λ s ctx, eval_stream (s.bound ctx) (s.initialize.eval ctx)
  (StreamEval.eval <$₁> StreamEval.eval <$₂> s) }

/- Convenience instance for `unit` so we don't have to write `unit → R` and can directly go to R
TODO: Remove? -/
noncomputable instance unit_eval {α β : Type} [StreamEval α β] [add_zero_class β] :
  StreamEval (BoundedStreamGen unit α) β :=
{ eval := λ s ctx, (StreamEval.eval s ctx : unit →₀ β) () }

instance base_compile : Compileable (Expr → Prog) Expr :=
⟨λ c e, c e⟩

section laws
-- Law 1: eval frame should be frame
structure BoundedStreamGen.has_frame (x : BoundedStreamGen ι α) (ι' β) [StreamEval ι ι'] [StreamEval α β] (S : set Ident) :=
(current : function.has_frame (StreamEval.eval x.current : _ → ι') S)
(value : function.has_frame (StreamEval.eval x.value : _ → β) S)
(ready : ↑x.ready.frame ⊆ S)
(next : ↑x.next.frame ⊆ S)
(valid : ↑x.valid.frame ⊆ S)
(bound : ↑x.bound.frame ⊆ S)
(initialize : ↑x.initialize.frame ⊆ S)

theorem eval_has_frame_of_has_frame {ι' β S} [StreamEval ι ι'] [StreamEval α β] [add_zero_class β] {x : BoundedStreamGen ι α} (hx : x.has_frame ι' β S) :
  function.has_frame (StreamEval.eval x : _ → (ι' →₀ β)) S :=
begin
  sorry,
end


-- Law 2: eval for bound steps should make invalid

end laws

section variable_state

structure WithFrame (α : Type) : Type :=
(val : α)
(frame : finset NameSpace)

instance WithFrame_coe {α : Type} : has_coe (WithFrame α) α := ⟨WithFrame.val⟩

@[simp] lemma WithFrame_coe_val (x : WithFrame α) : x.val = (x : α) := rfl

@[simp] lemma WithFrame.val_eq (val : α) (frame : finset NameSpace) :
  (WithFrame.mk val frame : α) = val := rfl

@[simp] lemma WithFrame.frame_eq (val : α) (frame : finset NameSpace) :
  (WithFrame.mk val frame).frame = frame := rfl

parameter (R)
def WithFrame.is_sound (x : WithFrame α) (β : Type) [StreamEval α β] : Prop :=
function.has_frame (StreamEval.eval (x : α) : (Ident → IdentVal) → β) (Ident.ns⁻¹' x.frame)

parameter {R}
def WithFrame.fresh {β : Type} (x : finset NameSpace) (f : NameSpace → β) : WithFrame β :=
⟨f (fresh x), insert (fresh x) x⟩

lemma WithFrame.fresh_spec (x : finset NameSpace) ⦃v : Ident⦄ (hx : v.ns ∈ x) (v' : Vars) :
  v ≠ (fresh x)∷v' :=
by { rintro rfl, exact not_fresh_mem _ hx, }

lemma WithFrame.is_sound_of_fresh₁ {ι' β} [add_zero_class β] [StreamEval ι ι'] [StreamEval α β] (x : finset NameSpace) {f : NameSpace → BoundedStreamGen ι α}
  (hf : BoundedStreamGen.has_frame (f (fresh x)) ι β (Ident.ns⁻¹' (insert (fresh x) x))) :
  WithFrame.is_sound (WithFrame.fresh x f) (ι →₀ β) :=
begin
  simp [WithFrame.is_sound], sorry,
end

lemma WithFrame.is_sound_of_fresh₂ {β} [add_zero_class β] [StreamEval α β] (x : finset NameSpace) {f : NameSpace → (BoundedStreamGen unit α)}
  (hf : BoundedStreamGen.has_frame (f (fresh x)) unit β (Ident.ns⁻¹' (insert (fresh x) x))) :
  WithFrame.is_sound (WithFrame.fresh x f) β :=
begin
  simp [WithFrame.is_sound], sorry,
end


-- (current : ι)
-- (value : α)
-- (ready : Expr)
-- (next : Prog)
-- (valid : Expr)
-- (bound : Expr)
-- (initialize : Prog)

end variable_state
-- example (i : Ident) :  := rfl

section singleton
open Vars (i)

def BoundedStreamGen.singleton (a : WithFrame α) : WithFrame (BoundedStreamGen unit α) :=
WithFrame.fresh a.frame $ λ ns,
{ current := (),
  value := a,
  ready := (1 : ℕ),
  valid := ns∷i ⟪<⟫ (1 : ℕ),
  bound := ⟨∅, λ _, 1, function.has_frame.const _ _ _⟩,
  next := ns∷i ::= (1 : ℕ),
  initialize := ns∷i ::= (0 : ℕ) }

theorem singleton_spec {β : Type} [add_zero_class β] [StreamEval α β] (ctx : Ident → IdentVal) (a : WithFrame α)
  (h : WithFrame.is_sound a β) :
  (StreamEval.eval (BoundedStreamGen.singleton a).val ctx : β) = StreamEval.eval a.val ctx :=
begin
  simp only [BoundedStreamGen.singleton, WithFrame.fresh],
  have := WithFrame.fresh_spec a.frame, set ns := fresh a.frame,
  simp [StreamEval.eval, Prog.eval], rw [WithFrame.is_sound, function.has_frame_iff] at h,
  apply h, intros x hx, simp [this hx],
end

theorem singleton_frame_sound {β : Type} [add_zero_class β] [StreamEval α β] {a : WithFrame α}
  (h : WithFrame.is_sound a β) : WithFrame.is_sound (BoundedStreamGen.singleton a) β :=
begin
  simp only [BoundedStreamGen.singleton], apply WithFrame.is_sound_of_fresh₂,
  split,
  { simp [StreamEval.eval], apply function.has_frame.mono, apply function.has_frame.const, exact set.empty_subset _, },
  { simp, apply function.has_frame.mono, exact h, simp [set.preimage_subset_preimage_iff], },
  all_goals { simp [fin.forall_fin_two], },
end

end singleton



def BoundedStreamGen.expr_to_prog (inp : BoundedStreamGen unit Expr) : BoundedStreamGen unit Prog :=
{ current := (),
  value := NameSpace.reserved∷Vars.output ::= NameSpace.reserved∷Vars.output ⟪+⟫ inp.value,
  ready := inp.ready,
  next := inp.next,
  valid := inp.valid,
  bound := inp.bound,
  initialize := inp.initialize <;> NameSpace.reserved∷Vars.output ::= (0 : R) }

-- section example_singleton

-- def test : BoundedStreamGen ℤ unit (Expr ℤ) := M.get (BoundedStreamGen.singleton (10 : ℤ))

-- lemma test_eval : (StreamEval.eval (λ _, arbitrary (IdentVal ℤ)) test : ℤ) = 10 :=
-- by { simp [StreamEval.eval, test, Prog.eval, BoundedStreamGen.singleton], }

-- end example_singleton

section range

def range_aux (n : Expr) (v : Ident) : BoundedStreamGen Expr Expr :=
{ current := v,
  value := Expr.call Op.cast_r ![v],
  ready := (1 : ℕ),
  valid := v ⟪<⟫ n,
  next := v ::= v ⟪+⟫ (1 : ℕ),
  bound := (n : Expr).to_loop_bound,
  initialize := v ::= (0 : ℕ), }

def range (n : WithFrame Expr) : WithFrame (BoundedStreamGen Expr Expr) :=
WithFrame.fresh n.frame $ λ ns, range_aux n ns∷Vars.i

lemma range_spec_aux (bound n x₀ : ℕ) (hn : n ≤ x₀ + bound)
  (ctx : Ident → IdentVal)
  (n' : WithFrame Expr) (hn' : Expr.eval ctx n' = ExprVal.nat n)
  (n'_sound : WithFrame.is_sound n' ExprVal)
  (v : Ident) (hv : v.ns ∉ n'.frame) (hx₀ : ctx v = IdentVal.base (ExprVal.nat x₀)) :
  ∀ (t : ℕ), eval_stream bound ctx ((λ (e : Expr) ctx, (e.eval ctx).to_nat) <$₁> (λ (e : Expr) ctx, (e.eval ctx).to_r) <$₂> (range_aux n' v)) t =
   (if x₀ ≤ t ∧ t < n then (t : R) else 0) :=
begin
  induction bound with bound ih generalizing ctx x₀,
  { intro t, simp, split_ifs, { cases not_lt.mpr (hn.trans h.1) h.2, }, refl, },
  intro t, simp [range_aux, hx₀, hn', ← apply_ite _root_.ExprVal.nat, imp_false],
  by_cases h : x₀ < n, swap,
  { have h' : ¬(x₀ ≤ t ∧ t < n) := λ H, h (lt_of_le_of_lt H.1 H.2), simp [h, h'], },
  simp [h, Prog.eval, hx₀],
  rw [← range_aux, ih (function.update ctx v (IdentVal.base (ExprVal.nat $ x₀ + 1))) (x₀ + 1) _ _ _]; clear ih,
  { by_cases H : x₀ = t, { subst H, simp [h], }, simp [ne.le_iff_lt H, ← nat.succ_le_iff, H, nat.succ_eq_add_one], },
  { refine hn.trans (le_of_eq _), rw nat.succ_eq_add_one, ac_refl, },
  { simp only [WithFrame.is_sound, function.has_frame_iff, StreamEval.eval] at n'_sound, rw ← hn', apply n'_sound,
    simp_intros x hx, suffices : x ≠ v, { simp [this], }, rintro rfl, exact hv hx, },
  { simp, }
end

example (a b :ℕ) (h : a ≠ b) : a + 1 ≤ b ↔ a ≤ b :=
by { rw nat.succ_le_iff, exact (ne.le_iff_lt h).symm}

theorem range_spec (n : WithFrame Expr) (hn : WithFrame.is_sound n ExprVal) (ctx : Ident → IdentVal) (n' : ℕ)
  (hn' : Expr.eval ctx n = ExprVal.nat n') :
  (StreamEval.eval (range n).val ctx : ℕ →₀ R) = finsupp.indicator (finset.range n') (λ i _, (i : R)) :=
begin
  simp only [StreamEval.eval, range, WithFrame.fresh],
  have n_fresh := WithFrame.fresh_spec n.frame, set ns := fresh n.frame,
  ext t,
  convert range_spec_aux ((n : Expr).to_loop_bound ctx) n' 0 _ ((range_aux n ns∷Vars.i).initialize.eval ctx) n _ hn ns∷Vars.i _ _ t, { simp, },
  { simp [hn'], },
  { simp only [WithFrame.is_sound, function.has_frame_iff, StreamEval.eval] at hn, rw ← hn', apply hn, simp_intros x hx, suffices : x ≠ ns∷Vars.i, { simp [range_aux, Prog.eval, this], }, rintro rfl, exact n_fresh hx _ rfl, },
  { intro h, exact n_fresh h _ rfl, },
  { simp [range_aux, Prog.eval], },
end

end range

section contract

def contract (g : BoundedStreamGen ι α) : BoundedStreamGen unit α :=
(λ _, ()) <$₁> g

lemma contract_aux [add_comm_monoid α] (n : ℕ) (ctx : Ident → IdentVal)
  (g : BoundedStreamGen ((Ident → IdentVal) → ι) ((Ident → IdentVal) → α)) :
  (eval_stream n ctx ((λ _ _, ()) <$₁> g)) () = (eval_stream n ctx g).sum_range :=
begin
  induction n with n ih generalizing ctx, { simp, },
  simp,
  split_ifs,
  { simp [← ih (g.next.eval ctx)], }, -- Valid and ready
  { simp [← ih (g.next.eval ctx)], }, -- Valid but not ready
  refl, -- Invalid, both are 0
end

theorem contract_spec {β ι' : Type} [add_comm_monoid β] [StreamEval α β] [StreamEval ι ι']
  (s : BoundedStreamGen ι α) (ctx : Ident → IdentVal) :
  StreamEval.eval (contract s) ctx = (StreamEval.eval s ctx : ι' →₀ β).sum_range :=
by simpa [StreamEval.eval, contract, bifunctor.fst] with functor_norm
using contract_aux (s.bound ctx) (s.initialize.eval ctx)
      (StreamEval.eval <$₁> StreamEval.eval <$₂> s)

end contract

section repeat

end repeat

def flatten {ι₁ ι₂ α : Type} (outer : BoundedStreamGen ι₁ (BoundedStreamGen ι₂ α)) :
  BoundedStreamGen (ι₁ × ι₂) α :=
let inner := outer.value in
{ current := (outer.current, inner.current),
  value := inner.value,
  ready := outer.ready ⟪&&⟫ inner.ready,
  next := let next_outer := outer.next <;> inner.initialize in
  Prog.branch outer.ready
    (Prog.branch inner.valid inner.next next_outer)
    next_outer,
  valid := outer.valid,
  bound := sorry, --outer.bound ⟪*⟫ inner.bound, -- TODO: fix
  initialize := outer.initialize <;> inner.initialize }

-- def test₂ : BoundedStreamGen ℤ (Expr ℤ) (Expr ℤ) := range (40 : ℕ) vars.x
-- #eval trace_val $ to_string $ (contract test₂).expr_to_prog.compile
-- #eval (((contract test₂).expr_to_prog.compile.eval' ∅).ilookup vars.output).get none

def externVec (len : Expr) (inp : Ident) (inp_idx : Ident) : BoundedStreamGen Expr Expr :=
{ current := inp_idx,
  value := inp⟬ inp_idx ⟭,
  ready := inp_idx ⟪<⟫ len,
  next := inp_idx ::= inp_idx ⟪+⟫ (1 : ℕ),
  valid := inp_idx ⟪<⟫ len,
  bound := len.to_loop_bound,
  initialize := inp_idx ::= (0 : ℕ) }

def externCSRMat (l₁ l₂ : Expr) (rows cols data : Ident) (i j k : Ident) :
  BoundedStreamGen (Expr × Expr) Expr :=
{ current := (i, cols⟬j⟭),
  value := data⟬k⟭,
  ready := j ⟪<⟫ rows⟬i ⟪+⟫ (1 : ℕ)⟭,
  next :=
    k ::= k ⟪+⟫ (1 : ℕ) <;>
    Prog.branch (j ⟪<⟫ rows⟬i ⟪+⟫ (1 : ℕ)⟭)
      (j ::= j ⟪+⟫ (1 : ℕ))
      (i ::= i ⟪+⟫ (1 : ℕ)),
  valid := i ⟪<⟫ l₁,
  bound := sorry, --l₁ ⟪*⟫ l₂ ,
  initialize := i ::= (0 : ℕ) <;> j ::= (0 : ℕ) <;> k ::= (0 : ℕ), }


-- def test₃ : BoundedStreamGen ℤ (Expr ℤ) (Expr ℤ) := externVec (10 : ℕ) (Ident.of "input") (Ident.of "idx")

-- #eval trace_val $ to_string $ (contraction (Ident.of "acc") test₃).expr_to_prog.compile

end

-- Examples

-- section example_prog
-- namespace vars

-- abbreviation x := Ident.of "x"
-- abbreviation y := Ident.of "y"
-- abbreviation z := Ident.of "z"
-- abbreviation s := Ident.of "s"
-- abbreviation i := Ident.of "i"
-- abbreviation acc := Ident.of "acc"
-- abbreviation output := Ident.of "output"

-- end vars

-- open Expr Prog vars

-- def pow_prog : Prog ℤ :=
-- z ::= (1 : ℤ) <;>
-- loop ⟨_, _, function.has_frame.const _ _ 4⟩ (z ::= x ⟪*⟫ z)

-- def pow_prog_input (i : Ident) : IdentVal ℤ :=
--   if i = x then IdentVal.base (ExprVal.rval 3)
--   else if i = y then IdentVal.base (ExprVal.nat 4)
--   else arbitrary _

-- def arr_prog : Prog ℤ :=
-- s ::= (0 : ℤ) <;>
-- i ::= (0 : ℕ) <;>
-- loop (Expr.to_loop_bound y) $
--   s ::= s ⟪+⟫ x⟬i⟭ <;>
--   i ::= i ⟪+⟫ (1 : ℕ)

-- def arr_prog_input (i : Ident) : IdentVal ℤ :=
--   if i = x then IdentVal.arr [ExprVal.rval 30, ExprVal.rval (-1), ExprVal.rval 4]
--   else if i = y then IdentVal.base (ExprVal.nat 3)
--   else arbitrary _

-- def range_sum : Prog ℤ :=
-- s ::= (0 : ℤ) <;>
-- i ::= (0 : ℕ) <;>
-- loop ⟨_, _, function.has_frame.const _ _ 500⟩ $
--   s ::= s ⟪+⟫ (Expr.call Op.cast_r ![i]) <;>
--   i ::= i ⟪+⟫ (1 : ℕ)


-- end example_prog