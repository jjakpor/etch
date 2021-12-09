import algebra
import algebra.group
import algebra.group.defs
import tactic
import logic.relation
import base
import stream
import data.stream.basic

namespace iter

section params_unary
variables {σ I V : Type} [linear_order I]
[decidable_eq σ]
(a : iter σ I V)
variables (s t : σ)

@[simp] lemma mono_iff_delta_mono {a : iter σ I V} : a.monotonic ↔ ∀ t, a.ι t ≤ a.ι (a.δ t) := begin
split, {intros m t, exact m _ _ (iter.transition.step a)},
{ intro h, intros w x path, obtain ⟨len, h⟩ : _ := index_of_path path,
  rw h,
  induction len with pl h1 generalizing x w,
  simp only [pow_zero, one_smul, le_refl],
  exact calc
  a.ι w ≤ a.ι (a.δ ^ pl • w)       : by {exact h1 _ w (path_of_index _ _) rfl}
    ... ≤ a.ι (a.δ • a.δ ^ pl • w) : by {apply h}
    ... ≤ a.ι (a.δ ^ pl.succ • w)  : by {simp only [← mul_smul],
                                     change a.ι ((a.δ^1 * a.δ ^ pl) w) ≤ a.ι ((a.δ ^ pl.succ) w),
                                     simp only [← pow_add, add_comm, le_refl]}
},
end

end params_unary

section params_binary
variables {σ₁ σ₂ I V : Type} [linear_order I] [decidable_eq σ₁] [decidable_eq σ₂] [add_comm_monoid V]
(a : iter σ₁ I V) (b : iter σ₂ I V)

lemma add_ι_min {s} : (a+'b).ι s = min (a.ι s.1) (b.ι s.2) := begin
cases s with s₁ s₂,
rw [iter.ι],
simp only [add_iter, iter.emit],
rw min_def,
obtain (h|h|h) := lt_trichotomy (a.ι s₁) (b.ι s₂),
{
    repeat {simp only [h]},
    simp only [add_emit];
    split_ifs,
    repeat {refl}, -- 2
    repeat {exfalso, exact h_2 (le_of_lt h)}, --2
}, swap,
{
    simp only [add_emit];
    split_ifs with h1 h2 h3,
    repeat {refl}, -- 2
    repeat {exfalso, exact h2 (le_of_lt h1)}, --1
    rw le_antisymm h3 (le_of_lt h), refl,
},
{
    simp only [add_emit],
    split_ifs,
    repeat{refl}, --2
    repeat {simpa [h]}, --2
    { -- main case
        cases h4 : a.emit s₁ with v1; cases h5 : b.emit s₂ with v2,
        { simp only [option.lift_or_get, iter.ι, h4, h5],  },
        repeat { try {cases v1}, try {cases v2}, simpa only [iter.ι, h4, h5] using h }
    },
    { exfalso, exact h_3 (le_of_eq h) }
},
end

lemma step_dichotomy_1 (s₁:σ₁)(s₂:σ₂) : ((a +'b).δ (s₁,s₂)).1 = a.δ s₁ ∨ ((a +'b).δ (s₁,s₂)).1 = s₁ := begin
simp only [add_iter, iter.δ], split_ifs, tidy, --exact or.inl rfl, exact or.inr rfl, exact or.inl rfl,
end
lemma step_dichotomy_2 (s₁:σ₁)(s₂:σ₂) : ((a +'b).δ (s₁,s₂)).2 = b.δ s₂ ∨ ((a +'b).δ (s₁,s₂)).2 = s₂ := begin
simp only [add_iter, iter.δ], split_ifs, tidy, -- exact or.inr rfl, exact or.inl rfl, exact or.inl rfl,
end
theorem add_iter_monotonic (s₁:σ₁) (s₂:σ₂) : a.monotonic → b.monotonic → (a +' b).monotonic := begin
intros m1 m2, simp only [mono_iff_delta_mono],

rintro ⟨t₁, t₂⟩, simp only [add_ι_min],
apply min_le_min _ _,

{ obtain (h|h) := step_dichotomy_1 a b t₁ t₂; rw h,
  apply mono_iff_delta_mono.1 m1,
  apply le_refl _ },

{ obtain (h|h) := step_dichotomy_2 a b t₁ t₂; rw h,
  apply mono_iff_delta_mono.1 m2,
  apply le_refl _ }
end

-- todo

theorem add_iter_strict    (s₁:σ₁) (s₂:σ₂) : a.strict → b.strict → (a +' b).strict := sorry
-- todo: j needs to be sufficiently large (and statement not true ∀j)
theorem add_iter_sound     (s₁:σ₁) (s₂:σ₂) : ∃ j, ⟦a +' b, (s₁,s₂)⟧ j = ⟦a, s₁⟧ j + ⟦b, s₂⟧ j := sorry

end params_binary

end iter
