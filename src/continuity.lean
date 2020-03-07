import continuity_def

namespace continuity

open real_seq

section sec_5_1

lemma limits_unique {f : ℝ → ℝ} {x l₁ l₂ : ℝ} (hl₁ : limit_eq f x l₁) (hl₂ : limit_eq f x l₂) : l₁ = l₂ := begin
  refine close_implies_eq _,
  intros ε hε,
  rcases hl₁ (ε / 2) (half_pos hε) with ⟨δ₁, hδ₁, hδ₁'⟩,
  rcases hl₂ (ε / 2) (half_pos hε) with ⟨δ₂, hδ₂, hδ₂'⟩,
  let δ := min δ₁ δ₂,
  have hδ : δ > 0 := lt_min hδ₁ hδ₂,
  replace hδ₁' := hδ₁' (x + δ / 2) _,
  replace hδ₂' := hδ₂' (x + δ / 2) _,
  calc
    abs (l₁ - l₂) ≤ abs (l₁ - f (x + δ / 2)) + abs (f (x + δ / 2) - l₂) : abs_sub_le _ _ _
      ... = abs (f (x + δ / 2) - l₁) + abs (f (x + δ / 2) - l₂) : by rw abs_sub
      ... < ε / 2 + ε / 2 : add_lt_add hδ₁' hδ₂'
      ... = ε : add_halves ε,
  all_goals {
    rw [add_sub_cancel', abs_of_pos (half_pos hδ)],
    split,
    { exact half_pos hδ },
    { refine lt_of_lt_of_le (half_lt_self hδ) _,
      try { exact min_le_left _ _, },
      try { exact min_le_right _ _, },
    }
  },
end

-- Example 5.3
example : ¬ continuous_at (λ x, ite (x ≤ 0) 0 1) 0 := begin
  let f : ℝ → ℝ := λ x, ite (x ≤ 0) 0 1,
  change ¬ continuous_at f 0,
  unfold continuous_at,
  push_neg,
  existsi (1 : ℝ),
  split,
  { exact zero_lt_one },
  { intros δ hδ,
    existsi δ / 2,
    split,
    { rw [sub_zero, abs_of_pos (half_pos hδ)],
      exact half_lt_self hδ,
    },
    { refine le_of_eq _,
      have h₁ : f 0 = 0 := if_pos (le_refl 0),
      have h₂ : f (δ / 2) = 1 := if_neg (not_le_of_gt (half_pos hδ)),
      rw [h₁, h₂, sub_zero, abs_of_pos],
      exact zero_lt_one,
    }
  }
end

-- Example 5.5
example (m c : ℝ) : continuous (λ x, m * x + c) := begin
  intros a ε hε,
  sorry,
end

-- Example 5.6
example (m c : ℝ) : continuous (^2) := begin
  intros a ε hε,
  sorry,
end

local attribute [instance] classical.prop_decidable

-- Theorem 5.9 (Theorem 1.1 of term 2)
theorem continuous_iff_seq_continuous {f : ℝ → ℝ} {a : ℝ} :
  continuous_at f a ↔ ∀ (x : seq), (x ⟶ a) → (f ∘ x ⟶ f a) :=
begin
  split,
  { intros h x hx ε hε,
    rcases h ε hε with ⟨δ, hδ₁, hδ₂⟩,
    cases hx δ hδ₁ with N hN,
    existsi N,
    intros n hn,
    exact hδ₂ (x n) (hN n hn),
  },
  { intro h,
    unfold continuous_at,
    by_contradiction h₂,
    push_neg at h₂,
    rcases h₂ with ⟨ε, ⟨hε₁, hε₂⟩⟩,
    refine not_forall_of_exists_not _ h,
    let x : seq := λ n, classical.some (hε₂ (1 / (n + 1)) nat.one_div_pos_of_nat),
    existsi x,
    push_neg,
    split,
    { intros ε hε,
      cases exists_nat_one_div_lt hε with N hN,
      existsi N,
      intros n hn,
      calc
        abs (x n - a) < 1 / (n + 1) : (classical.some_spec (hε₂ (1 / (n + 1)) _)).left
          ... ≤ 1 / (N + 1) : nat.one_div_le_one_div hn
          ... < ε : hN,
    },
    { unfold is_limit,
      push_neg,
      existsi ε,
      split,
      { exact hε₁ },
      { intro N,
        existsi N,
        split,
        { exact le_refl N },
        { exact (classical.some_spec (hε₂ (1 / (N + 1)) _)).right }
      }
    }
  }
end

end sec_5_1

section sec_1_0

-- Proposition 1.2 (Algebra of Continuous Functions)
section algebra_of_continuous_fns

theorem cont_of_add_cont {f g : ℝ → ℝ} {a : ℝ} (hf : continuous_at f a) (hg : continuous_at g a) :
  continuous_at (λ x, f x + g x) a :=
begin
  rw continuous_iff_seq_continuous at *,
  intros x hx,
  exact lim_add_eq_add_lim (hf x hx) (hg x hx),
end

theorem cont_of_sub_cont {f g : ℝ → ℝ} {a : ℝ} (hf : continuous_at f a) (hg : continuous_at g a) :
  continuous_at (λ x, f x - g x) a :=
begin
  rw continuous_iff_seq_continuous at *,
  intros x hx,
  exact lim_sub_eq_sub_lim (hf x hx) (hg x hx),
end

theorem cont_of_mul_cont {f g : ℝ → ℝ} {a : ℝ} (hf : continuous_at f a) (hg : continuous_at g a) :
  continuous_at (λ x, f x * g x) a :=
begin
  rw continuous_iff_seq_continuous at *,
  intros x hx,
  exact lim_mul_eq_mul_lim (hf x hx) (hg x hx),
end

theorem cont_of_div_cont {f g : ℝ → ℝ} {a : ℝ} (hf : continuous_at f a) (hg : continuous_at g a) (hga : g a ≠ 0) :
  continuous_at (λ x, f x / g x) a :=
begin
  rw continuous_iff_seq_continuous at *,
  intros x hx,
  refine lim_div_eq_div_lim (hf x hx) (hg x hx) hga,
end

end algebra_of_continuous_fns

-- Proposition 1.3
lemma cont_of_comp_cont {f g : ℝ → ℝ} {a : ℝ} (hf : continuous_at f a) (hg : continuous_at g (f a)) :
  continuous_at (g ∘ f) a :=
begin
  rw continuous_iff_seq_continuous at *,
  intros x hx,
  refine hg (f ∘ x) _,
  exact hf x hx,
end

end sec_1_0

section sec_1_1

end sec_1_1

end continuity