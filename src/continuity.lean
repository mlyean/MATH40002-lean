import continuity_def

namespace continuity

section sec_5_1

open real_seq

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

-- Example 5.2
section ex_5_2

noncomputable def f (x : ℝ) : ℝ := if x ≤ 0 then 0 else 1

example : ¬ continuous_at f 0 := begin
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

end ex_5_2

end sec_5_1

end continuity