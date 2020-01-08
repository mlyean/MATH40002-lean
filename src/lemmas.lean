import data.real.basic

lemma div_lt_iff'' {a b c : ℝ} (hb : b > 0) (hc : c > 0) : a / b < c ↔ a / c < b :=
  by rw [div_lt_iff hb, div_lt_iff' hc]

lemma Sup_subset_le_Sup {A B : set ℝ} (h : B ⊆ A) (ha_bdd : bdd_above A) (hb_nonempty : B ≠ ∅) : real.Sup B ≤ real.Sup A := begin
  refine real.Sup_le_ub B (set.exists_mem_of_ne_empty hb_nonempty) _,
  intros x hx,
  exact real.le_Sup A ha_bdd (h hx),
end

lemma Inf_le_Inf_subset {A B : set ℝ} (h : B ⊆ A) (ha_bdd : bdd_below A) (hb_nonempty : B ≠ ∅) : real.Inf A ≤ real.Inf B := begin
  refine real.lb_le_Inf B (set.exists_mem_of_ne_empty hb_nonempty) _,
  intros x hx,
  exact real.Inf_le A ha_bdd (h hx),
end

lemma range_add_eq_Ici (n : ℕ) : set.range (+ n) = set.Ici n := begin
  refine set.ext _,
  intro x,
  simp,
  split,
  { rintro ⟨y, hy⟩,
    exact nat.le.intro hy,
  },
  { exact nat.le.dest }
end

lemma range_add_subset_range_add {m n : ℕ} (h : m ≤ n) : set.range (+ n) ⊆ set.range (+ m) := begin
  rw [range_add_eq_Ici, range_add_eq_Ici],
  intros x hx,
  exact le_trans h hx,
end