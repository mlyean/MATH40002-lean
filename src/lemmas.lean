import data.real.basic
import data.set.basic

lemma finite.nat (s : set ℕ) : set.finite s ↔ ∃ n, ∀ m > n, m ∉ s := begin
  split,
  { intro h,
    apply classical.by_contradiction,
    intro hs,
    push_neg at hs,
    have hs' : s.nonempty := begin
      rcases hs 0 with ⟨m, ⟨hm₁, hm₂⟩⟩,
      existsi m,
      exact hm₂,
    end,
    rcases set.finite.exists_maximal_wrt id s h hs' with ⟨m, ⟨hm₁, hm₂⟩⟩,
    change ∀ k ∈ s, m ≤ k → m = k at hm₂,
    rcases hs m with ⟨M, ⟨hM₁, hM₂⟩⟩,
    exact ne_of_lt hM₁ (hm₂ M hM₂ (le_of_lt hM₁)),
  },
  { rintro ⟨n, hn⟩,
    have h : s ⊆ (finset.range (n + 1)).to_set := begin
      intros x hx,
      show x ∈ finset.range (n + 1),
      rw finset.mem_range,
      refine lt_of_not_ge _,
      intro hx',
      exact hn x hx' hx,
    end,
    exact set.finite_subset (finset.finite_to_set _) h,
  }
end

lemma infinite.nat (s : set ℕ) : set.infinite s ↔ ∀ n, ∃ m > n, m ∈ s := begin
  unfold set.infinite,
  rw finite.nat,
  finish,
end

lemma div_lt_iff'' {a b c : ℝ} (hb : b > 0) (hc : c > 0) : a / b < c ↔ a / c < b :=
  by rw [div_lt_iff hb, div_lt_iff' hc]

lemma Sup_subset_le_Sup {A B : set ℝ} (h : B ⊆ A) (ha_bdd : bdd_above A) (hb_nonempty : B.nonempty) : real.Sup B ≤ real.Sup A := begin
  refine real.Sup_le_ub B (hb_nonempty) _,
  intros x hx,
  exact real.le_Sup A ha_bdd (h hx),
end

lemma Inf_le_Inf_subset {A B : set ℝ} (h : B ⊆ A) (ha_bdd : bdd_below A) (hb_nonempty : B.nonempty) : real.Inf A ≤ real.Inf B := begin
  refine real.lb_le_Inf B (hb_nonempty) _,
  intros x hx,
  exact real.Inf_le A ha_bdd (h hx),
end

lemma range_add_eq_Ici (n : ℕ) : set.range (+ n) = set.Ici n := begin
  refine set.ext _,
  intro x,
  simp,
  split,
  { rintro ⟨y, hy⟩,
    subst hy,
    exact nat.le_add_left n y,
  },
  { intro h,
    existsi x - n,
    exact nat.sub_add_cancel h,
  }
end

lemma range_add_subset_range_add {m n : ℕ} (h : m ≤ n) : set.range (+ n) ⊆ set.range (+ m) := begin
  rw [range_add_eq_Ici, range_add_eq_Ici],
  intros x hx,
  exact le_trans h hx,
end