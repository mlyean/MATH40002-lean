import seq
import series_def
import algebra.geom_sum

namespace MATH40002

open real_seq
open real_series

-- Chapter 4 : Series

-- Section 4.1 : Convergence of Series
section sec_4_1

lemma sum_of_nonneg_monotone {a : seq} (ha : a ≥ 0) : monotone (partial_sum a) := begin
  intros m n hmn,
  induction hmn with n hn ih,
  { exact le_refl (partial_sum a m) },
  { refine le_trans ih _,
    rw [←sub_nonneg, partial_sum_succ_sub],
    exact ha n,
  }
end

lemma sum_of_pos_strict_mono {a : seq} (ha : a > 0) : strict_mono (partial_sum a) := begin
  intros m n hmn,
  induction hmn with n hn ih,
  { rw [partial_sum_succ, lt_add_iff_pos_right],
    exact ha m,
  },
  { rw partial_sum_succ,
    refine lt_trans ih _,
    rw lt_add_iff_pos_right,
    exact ha n,
  }
end

lemma sum_of_nonneg_converges_of_bdd_above {a : seq} (ha : a ≥ 0) (ha' : seq_bdd_above (partial_sum a)) :
  seq_converges (partial_sum a) := seq_converges_of_bdd_increasing (sum_of_nonneg_monotone ha) ha'

-- Example 4.1
lemma sum_of_geom_series (x : ℝ) (hx : abs x < 1) : geom_series x ⟶  1 / (1 - x) := begin
  have hx' : x ≠ 1 := ne_of_lt (abs_lt.mp hx).right,
  have : geom_series x = λ n, (1 - x ^ n) / (1 - x) :=
    funext (λ n, by rw [geom_sum hx', ←neg_div_neg_eq, neg_sub, neg_sub]),
  rw this,
  conv {
    congr,
    skip,
    congr,
    rw ←sub_zero (1 : ℝ),
  },
  replace hx' := sub_ne_zero.mpr hx'.symm,
  refine lim_div_eq_div_lim (lim_sub_eq_sub_lim lim_of_const_seq _) lim_of_const_seq hx',
  exact lim_of_geom_zero' (abs_lt.mp hx),
end

lemma sum_le_of_terms_le {a b : seq} (hab : a ≤ b) : partial_sum a ≤ partial_sum b := begin
  intro n,
  induction n with n hn,
  { rw [partial_sum_zero, partial_sum_zero] },
  { rw [partial_sum_succ, partial_sum_succ],
    exact add_le_add hn (hab n),
  }
end

-- Theorem 4.2 (Limit test)
theorem lim_of_terms_eq_zero (a : seq) (ha : sum_to_inf_converges a) : is_limit a 0 := begin
  cases ha with l hl,
  have : a = λ n, partial_sum a (n + 1) - partial_sum a n := funext (λ n, (partial_sum_succ_sub a n).symm),
  rw [this, ←sub_self l],
  exact lim_sub_eq_sub_lim ((lim_eq_lim_of_tail 1).mp hl) hl,
end

lemma harmonic_series_ineq (k : ℕ) : (partial_sum (λ n, 1 / (n + 1)) (2 ^ k)) ≥ 1 + k / 2 := begin
  unfold partial_sum,
  induction k with k hk,
  { norm_num, },
  { rw nat.succ_eq_add_one,
    rw ←finset.sum_Ico_consecutive (λ n, 1 / ((n : ℝ) + 1)) (_ : 0 ≤ 2 ^ k) (_ : 2 ^ k ≤ 2 ^ (k + 1)),
    show 0 ≤ 2 ^ k, from nat.zero_le (2 ^ k),
    show 2 ^ k ≤ 2 ^ (k + 1), from nat.le_add_left (2 ^ k) _,
    rw [nat.cast_add, nat.cast_one, add_div, ←add_assoc],
    refine add_le_add hk _,
    have h : (2 ^ k : ℝ) ≠ 0 := (ne_of_lt (pow_pos zero_lt_two k)).symm,
    calc
      1 / 2 = 2 ^ k * (1 / 2 ^ (k + 1)) : by rw [←div_mul_left 2 h, ←pow_succ, div_eq_mul_one_div (2 ^ k : ℝ) (2 ^ (k + 1) : ℝ)]
        ... = (finset.Ico (2 ^ k) (2 ^ (k + 1))).sum (λ (n : ℕ), (1 : ℝ) / (2 ^ (k + 1))) : by {
          rw [finset.sum_const _, finset.Ico.card],
          conv_rhs {
            congr,
            { rw [nat.pow_succ, mul_two, nat.add_sub_cancel] }
          },
          rw add_monoid.smul_eq_mul,
          norm_cast,
        }
        ... ≤ (finset.Ico (2 ^ k) (2 ^ (k + 1))).sum (λ (n : ℕ), (1 : ℝ) / (n + 1)) : by {
          refine finset.sum_le_sum _,
          intros x hx,
          rw finset.Ico.mem at hx,
          rw one_div_le_one_div,
          show (0 : ℝ) < 2 ^ (k + 1), from pow_pos zero_lt_two (k + 1),
          show 0 < (x : ℝ) + 1, from nat.cast_add_one_pos x,
          norm_cast,
          exact hx.2,
        },
  }
end

lemma harmonic_series_monotone : monotone (partial_sum (λ n, 1 / (n + 1))) :=
  sum_of_nonneg_monotone (λ n, le_of_lt nat.one_div_pos_of_nat)

-- Example 4.4
theorem harmonic_series_diverges_to_pos_inf : ∑ (λ n, 1 / (n + 1)) ⟶+∞ := begin
  intro M,
  cases exists_nat_gt (2 * M) with M' hM',
  existsi 2 ^ (M' + 1),
  intros n hn,
  refine le_of_lt _,
  calc
    partial_sum (λ n, 1 / (n + 1)) n ≥ partial_sum (λ (n : ℕ), 1 / (↑n + 1)) (2 ^ (M' + 1)) : harmonic_series_monotone hn
      ... ≥ 1 + (M' + 1) / 2 : harmonic_series_ineq (M' + 1)
      ... > (M' + 1) / 2 : lt_one_add (((M' : ℝ) + 1) / 2)
      ... > M : by { rw [gt_iff_lt, lt_div_iff' two_pos], exact lt_trans hM' (lt_add_one M'), }
end

-- Example 4.5
lemma partial_sum_one_div_mul_succ : partial_sum (λ n, 1 / ((n + 1) * (n + 2))) = λ n, 1 - 1 / (n + 1) := begin
  funext,
  induction n with n hn,
  { unfold partial_sum,
    simp, },
  { rw [partial_sum_succ, hn, sub_add, sub_left_inj, nat.succ_eq_add_one, nat.cast_add, nat.cast_one],
    have : (n : ℝ) + 2 ≠ 0 := ne_of_gt (by { norm_cast, norm_num }),
    rw [←div_mul_left ((n : ℝ) + 1) this, ←sub_div],
    conv_lhs {
      congr,
      { change (n : ℝ) + 2 + -1,
        rw add_assoc,
        congr,
        skip,
        change (1 + 1 : ℝ) - 1,
        rw add_sub_cancel (1 : ℝ) 1,
      }
    },
    have : (n : ℝ) + 1 ≠ 0 := ne_of_gt (nat.cast_add_one_pos n),
    rw [div_mul_right ((n : ℝ) + 2) this, add_assoc],
    refl,
  }
end

lemma sum_one_div_mul_succ : sum_to_inf_eq (λ n, 1 / ((n + 1) * (n + 2))) 1 := begin
  unfold sum_to_inf_eq,
  conv {
    congr,
    skip,
    rw ←sub_zero (1 : ℝ),
  },
  rw partial_sum_one_div_mul_succ,
  exact lim_sub_eq_sub_lim lim_of_const_seq lim_of_reciprocal,
end

lemma partial_sum_one_div_pow_two : partial_sum (λ n, 1 / ((n + 1) ^ 2)) ≤ λ n, 2 - 1 / (n + 1) := begin
  have h : partial_sum (λ n, 1 / ((n + 2) ^ 2)) ≤ λ n, 1 - 1 / (n + 1) := begin
    rw ←partial_sum_one_div_mul_succ,
    refine sum_le_of_terms_le _,
    intro n,
    have hn : (n : ℝ) + 1 > 0 := nat.cast_add_one_pos n,
    have hn' : (n : ℝ) + 2 > 0 := by { norm_cast, norm_num },
    change (1 : ℝ) / (↑n + 2) ^ 2 ≤ 1 / ((↑n + 1) * (↑n + 2)),
    rw one_div_le_one_div (pow_pos hn' 2) (mul_pos hn hn'),
    norm_cast,
    norm_num,
  end,
  intro n,
  change partial_sum (λ n, (1 : ℝ) / (n + 1) ^ 2) n ≤ 2 - (1 : ℝ) / (n + 1),
  induction n with n hn,
  { simp,
    norm_num, 
  },
  { rw [partial_sum_tail, nat.cast_zero, zero_add, one_pow, div_one, nat.succ_eq_add_one, nat.cast_add, nat.cast_one],
    change 1 + partial_sum ((λ (n : ℕ), 1 / (↑(n + 1) + 1) ^ 2)) n ≤ 2 - 1 / (↑n + 1 + 1),
    conv_lhs {
      congr,
      skip,
      congr,
      funext,
      rw [nat.cast_add, nat.cast_one, add_assoc],
      change (1 : ℝ) / (n + 2) ^ 2,
    },
    conv_rhs {
      congr,
      change (1 : ℝ) + 1,
      skip,
      rw add_assoc,
      change (1 : ℝ) / (↑n + 2),
    },
    change _ ≤ (1 : ℝ) + 1 + -((1 : ℝ) / (n + 2)),
    rw add_assoc,
    refine add_le_add_left _ _,
    change _ ≤ 1 - (1 : ℝ) / (↑n + 2),
    refine le_trans (h n) _,
    change (1 : ℝ) - 1 / (n + 1) ≤ 1 - 1 / (↑n + 2),
    refine add_le_add_left (le_of_neg_le_neg _) _,
    rw [neg_neg, neg_neg, one_div_le_one_div],
    repeat { norm_cast, norm_num },
  },
end

lemma sum_one_div_pow_two : sum_to_inf_converges (λ n, 1 / (n + 1) ^ 2) := begin
  refine sum_of_nonneg_converges_of_bdd_above _ _,
  { intro n,
    exact le_of_lt (one_div_pos_of_pos (pow_pos (nat.cast_add_one_pos n) 2)),
  },
  { existsi (2 : ℝ),
    rintros x ⟨y, hy⟩,
    subst hy,
    calc
      partial_sum (λ n, (1 : ℝ) / (n + 1) ^ 2) y ≤ 2 - (1 : ℝ) / (y + 1) : partial_sum_one_div_pow_two y
        ... ≤ 2 : by { rw [sub_le, sub_self], exact le_of_lt nat.one_div_pos_of_nat },
  }
end

-- Proposition 4.6
lemma sum_of_nonneg_converges_iff_bdd_above {a : seq} (ha : a ≥ 0) :
  sum_to_inf_converges a ↔ seq_bdd_above (partial_sum a) :=
begin
  split,
  { rintro ⟨s, hs⟩,
    exact bdd_above_of_converges (seq_converges_of_has_limit hs),
  },
  { exact sum_of_nonneg_converges_of_bdd_above ha }
end

lemma sum_of_nonneg_diverges_iff_not_bdd_above {a : seq} (ha : a ≥ 0) :
  sum_to_inf_diverges_to_pos_inf a ↔ ¬ seq_bdd_above (partial_sum a) :=
begin
  split,
  { exact seq_not_bdd_above_of_diverges_to_pos_inf },
  { intros ha' M,
    change ¬ ∃ x, ∀ y ∈ set.range (partial_sum a), y ≤ x at ha',
    push_neg at ha',
    rcases ha' M with ⟨y, ⟨⟨N, hN⟩, hM⟩⟩,
    subst hN,
    existsi N,
    intros n hn,
    exact le_of_lt (lt_of_lt_of_le hM (sum_of_nonneg_monotone ha hn)),
  }
end

-- Theorem 4.7 (Comparison Test)
theorem comparison_test {a b : seq} (ha : a ≥ 0) (hab : a ≤ b) (hb : sum_to_inf_converges b) :
  sum_to_inf_converges a :=
begin
  refine sum_of_nonneg_converges_of_bdd_above ha _,
  rw sum_of_nonneg_converges_iff_bdd_above (le_trans ha hab) at hb,
  cases hb with B hB,
  existsi B,
  rintros x ⟨y, hy⟩,
  subst hy,
  exact le_trans (sum_le_of_terms_le hab y) (hB (set.mem_range_self y)),
end

-- Theorem 4.9 (Algebra of Limits)
theorem sum_add_eq_add_sum {a b : seq} {la lb : ℝ} (hla : (∑ a ⟶ la)) (hlb : ∑ b ⟶ lb) :
  ∑ a + b ⟶ la + lb :=
begin
  unfold sum_to_inf_eq partial_sum,
  conv {
    congr,
    funext,
    erw finset.sum_add_distrib,
  },
  exact lim_add_eq_add_lim hla hlb,
end

theorem sum_smul_eq_mul_sum {a : seq} {la : ℝ} (c : ℝ) (hla : (∑ a ⟶ la)) :
  ∑ c • a ⟶ c * la :=
begin
  unfold sum_to_inf_eq partial_sum,
  conv {
    congr,
    funext,
    erw ←finset.mul_sum,
  },
  exact lim_mul_eq_mul_lim lim_of_const_seq hla,
end

end sec_4_1

-- Section 4.2 : Absolute Convergence
section sec_4_2

-- Example 4.10
example : ¬ abs_convergent (λ n, (-1) ^ n / (n + 1)) := begin
  unfold abs_convergent,
  have : abs ∘ (λ (n : ℕ), (-1 : ℝ) ^ n / (n + 1)) = λ (n : ℕ), (1 : ℝ) / (n + 1) := begin
    funext n,
    change abs ((-1 : ℝ) ^ n / (n + 1)) = 1 / (n + 1),
    rw [abs_div, ←pow_abs, abs_neg, abs_one, one_pow],
    refine congr_arg _ (abs_of_pos _),
    exact nat.cast_add_one_pos n,
  end,
  rw this,
  exact seq_diverges_of_diverges_to_pos_inf harmonic_series_diverges_to_pos_inf,
end

example : sum_to_inf_converges (λ n, (-1) ^ n / (n + 1)) := begin
  sorry,
end

lemma sum_to_inf_converges_iff_cauchy {a : seq} : sum_to_inf_converges a ↔ seq_cauchy (partial_sum a) :=
begin
  unfold sum_to_inf_converges,
  exact converges_iff_cauchy,
end

lemma partial_sum_cauchy_iff {a : seq} :
  seq_cauchy (partial_sum a) ↔ ∀ ε > 0, ∃ N, ∀ (m ≥ N) (n ≥ m), abs ((finset.Ico m n).sum a) < ε :=
begin
  rw cauchy_iff,
  refine forall_congr (λ ε, _),
  refine imp_congr iff.rfl _,
  refine exists_congr (λ N, _),
  refine forall_congr (λ m, _),
  refine imp_congr iff.rfl _,
  refine forall_congr (λ n, _),
  refine forall_congr (λ hmn, _),
  rwa partial_sum_sub hmn,
end

-- Theorem 4.11
theorem convergent_of_abs_convergent {a : seq} (ha : abs_convergent a) : sum_to_inf_converges a := begin
  unfold abs_convergent at ha,
  rw [converges_iff_cauchy, partial_sum_cauchy_iff] at ha,
  rw [sum_to_inf_converges_iff_cauchy, cauchy_iff],
  intros ε hε,
  cases ha ε hε with N hN,
  existsi N,
  intros m hm n hn,
  rw partial_sum_sub hn,
  calc
    abs (finset.sum (finset.Ico m n) a) ≤ finset.sum (finset.Ico m n) (abs ∘ a) : finset.abs_sum_le_sum_abs
      ... ≤ abs (finset.sum (finset.Ico m n) (abs ∘ a)) : le_abs_self _
      ... < ε : hN m hm n hn,
end

end sec_4_2

-- Section 4.3 : Tests for Convergence
section sec_4_3

-- Theorem 4.18 (Comparison II)
theorem comparison_test₂ {a b c : seq} (hca : c ≤ a) (hab : a ≤ b)
  (hc : sum_to_inf_converges c) (hb : sum_to_inf_converges b) :
  sum_to_inf_converges a :=
begin
  rw [sum_to_inf_converges_iff_cauchy, partial_sum_cauchy_iff] at *,
  intros ε hε,
  cases hb ε hε with Nb hNb,
  cases hc ε hε with Nc hNc,
  let N := max Nb Nc,
  existsi N,
  intros m hm n hn,
  rw abs_lt,
  split,
  { have : -ε < finset.sum (finset.Ico m n) c :=
      (abs_lt.mp (hNc m (le_trans (le_max_right _ _) hm) n hn)).left,
    refine lt_of_lt_of_le this (finset.sum_le_sum _),
    intros k hk,
    exact hca k,
  },
  { have : finset.sum (finset.Ico m n) b < ε := 
      (abs_lt.mp (hNb m (le_trans (le_max_left _ _) hm) n hn)).right,
    refine lt_of_le_of_lt (finset.sum_le_sum _) this,
    intros k hk,
    exact hab k,
  }
end

-- Exercise 4.21
lemma sum_to_inf_converges_iff_tail_converges {a : seq} (N : ℕ) :
  sum_to_inf_converges (a ∘ (+ N)) ↔ sum_to_inf_converges a :=
begin
  unfold sum_to_inf_converges,
  conv_rhs {
    rw seq_converges_iff_tail_converges N,
  },
  have : (partial_sum a) ∘ (+ N) = λ n, (partial_sum a N) + (partial_sum (a ∘ (+ N)) n) := begin
    funext n,
    unfold partial_sum function.comp,
    simp only [add_comm],
    rw [finset.sum_Ico_add, zero_add, add_comm],
    symmetry,
    exact finset.sum_Ico_consecutive _ (zero_le N) (nat.le_add_left N n),
  end,
  rw this,
  conv_rhs {
    congr,
    change const_seq (partial_sum a N) + partial_sum (a ∘ (+ N)),
    rw add_comm,
  },
  exact seq_converges_iff_add_converges.symm,
end

-- Theorem 4.19 (Comparison III)
theorem comparison_test₃ {a b : seq} (hb : abs_convergent b) (hb' : ∀ n, b n ≠ 0) (hab : seq_converges (a / b)) :
  abs_convergent a :=
begin
  sorry,
end

-- Theorem 4.22 (Alternating Series Test)
theorem alternating_series_test {a : seq} (ha : seq_decreasing a) (ha' : a ⟶ 0) :
  sum_to_inf_converges ((λ n, (-1) ^ n) * a) :=
begin
  sorry,
end

-- Theorem 4.23 (Ratio Test)
theorem ratio_test {a : seq} {l : ℝ} (ha : (a ∘ (+1)) / a ⟶ l) (hl : l < 1) : abs_convergent a := begin
  sorry,
end

-- Theorem 4.25 (Root Test)
theorem root_test {a : seq} {r : ℝ} (ha : (λ n, abs (a n) ^ (1 / n)) ⟶ r) (hr : r < 1) : abs_convergent a := begin
  sorry,
end

end sec_4_3

end MATH40002