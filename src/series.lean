import seq
import series_def
import algebra.geom_sum

namespace MATH40002

open real_seq
open real_series

section sec_4_1

-- Example 4.1
lemma sum_of_geom_series (x : ℝ) (hx : abs x < 1) : is_limit (geom_series x) (1 / (1 - x)) := begin
  have hx' : x ≠ 1 := ne_of_lt (abs_lt.mp hx).2,
  have h : geom_series x = λ n, (1 - x ^ n) / (1 - x) := begin
    funext n,
    rw [geom_sum hx', ←neg_div_neg_eq, neg_sub, neg_sub],
  end,
  rw h,
  conv {
    congr,
    skip,
    congr,
    rw ←sub_zero (1 : ℝ),
  },
  replace hx' := sub_ne_zero.mpr hx'.symm,
  refine lim_div_eq_div_lim hx' (lim_sub_eq_sub_lim lim_of_const_seq _) lim_of_const_seq,
  exact lim_of_geom_zero' (abs_lt.mp hx),
end

lemma partial_sum_succ_sub (a : seq) (n : ℕ) : partial_sum a (n + 1) - partial_sum a n = a n := begin
  unfold partial_sum,
  rw finset.sum_Ico_succ_top (nat.zero_le n),
  exact add_sub_cancel' (partial_sum a n) (a n),
end

-- Theorem 4.2 (Limit test)
theorem lim_of_terms_eq_zero (a : seq) (ha : sum_to_inf_converges a) : is_limit a 0 := begin
  have h : a = λ n, partial_sum a (n + 1) - partial_sum a n := begin
    funext n,
    exact (partial_sum_succ_sub a n).symm,
  end,
  cases ha with l hl,
  rw [h, ←sub_self l],
  exact lim_sub_eq_sub_lim ((lim_eq_lim_of_tail 1).mp hl) hl,
end

lemma harmonic_series_ineq (k : ℕ) : (partial_sum (λ n, 1 / (n + 1)) (2 ^ k)) ≥ 1 + k / 2 := begin
  unfold partial_sum,
  induction k with k hk,
  { simp },
  { rw nat.succ_eq_add_one,
    rw ←finset.sum_Ico_consecutive (λ n, 1 / ((n : ℝ) + 1)) (_ : 0 ≤ 2 ^ k) (_ : 2 ^ k ≤ 2 ^ (k + 1)),
    show 0 ≤ 2 ^ k, from nat.zero_le (2 ^ k),
    show 2 ^ k ≤ 2 ^ (k + 1), from nat.le_add_left (2 ^ k) _,
    rw [nat.cast_add, nat.cast_one, add_div, ←add_assoc],
    refine add_le_add hk _,
    have h : (2 ^ k : ℝ) ≠ 0 := by { norm_num, exact (ne_of_lt (pow_pos zero_lt_two k)).symm, },
    calc
      1 / 2 = 2 ^ k * (1 / 2 ^ (k + 1)) : by rw [←div_mul_left 2 h, ←pow_succ, div_eq_mul_one_div (2 ^ k : ℝ) (2 ^ (k + 1) : ℝ)]
        ... = (finset.Ico (2 ^ k) (2 ^ (k + 1))).sum (λ (n : ℕ), (1 : ℝ) / (2 ^ (k + 1))) : by {
          rw finset.sum_const _,
          rw finset.Ico.card,
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
          simp at hx,
          rw one_div_le_one_div,
          show (0 : ℝ) < 2 ^ (k + 1), from pow_pos zero_lt_two (k + 1),
          show 0 < (x : ℝ) + 1, by { norm_cast, exact nat.succ_pos x },
          norm_cast,
          exact hx.2,
        },
  }
end

lemma sum_monotone_of_nonneg_terms {a : seq} (ha : ∀ n, a n ≥ 0) : monotone (partial_sum a) := begin
  intros m n hmn,
  induction hmn with n hn ih,
  { exact le_refl (partial_sum a m) },
  { refine le_trans ih _,
    rw ←sub_nonneg,
    rw partial_sum_succ_sub,
    exact ha n,
  }
end

lemma harmonic_series_monotone : monotone (partial_sum (λ n, 1 / ((n : ℝ) + 1))) := begin
  refine sum_monotone_of_nonneg_terms _,
  intro n,
  norm_num,
  norm_cast,
  exact nat.zero_le (1 + n),
end

-- Example 4.4
theorem harmonic_series_diverges : sum_to_inf_diverges_to_pos_inf (λ n, 1 / ((n : ℝ) + 1)) := begin
  intros M hM,
  cases exists_nat_gt (2 * M) with M' hM',
  existsi 2 ^ (M' + 1),
  intros n hn,
  calc
    partial_sum (λ (n : ℕ), 1 / (↑n + 1)) n ≥ partial_sum (λ (n : ℕ), 1 / (↑n + 1)) (2 ^ (M' + 1)) : harmonic_series_monotone hn
      ... ≥ 1 + (M' + 1) / 2 : harmonic_series_ineq (M' + 1)
      ... > M : by linarith only [hM'],
end

end sec_4_1

end MATH40002