import seq
import series_def
import algebra.geom_sum

namespace MATH40002

open real_seq
open real_series

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
theorem harmonic_series_diverges : sum_to_inf_diverges_to_pos_inf (λ n, 1 / (n + 1)) := begin
  intros M hM,
  cases exists_nat_gt (2 * M) with M' hM',
  existsi 2 ^ (M' + 1),
  intros n hn,
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
    have : (n : ℝ) + 2 ≠ 0 := begin
      refine ne_of_gt _,
      norm_cast,
      norm_num,
    end,
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
    have : (n : ℝ) + 1 ≠ 0 := begin
      refine ne_of_gt _,
      norm_cast,
      norm_num,
    end,
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
    have hn : (n : ℝ) + 1 > 0 := by { norm_cast, norm_num },
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
    refine add_le_add_left _ _,
    refine le_of_neg_le_neg _,
    rw [neg_neg, neg_neg, one_div_le_one_div],
    repeat {
      norm_cast,
      norm_num,
    },
  },
end

lemma sum_one_div_pow_two : sum_to_inf_converges (λ n, 1 / (n + 1) ^ 2) := begin
  refine sum_of_nonneg_converges_of_bdd_above _ _,
  { intro n,
    change (0 : ℝ) ≤ (1 : ℝ) / (n + 1) ^ 2,
    refine le_of_lt (one_div_pos_of_pos (pow_pos _ 2)),
    norm_cast,
    norm_num,
  },
  { existsi (2 : ℝ),
    rintros x ⟨y, hy⟩,
    subst hy,
    calc
      partial_sum (λ n, (1 : ℝ) / (n + 1) ^ 2) y ≤ 2 - (1 : ℝ) / (y + 1) : partial_sum_one_div_pow_two y
        ... ≤ 2 : by { norm_num, norm_cast, norm_num, },
  }
end

end sec_4_1

end MATH40002