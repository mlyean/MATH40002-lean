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

end sec_4_1

end MATH40002