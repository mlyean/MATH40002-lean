import seq
import series_def
import algebra.geom_sum

namespace MATH40002

open real_seq
open real_series

section sec_4_1

-- Example 4.1
lemma sum_of_geom_series (x : ℝ) (hx : abs x < 1) : is_limit (geom_series x ∘ (+ 1)) (1 / (1 - x)) := begin
  have hx' : x ≠ 1 := ne_of_lt (abs_lt.mp hx).2,
  have h : geom_series x ∘ (+ 1) = λ n, (1 - x ^ (n + 1)) / (1 - x) := begin
    funext n,
    change geom_series x (n + 1) = _,
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
  rw ←lim_eq_lim_of_tail 1,
  exact lim_of_geom_zero' (abs_lt.mp hx),
end

end sec_4_1

end MATH40002