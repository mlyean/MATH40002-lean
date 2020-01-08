import data.finset
import seq_def

namespace real_series

open real_seq

section sec_4_1

def partial_sum (a : seq) : seq := λ n, (finset.Ico 0 n).sum a

lemma partial_sum_zero {a : seq} : partial_sum a 0 = 0 := finset.sum_range_zero a

lemma partial_sum_succ {a : seq} {n : ℕ} : partial_sum a (n + 1) = partial_sum a n + a n :=
  finset.sum_Ico_succ_top (nat.zero_le n) a

def sum_to_inf_eq (a : seq) := is_limit (partial_sum a)

def sum_to_inf_converges (a : seq) := seq_converges (partial_sum a)

def sum_to_inf_diverges (a : seq) := seq_diverges (partial_sum a)
def sum_to_inf_diverges_to_pos_inf (a : seq) := seq_diverges_to_pos_inf (partial_sum a)
def sum_to_inf_diverges_to_neg_inf (a : seq) := seq_diverges_to_neg_inf (partial_sum a)

end sec_4_1

end real_series