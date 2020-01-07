import data.finset
import seq_def

namespace real_series

open real_seq

section sec_4_1

def partial_sum (a : seq) : seq := λ n, (finset.Ico 0 n).sum a

def sum_to_inf_eq (a : seq) := is_limit (partial_sum a)

def sum_to_inf_converges (a : seq) := seq_converges (partial_sum a)

end sec_4_1

end real_series