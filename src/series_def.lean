import data.finset
import seq_def

namespace real_series

open real_seq

section sec_4_1

def partial_sum (a : seq) : seq := λ n, (finset.Ico 0 (n + 1)).sum a

end sec_4_1

end real_series