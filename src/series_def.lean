import data.finset
import seq_def

namespace real_series

open real_seq

-- Sectioj 4.1 : Convergence of Series
section sec_4_1

def partial_sum (a : seq) : seq := λ n, (finset.Ico 0 n).sum a

@[simp] lemma partial_sum_zero {a : seq} : partial_sum a 0 = 0 := finset.sum_range_zero a

lemma partial_sum_succ {a : seq} {n : ℕ} : partial_sum a (n + 1) = partial_sum a n + a n :=
  finset.sum_Ico_succ_top (nat.zero_le n) a

lemma partial_sum_tail {a : seq} {n : ℕ} : partial_sum a (n + 1) = a 0 + partial_sum (a ∘ (+ 1)) n := begin
  unfold partial_sum,
  rw finset.sum_eq_sum_Ico_succ_bot (nat.succ_pos n) a,
  refine congr_arg (λ x, (a 0) + x) _,
  refine congr_arg multiset.sum _,
  conv_rhs { rw ←multiset.map_map },
  refine congr_arg (multiset.map a) _,
  rw [finset.Ico.val, finset.Ico.val, nat.succ_eq_add_one],
  have : (λ (x : ℕ), x + 1) = has_add.add 1 := funext (λ x, add_comm x 1),
  rw this,
  exact (multiset.Ico.map_add 0 n 1).symm,
end

lemma partial_sum_succ_sub (a : seq) (n : ℕ) : partial_sum a (n + 1) - partial_sum a n = a n := 
  sub_eq_iff_eq_add'.mpr partial_sum_succ

lemma partial_sum_sub {a : seq} {m n : ℕ} (hmn : m ≤ n) : partial_sum a n - partial_sum a m = (finset.Ico m n).sum a :=
begin
  unfold partial_sum,
  rw sub_eq_iff_eq_add',
  symmetry,
  exact finset.sum_Ico_consecutive a (zero_le m) hmn,
end

lemma partial_sum_smul {a : seq} {c : ℝ} : partial_sum (c • a) = c • partial_sum a :=
  funext (λ n, finset.sum_hom _ _)

def sum_to_inf_eq (a : seq) := is_limit (partial_sum a)
notation `∑ ` a ` ⟶ ` l := sum_to_inf_eq a l

def sum_to_inf_converges (a : seq) := seq_converges (partial_sum a)

def sum_to_inf_diverges (a : seq) := seq_diverges (partial_sum a)
def sum_to_inf_diverges_to_pos_inf (a : seq) := seq_diverges_to_pos_inf (partial_sum a)
def sum_to_inf_diverges_to_neg_inf (a : seq) := seq_diverges_to_neg_inf (partial_sum a)
notation `∑  ` a ` ⟶+∞` := sum_to_inf_diverges_to_pos_inf a
notation `∑ ` a ` ⟶-∞` := sum_to_inf_diverges_to_neg_inf a

end sec_4_1

-- Section 4.2 : Absolute Convergence
section sec_4_2

-- Absolute convergence
def abs_convergent (a : seq) := sum_to_inf_converges (abs ∘ a)

end sec_4_2

end real_series