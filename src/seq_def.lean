import data.real.basic

namespace real_seq

def seq : Type := ℕ → ℝ

-- Basic operations on sequences
def const_seq (x : ℝ) : seq := λ _, x
def zero_seq : seq := const_seq 0
def one_seq : seq := const_seq 1
def add_seq (a b : seq) : seq := λ n, a n + b n
def mul_seq (a b : seq) : seq := λ n, a n * b n
noncomputable def inv_seq (a : seq) : seq := λ n, (a n)⁻¹
def neg_seq (a : seq) : seq := λ n, -a n
def sub_seq (a b : seq) : seq := λ n, a n - b n
noncomputable def div_seq (a b : seq) : seq := λ n, a n / b n

-- Properties of sequences
instance : has_zero seq := ⟨zero_seq⟩
instance : has_one seq := ⟨one_seq⟩
instance : has_add seq := ⟨add_seq⟩
instance : has_mul seq := ⟨mul_seq⟩
noncomputable instance : has_inv seq := ⟨inv_seq⟩
instance : has_neg seq := ⟨neg_seq⟩
instance : has_sub seq := ⟨sub_seq⟩
noncomputable instance : has_div seq := ⟨div_seq⟩

protected lemma add_assoc (a b c : seq) : a + b + c = a + (b + c) := begin
  funext,
  exact add_assoc (a n) (b n) (c n),
end

protected lemma zero_add (a : seq) : 0 + a = a := begin
  funext,
  exact zero_add (a n),
end

protected lemma add_zero (a : seq) : a + 0 = a := begin
  funext,
  exact add_zero (a n),
end

protected lemma add_left_neg (a : seq) : -a + a = 0 := begin
  funext,
  exact add_left_neg (a n),
end

protected lemma add_comm (a b : seq) : a + b = b + a := begin
  funext,
  exact add_comm (a n) (b n),
end

instance : add_comm_group seq := {
  add := real_seq.add_seq,
  add_assoc := real_seq.add_assoc,
  zero := real_seq.zero_seq,
  zero_add := real_seq.zero_add,
  add_zero := real_seq.add_zero,
  neg := real_seq.neg_seq,
  add_left_neg := real_seq.add_left_neg,
  add_comm := real_seq.add_comm,
}

-- Section 3.1 : Convergence of Sequences
section sec_3_1

-- Boundedness
def seq_bdd_above (a : seq) := bdd_above (set.range a)
def seq_bdd_below (a : seq) := bdd_below (set.range a)
def seq_bdd (a : seq) := ∃ M > 0, ∀ n, abs (a n) ≤ M

-- Limits
def is_limit (a : seq) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, abs ((a n) - l) < ε

-- Convergence
def seq_converges (a : seq) := ∃ (l : ℝ), is_limit a l

lemma seq_converges_of_has_limit {a : seq} {l : ℝ} : is_limit a l → seq_converges a := begin
  intro H,
  existsi l,
  exact H,
end

-- Divergence
def seq_diverges (a : seq) := ¬ seq_converges a
def seq_diverges_to_pos_inf (a : seq) := ∀ M > 0, ∃ N, ∀ n ≥ N, a n > M
def seq_diverges_to_neg_inf (a : seq) := seq_diverges_to_pos_inf (-a)

lemma seq_diverges_iff {a : seq} : seq_diverges a ↔ ∀ (l : ℝ), ∃ ε > 0, ∀ N, ∃ n ≥ N, abs ((a n) - l) ≥ ε := begin
  unfold seq_diverges seq_converges is_limit,
  push_neg,
  simp,
end

-- Monotonicity
def seq_increasing (a : seq) := monotone a
def seq_decreasing (a : seq) := monotone (-a : seq)

end sec_3_1

-- Section 3.2 : Cauchy Sequences
section sec_3_2

-- Cauchy
def seq_cauchy (a : seq) := ∀ ε > 0, ∃ N, ∀ (m ≥ N) (n ≥ N), abs (a n - a m) < ε

end sec_3_2

-- Section 3.3 : Subsequences
section sec_3_3

-- Subsequence
def is_subseq_of (a : seq) (b : seq) := ∃ (p : ℕ → ℕ) (hp : monotone p), b = a ∘ p

end sec_3_3

end real_seq