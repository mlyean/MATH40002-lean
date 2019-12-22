import data.real.basic

namespace MATH40002

def seq : Type := ℕ → ℝ

-- Boundedness
def seq_bdd_above (a : seq) := bdd_above (set.range a)
def seq_bdd_below (a : seq) := bdd_below (set.range a)
def seq_bdd (a : seq) := ∃ M > 0, ∀ n, abs (a n) ≤ M

-- Limits
def is_limit (a : seq) (l : ℝ) := ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, abs ((a n) - l) < ε

-- Convergence
def seq_converges (a : seq) := ∃ (l : ℝ), is_limit a l

lemma seq_converges_of_has_limit {a : seq} {l : ℝ} : is_limit a l → seq_converges a := begin
  intro H,
  existsi l,
  exact H,
end

-- Divergence
def seq_diverges (a : seq) := ¬ seq_converges a
def seq_diverges_to_pos_inf (a : seq) := ∀ (M : ℕ), ∃ N, ∀ n ≥ N, a n > M
def seq_diverges_to_neg_inf (a : seq) := seq_diverges_to_pos_inf (λ n, -a n)

lemma seq_diverges_iff {a : seq} : seq_diverges a ↔ ∀ (l : ℝ), ∃ ε > 0, ∀ N, ∃ n ≥ N, abs ((a n) - l) ≥ ε := begin
  unfold seq_diverges seq_converges is_limit,
  push_neg,
  simp,
end

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

instance : has_zero seq := ⟨zero_seq⟩
instance : has_one seq := ⟨one_seq⟩
instance : has_add seq := ⟨add_seq⟩
instance : has_mul seq := ⟨mul_seq⟩
noncomputable instance : has_inv seq := ⟨inv_seq⟩
instance : has_neg seq := ⟨neg_seq⟩
instance : has_sub seq := ⟨sub_seq⟩
noncomputable instance : has_div seq := ⟨div_seq⟩

-- Monotonicity
def seq_increasing (a : seq) := monotone a
def seq_decreasing (a : seq) := monotone (λ n, -a n)

end MATH40002