import data.real.basic
import algebra.pi_instances

namespace real_seq

def seq : Type := ℕ → ℝ
def const_seq (x : ℝ) : seq := λ _, x

-- Properties of sequences
section props

instance : has_zero seq := pi.has_zero
instance : has_one seq := pi.has_one
instance : has_add seq := pi.has_add
instance : has_mul seq := pi.has_mul
noncomputable instance : has_inv seq := pi.has_inv
instance : has_neg seq := pi.has_neg
instance : has_sub seq := ⟨λ a b n, a n - b n⟩
noncomputable instance : has_div seq := ⟨λ a b n, a n / b n⟩

variables (a b c : seq)

protected lemma add_assoc : a + b + c = a + (b + c) := funext (λ n, add_assoc _ _ _)
protected lemma zero_add : 0 + a = a := funext (λ n, zero_add _)
protected lemma add_zero : a + 0 = a := funext (λ n, add_zero _)
protected lemma add_left_neg : -a + a = 0 := funext (λ n, add_left_neg _)
protected lemma add_comm : a + b = b + a := funext (λ n, add_comm _ _)
protected lemma mul_assoc : a * b * c = a * (b * c) := funext (λ n, mul_assoc _ _ _)
protected lemma one_mul : 1 * a = a := funext (λ n, one_mul (a n))
protected lemma mul_one : a * 1 = a := funext (λ n, mul_one (a n))
protected lemma left_distrib : a * (b + c) = a * b + a * c := funext (λ n, left_distrib _ _ _)
protected lemma right_distrib : (a + b) * c = a * c + b * c := funext (λ n, right_distrib _ _ _)

end props

instance : ring seq := {
  add := real_seq.has_add.add,
  add_assoc := real_seq.add_assoc,
  zero := real_seq.has_zero.zero,
  zero_add := real_seq.zero_add,
  add_zero := real_seq.add_zero,
  neg := real_seq.has_neg.neg,
  add_left_neg := real_seq.add_left_neg,
  add_comm := real_seq.add_comm,
  mul := real_seq.has_mul.mul,
  mul_assoc := real_seq.mul_assoc,
  one := real_seq.has_one.one,
  one_mul := real_seq.one_mul,
  mul_one := real_seq.mul_one,
  left_distrib := real_seq.left_distrib,
  right_distrib := real_seq.right_distrib,
}

-- Section 3.1 : Convergence of Sequences
section sec_3_1

-- Boundedness
def seq_bdd_above (a : seq) := bdd_above (set.range a)
def seq_bdd_below (a : seq) := bdd_below (set.range a)
def seq_bdd (a : seq) := ∃ M > 0, ∀ n, abs (a n) ≤ M

lemma seq_bdd_above_of_bdd {a : seq} (h : seq_bdd a) : seq_bdd_above a := begin
  rcases h with ⟨A, ⟨hA, hA'⟩⟩,
  existsi A,
  rintros x ⟨n, hn⟩,
  rw ←hn,
  exact (abs_le.1 (hA' n)).2,
end

lemma seq_bdd_below_of_bdd {a : seq} (h : seq_bdd a) : seq_bdd_below a := begin
  rcases h with ⟨A, ⟨hA, hA'⟩⟩,
  existsi -A,
  rintros x ⟨n, hn⟩,
  rw ←hn,
  exact (abs_le.1 (hA' n)).1,
end

-- Limits
def is_limit (a : seq) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, abs ((a n) - l) < ε

-- Convergence
def seq_converges (a : seq) := ∃ (l : ℝ), is_limit a l

lemma seq_converges_of_has_limit {a : seq} {l : ℝ} : is_limit a l → seq_converges a := Exists.intro l

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
def is_subseq_of (a : seq) (b : seq) := ∃ (p : ℕ → ℕ) (hp : strict_mono p), b = a ∘ p

end sec_3_3

end real_seq