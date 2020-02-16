import data.real.basic
import data.complex.basic
import data.set.basic
import algebra.pi_instances

namespace real_seq

def cseq_on (s : set ℂ) : Type := ℕ → psigma s
def cseq : Type := ℕ → ℂ
def seq_on (s : set ℝ) : Type := ℕ → psigma s
def seq : Type := ℕ → ℝ

instance coe_cseq_on {s₁ s₂ : set ℂ} (h : s₁ ⊆ s₂) : has_coe (cseq_on s₁) (cseq_on s₂) := ⟨λ a n, ⟨(a n).fst, h (a n).snd⟩⟩
instance coe_cseq_on₂ {s : set ℂ} : has_coe (cseq_on s) cseq := ⟨λ a n, (a n).fst⟩
instance coe_cseq : has_coe cseq (set ℂ) := ⟨set.range⟩
instance coe_seq_on {s₁ s₂ : set ℝ} (h : s₁ ⊆ s₂) : has_coe (seq_on s₁) (seq_on s₂) := ⟨λ a n, ⟨(a n).fst, h (a n).snd⟩⟩
instance coe_seq_on₂ {s : set ℝ} : has_coe (seq_on s) seq := ⟨λ a n, (a n).fst⟩
instance coe_seq_ℂ : has_coe seq cseq := ⟨λ a n, coe (a n)⟩
instance coe_seq : has_coe seq (set ℝ) := ⟨set.range⟩

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
instance : has_le seq := ⟨λ a b, ∀ n, a n ≤ b n⟩
instance : has_lt seq := ⟨λ a b, ∀ n, a n < b n⟩
noncomputable instance : has_div seq := ⟨λ a b n, a n / b n⟩
instance : has_scalar ℝ seq := ⟨λ c a n, c * a n⟩ 

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
protected lemma mul_comm : a * b = b * a := funext (λ n, mul_comm _ _)
protected lemma le_refl : a ≤ a := λ n, le_refl (a n)
protected lemma le_trans : a ≤ b → b ≤ c → a ≤ c := λ h₁ h₂ n, le_trans (h₁ n) (h₂ n)
protected lemma le_antisymm : a ≤ b → b ≤ a → a = b := λ h₁ h₂, funext (λ n, le_antisymm (h₁ n) (h₂ n))

end props

instance : comm_ring seq := {
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
  mul_comm := real_seq.mul_comm,
}

instance : partial_order seq := {
  le := real_seq.has_le.le,
  le_refl := real_seq.le_refl,
  le_trans := real_seq.le_trans,
  le_antisymm := real_seq.le_antisymm,
}

-- Section 3.1 : Convergence of Sequences
section sec_3_1

-- Boundedness
def seq_bdd_above (a : seq) := bdd_above (set.range a)
def seq_bdd_below (a : seq) := bdd_below (set.range a)
def seq_bdd (a : seq) := ∃ M > 0, ∀ n, abs (a n) ≤ M

lemma seq_bdd_above_iff {a : seq} : seq_bdd_above a ↔ ∃ A > 0, ∀ n, a n ≤ A := begin
  split,
  { rintro ⟨A, hA⟩,
    let A' := max A 1,
    have hA' : A' > 0 := lt_of_lt_of_le zero_lt_one (le_max_right A 1),
    existsi [A', hA'],
    intro n,
    exact le_trans (hA (set.mem_range_self n)) (le_max_left A 1),
  },
  { rintro ⟨A, ⟨hA₁, hA₂⟩⟩,
    existsi A,
    intros x hx,
    rw set.mem_range at hx,
    cases hx with y hy,
    subst hy,
    exact hA₂ y,
  }
end

lemma seq_bdd_below_iff {a : seq} : seq_bdd_below a ↔ ∃ A > 0, ∀ n, a n ≥ -A := begin
  split,
  { rintro ⟨A, hA⟩,
    let A' := max (-A) 1,
    have hA' : A' > 0 := lt_of_lt_of_le zero_lt_one (le_max_right (-A) 1),
    existsi [A', hA'],
    intro n,
    refine le_trans _ (hA (set.mem_range_self n)),
    rw neg_le,
    exact le_max_left (-A) 1,
  },
  { rintro ⟨A, ⟨hA₁, hA₂⟩⟩,
    existsi (-A),
    intros x hx,
    rw set.mem_range at hx,
    cases hx with y hy,
    subst hy,
    exact hA₂ y,
  }
end

lemma seq_bdd_above_of_bdd {a : seq} (h : seq_bdd a) : seq_bdd_above a := begin
  rcases h with ⟨A, ⟨hA, hA'⟩⟩,
  existsi A,
  rintros x ⟨n, hn⟩,
  subst hn,
  exact (abs_le.mp (hA' n)).right,
end

lemma seq_bdd_below_of_bdd {a : seq} (h : seq_bdd a) : seq_bdd_below a := begin
  rcases h with ⟨A, ⟨hA, hA'⟩⟩,
  existsi -A,
  rintros x ⟨n, hn⟩,
  subst hn,
  exact (abs_le.mp (hA' n)).left,
end

lemma seq_bdd_iff {a : seq} : seq_bdd a ↔ seq_bdd_above a ∧ seq_bdd_below a := begin
  split,
  { intro ha,
    exact ⟨seq_bdd_above_of_bdd ha, seq_bdd_below_of_bdd ha⟩,
  },
  { rw [seq_bdd_above_iff, seq_bdd_below_iff],
    rintro ⟨⟨A₁, hA₁, hA₁'⟩, ⟨A₂, hA₂, hA₂'⟩⟩,
    let A := max A₁ A₂,
    existsi [A, lt_of_lt_of_le hA₁ (le_max_left _ _)],
    intro n,
    rw abs_le,
    split,
    { exact le_trans (neg_le_neg (le_max_right _ _)) (hA₂' n) },
    { exact le_trans (hA₁' n) (le_max_left _ _) }
  }
end

-- Limits
def is_limit (a : seq) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, abs ((a n) - l) < ε
notation a ` ⟶ ` l := is_limit a l

-- Convergence
def seq_converges (a : seq) := ∃ (l : ℝ), is_limit a l

lemma seq_converges_of_has_limit {a : seq} {l : ℝ} : is_limit a l → seq_converges a := Exists.intro l

-- Divergence
def seq_diverges (a : seq) := ¬ seq_converges a
def seq_diverges_to_pos_inf (a : seq) := ∀ M, ∃ N, ∀ n ≥ N, a n ≥ M
def seq_diverges_to_neg_inf (a : seq) := ∀ M, ∃ N, ∀ n ≥ N, a n ≤ M
notation a ` ⟶+∞ ` := seq_diverges_to_pos_inf a
notation a ` ⟶-∞ ` := seq_diverges_to_neg_inf a

lemma seq_diverges_iff {a : seq} : seq_diverges a ↔ ∀ (l : ℝ), ∃ ε > 0, ∀ N, ∃ n ≥ N, abs ((a n) - l) ≥ ε := begin
  unfold seq_diverges seq_converges is_limit,
  push_neg,
  simp only [exists_prop, gt_iff_lt, iff_self, ge_iff_le, sub_eq_add_neg],
end

lemma seq_diverges_to_neg_inf_iff (a : seq) : (a ⟶-∞) ↔ ((-a) ⟶+∞) := begin
  split,
  { intros ha M,
    cases ha (-M) with N hN,
    existsi N,
    intros n hn,
    exact le_neg_of_le_neg (hN n hn),
  },
  { intros ha M,
    cases ha (-M) with N hN,
    existsi N,
    intros n hn,
    exact le_of_neg_le_neg (hN n hn),
  }
end

lemma seq_diverges_of_diverges_to_pos_inf {a : seq} (ha : a ⟶+∞) : seq_diverges a := begin
  rintro ⟨l, hl⟩,
  cases hl 1 zero_lt_one with N₁ hN₁,
  cases ha (l + 1) with N₂ hN₂,
  let N := max N₁ N₂,
  refine not_lt_of_ge (hN₂ N (le_max_right _ _)) _,
  rw ←sub_lt_iff_lt_add',
  exact (abs_lt.mp (hN₁ N (le_max_left _ _))).right,
end

lemma seq_diverges_of_diverges_to_neg_inf {a : seq} (ha : a ⟶-∞) : seq_diverges a := begin
  rintro ⟨l, hl⟩,
  cases hl 1 zero_lt_one with N₁ hN₁,
  cases ha (l - 1) with N₂ hN₂,
  let N := max N₁ N₂,
  refine not_lt_of_le (hN₂ N (le_max_right _ _)) _,
  rw [sub_lt_iff_lt_add, ←neg_lt_sub_iff_lt_add],
  exact (abs_lt.mp (hN₁ N (le_max_left _ _))).left,
end

lemma seq_not_bdd_above_of_diverges_to_pos_inf {a : seq} (ha : a ⟶+∞) : ¬ seq_bdd_above a := begin
  rintro ⟨M, hM⟩,
  cases ha (M + 1) with N hN,
  have h₁ : a N ≤ M := hM (set.mem_range_self N),
  have h₂ : a N > M := calc
    a N ≥ M + 1 : hN N (le_refl N)
      ... > M : lt_add_one M,
  exact not_lt_of_le h₁ h₂,
end

lemma seq_not_bdd_below_of_diverges_to_neg_inf {a : seq} (ha : a ⟶-∞) : ¬ seq_bdd_below a := begin
  rintro ⟨M, hM⟩,
  cases ha (M - 1) with N hN,
  have h₁ : a N ≥ M := hM (set.mem_range_self N),
  have h₂ : a N < M := calc
    a N ≤ M - 1 : hN N (le_refl N)
      ... < M : sub_one_lt M,
  exact not_lt_of_le h₁ h₂,
end

-- Monotonicity
def seq_increasing (a : seq) := monotone a
def seq_decreasing (a : seq) := monotone (-a)

end sec_3_1

-- Section 3.2 : Cauchy Sequences
section sec_3_2

-- Cauchy
def seq_cauchy (a : seq) := ∀ ε > 0, ∃ N, ∀ (m ≥ N) (n ≥ N), abs (a n - a m) < ε

end sec_3_2

-- Section 3.3 : Subsequences
section sec_3_3

-- Subsequence
def is_subseq_of (a : seq) (b : seq) := ∃ (n : psigma strict_mono), b = a ∘ n.fst

end sec_3_3

end real_seq