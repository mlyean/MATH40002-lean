import data.real.basic
import algebra.commute

namespace MATH40002

open classical

local attribute [instance] classical.prop_decidable

-- Some useful lemmas
lemma div_lt_iff'' {a b c : ℝ} (hb : b > 0) (hc : c > 0) : a / b < c ↔ a / c < b := by rw [div_lt_iff hb, div_lt_iff' hc]

-- Chapter 3 : Sequences

-- Definition of bounded for sequences
def seq_bdd_above (a : ℕ → ℝ) := ∃ (M : ℝ), ∀ n, a n ≤ M
def seq_bdd_below (a : ℕ → ℝ) := ∃ (M : ℝ), ∀ n, M ≤ a n
def seq_bdd (a : ℕ → ℝ) := ∃ M > 0, ∀ n, abs (a n) ≤ M

-- Definition of limit
def is_limit (a : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, abs ((a n) - l) < ε

-- Definitions of convergence and divergence
def seq_converges (a : ℕ → ℝ) := ∃ (l : ℝ), is_limit a l
def seq_diverges (a : ℕ → ℝ) := ¬ seq_converges a
def seq_diverges_to_pos_inf (a : ℕ → ℝ) := ∀ (M : ℕ), ∃ N, ∀ n ≥ N, a n > M
def seq_diverges_to_neg_inf (a : ℕ → ℝ) := seq_diverges_to_pos_inf (λ n, -a n)

def seq_diverges_iff (a : ℕ → ℝ) : seq_diverges a ↔ ∀ (l : ℝ), ∃ ε > 0, ∀ N, ∃ n ≥ N, abs ((a n) - l) ≥ ε := begin
  unfold seq_diverges,
  unfold seq_converges,
  unfold is_limit,
  push_neg,
  simp,
end

-- Example 3.4
example : is_limit (λ n, 1 / (n + 1)) 0 := begin
  intros ε hε,
  cases exists_nat_one_div_lt hε with N hN,
  existsi N,
  intros n hn,
  simp,
  rw abs_of_pos,
  { simp at hN,
    have hn' : 0 < 1 + (n : ℝ) := by { norm_cast, exact nat.zero_lt_one_add n },
    have hN' : 0 < 1 + (N : ℝ) := by { norm_cast, exact nat.zero_lt_one_add N },
    calc
      (1 + ↑n)⁻¹ ≤ (1 + ↑N)⁻¹ : by { rw inv_le_inv hn' hN', simp, exact hn }
        ... < ε : hN
  },
  { rw gt_iff_lt,
    apply inv_pos,
    norm_cast,
    exact nat.zero_lt_one_add n
  }
end

-- Example 3.5
example : is_limit (λ n, (n + 5) / (n + 1)) 1 := begin
  intros ε hε,
  have hε' : 0 < 4 / ε := begin
    refine div_pos _ hε,
    norm_num,
  end,
  cases exists_nat_gt (4 / ε) with N hN,
  existsi N + 1,
  intros n hn,
  simp,
  have hN' : 0 < 1 + (↑N : ℝ) := by { norm_cast, norm_num },
  have hn' : 0 < 1 + (↑n : ℝ) := by { norm_cast, norm_num },
  rw abs_of_pos,
  { have hn'' : 1 + (↑n : ℝ) ≠ 0 := ne_of_gt hn',
    calc
      -(1 : ℝ) + (5 + ↑n) / (1 + ↑n) = 4 / (1 + ↑n) : by { symmetry, rw [div_eq_iff hn'', add_mul, div_mul_cancel _ hn''], ring }
        ... < 4 / (1 + ↑N) : by {rw div_lt_div_left _ hn' hN', norm_cast, exact add_lt_add_left hn 1, norm_cast, exact nat.succ_pos' }
        ... < ε : by {rw div_lt_iff'' hN' hε, exact lt_trans hN (lt_one_add ↑N) }
  },
  { simp,
    refine one_lt_div_of_lt (5 + ↑n) hn' _,
    norm_num,
  }
end

-- Example 3.6
example : is_limit (λ n, (n + 2) / (n - 2)) 1 := begin
  intros ε hε,
  cases exists_nat_gt (max 4 (8 / ε)) with N hN,
  existsi N,
  intros n hn,
  have hn_gt_4 : (n : ℝ) > 4 :=
    calc
      (n : ℝ) ≥ N : by { norm_cast, exact hn }
        ... > max 4 (8 / ε) : hN
        ... ≥ 4 : le_max_left 4 (8 / ε),
  have hn_gt_2 : (n : ℝ) > 2 :=
    calc
      (n : ℝ) > 4 : hn_gt_4
        ... > 2 : by norm_num,
  have hn_pos : (n : ℝ) > 0 :=
    calc
      (n : ℝ) > 2 : hn_gt_2
        ... > 0 : by norm_num,
  have hsimp : (↑n + 2) / (↑n - 2) - (1 : ℝ) = 4 / (↑n - 2) := begin 
    have hn' : ((n : ℝ) - 2) ≠ 0 := begin
      change ¬ ((n : ℝ) - 2 = 0),
      rw sub_eq_zero,
      exact ne_of_gt hn_gt_2,
    end,
    conv_lhs { congr, skip, rw ←div_self hn' },
    field_simp [hn],
    ring,
  end,
  change abs ((↑n + 2) / (↑n - 2) - 1) < ε,
  calc
    abs (((n : ℝ) + 2) / (n - 2) - 1) = abs (4 / ((n : ℝ) - 2)) : by rw hsimp
      ... = 4 / ((n : ℝ) - 2) : by { rw abs_of_pos, refine div_pos _ _, norm_num, rw sub_pos, exact hn_gt_2 }
      ... < 4 / ((n : ℝ) / 2) : by {
        rw div_lt_div_left,
        { linarith only [hn_gt_4] },
        { norm_num },
        { rw sub_pos, exact hn_gt_2 },
        { refine div_pos hn_pos _, norm_num }
      }
      ... = 8 / (n : ℝ) : by { rw div_div_eq_mul_div, ring, }
      ... < ε : by {
        rw div_lt_iff'' _ hε,
        { calc
            8 / ε ≤ max 4 (8 / ε) : le_max_right 4 (8 / ε)
              ... < N : hN
              ... ≤ n : by { norm_cast, exact hn },
        },
        { exact hn_pos }},
end

-- Example 3.8
example (δ : ℝ) (h₁ : δ > 0) : seq_diverges (λ n, (-1) ^ n * δ) := begin
  by_contradiction h₂,
  unfold seq_diverges at h₂,
  rw not_not at h₂,
  cases h₂ with l hl,
  cases hl δ h₁ with N hN,
  have h₂ : N ≤ 2 * N := by { rw two_mul, exact nat.le_add_right N N },
  have h₃ : N ≤ 2 * N + 1 := nat.le_succ_of_le h₂,
  have h₄ : abs (δ - l) < δ := begin
    have H := hN (2 * N) h₂,
    change abs ((-1) ^ (2 * N) * δ - l) < δ at H,
    rwa [neg_one_pow_eq_pow_mod_two, nat.mul_mod_right, pow_zero, one_mul] at H,
  end,
  have h₅ : abs (δ + l) < δ := begin
    have H := hN (2 * N + 1) h₃,
    change abs ((-1) ^ (2 * N + 1) * δ - l) < δ at H,
    rw [neg_one_pow_eq_pow_mod_two, add_comm, nat.add_mul_mod_self_left] at H,
    change 1 % 2 with 1 at H,
    rw [pow_one, neg_one_mul, ←abs_neg] at H,
    simp at H,
    exact H,
  end,
  refine lt_irrefl (2 * δ) _,
  calc
    2 * δ = abs (2 * δ) : by rw abs_of_pos (mul_pos' zero_lt_two h₁)
      ... = abs ((δ - l) + (δ + l)) : by simp [two_mul]
      ... ≤ abs (δ - l) + abs (δ + l) : abs_add (δ - l) (δ + l)
      ... < δ + δ : add_lt_add h₄ h₅
      ... = 2 * δ : (two_mul δ).symm
end

lemma close_implies_eq (a b : ℝ) : (∀ ε > 0, abs (a - b) < ε) → a = b := begin
  intro h,
  rw ←sub_eq_zero,
  by_contradiction h',
  exact lt_irrefl (abs (a - b)) (h (abs (a - b)) (abs_pos_of_ne_zero h')),
end

-- Theorem 3.9 (Uniqueness of limits)
theorem limit_unique {a : ℕ → ℝ} {l₁ l₂ : ℝ} (h₁ : is_limit a l₁) (h₂ : is_limit a l₂) : l₁ = l₂ := begin
  apply close_implies_eq l₁ l₂,
  intros ε hε,
  cases h₁ (ε / 2) (half_pos hε) with N₁ hN₁,
  cases h₂ (ε / 2) (half_pos hε) with N₂ hN₂,
  let N := max N₁ N₂,
  replace hN₁ := hN₁ N (le_max_left N₁ N₂),
  replace hN₂ := hN₂ N (le_max_right N₁ N₂),
  calc
    abs (l₁ - l₂) ≤ abs (l₁ - a N) + abs (a N - l₂) : abs_sub_le l₁ (a N) l₂
      ... = abs (a N - l₁) + abs (a N - l₂) : by rw abs_sub
      ... < ε / 2 + ε / 2 : add_lt_add hN₁ hN₂
      ... = ε : add_halves ε,
end

-- Proposition 3.10
lemma bdd_of_converges (a : ℕ → ℝ) : seq_converges a → seq_bdd a := begin
  intro ha,
  cases ha with l hl,
  cases hl 1 zero_lt_one with N hN,
  let head : finset ℝ := (finset.range (N + 1)).image (λ n, abs (a n)),
  have head_has_mem : abs (a 0) ∈ head := begin
    rw finset.mem_image,
    existsi 0,
    simp,
  end,
  cases finset.max_of_mem head_has_mem with B hB,
  let M := max B (abs l + 1),
  have hM : M > 0 :=
    calc
      M = max B (abs l + 1) : rfl
        ... ≥ abs l + 1 : le_max_right B (abs l + 1)
        ... ≥ 0 + 1 : by {refine add_le_add_right (abs_nonneg l) 1 }
        ... = 1 : zero_add 1
        ... > 0 : zero_lt_one,
  existsi M,
  existsi hM,
  intro n,
  cases le_or_gt n N with h h,
  { have an_mem_head : abs (a n) ∈ head := begin
      rw finset.mem_image,
      existsi n,
      simp,
      exact nat.lt_succ_of_le h,
    end,
    calc
      abs (a n) ≤ B : finset.le_max_of_mem an_mem_head hB
        ... ≤ M : le_max_left B (abs l + 1),
  },
  { have h' : abs (a n) - abs l < 1 :=
    calc
      abs (a n) - abs l ≤ abs (a n - l) : abs_sub_abs_le_abs_sub (a n) l
        ... < 1 : hN n (le_of_lt h),
    rw sub_lt_iff_lt_add' at h',
    apply le_of_lt,
    calc
      abs (a n) < abs l + 1 : h'
        ... ≤ M : le_max_right B (abs l + 1),
  }
end

-- Some operations on sequences
def seq_add (a b : ℕ → ℝ) : ℕ → ℝ := λ n, a n + b n
def seq_mul (a b : ℕ → ℝ) : ℕ → ℝ := λ n, a n * b n
noncomputable def seq_div (a : ℕ → ℝ) (b : ℕ → ℝ) : ℕ → ℝ := λ n, a n / b n

-- Theorem 3.11 (Algebra of limits)
theorem limit_seq_add {a b : ℕ → ℝ} {la lb : ℝ} (hla : is_limit a la) (hlb : is_limit b lb) : is_limit (seq_add a b) (la + lb) := begin
  intros ε hε,
  cases hla (ε / 2) (half_pos hε) with Na hNa,
  cases hlb (ε / 2) (half_pos hε) with Nb hNb,
  let N := max Na Nb,
  existsi N,
  intros n Hn,
  replace hNa := hNa n (le_trans (le_max_left Na Nb) Hn),
  replace hNb := hNb n (le_trans (le_max_right Na Nb) Hn),
  unfold seq_add,
  have hsimp : a n + b n - (la + lb) = (a n - la) + (b n - lb) := by ring,
  calc
    abs (a n + b n - (la + lb)) = abs ((a n - la) + (b n - lb)) : by rw hsimp
      ... ≤ abs (a n - la) + abs (b n - lb) : abs_add (a n - la) (b n - lb)
      ... < ε / 2 + ε / 2 : add_lt_add hNa hNb
      ... = ε : add_halves ε,
end

theorem limit_seq_mul {a b : ℕ → ℝ} {la lb : ℝ} (hla : is_limit a la) (hlb : is_limit b lb) : is_limit (seq_mul a b) (la * lb) := begin
  intros ε hε,
  sorry
end

theorem limit_seq_div {a b : ℕ → ℝ} {la lb : ℝ} (hla : is_limit a la) (hlb : is_limit b lb) (hlb' : lb ≠ 0) : is_limit (seq_div a b) (la / lb) := begin
  intros ε hε,
  sorry
end

end MATH40002