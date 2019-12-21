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

lemma seq_converges_of_has_limit {a : ℕ → ℝ} {l : ℝ} : is_limit a l → seq_converges a := begin
  intro H,
  existsi l,
  exact H,
end

lemma seq_diverges_iff {a : ℕ → ℝ} : seq_diverges a ↔ ∀ (l : ℝ), ∃ ε > 0, ∀ N, ∃ n ≥ N, abs ((a n) - l) ≥ ε := begin
  unfold seq_diverges,
  unfold seq_converges,
  unfold is_limit,
  push_neg,
  simp,
end

-- Example 3.4
lemma limit_of_reciprocal : is_limit (λ n, 1 / (n + 1)) 0 := begin
  intros ε hε,
  cases exists_nat_one_div_lt hε with N hN,
  existsi N,
  intros n hn,
  rw sub_zero,
  dsimp,
  rw abs_of_pos,
  { refine lt_of_le_of_lt _ hN,
    rw one_div_le_one_div _ _,
    { norm_cast,
      simp,
      exact hn,
    },
    exact nat.cast_add_one_pos n,
    exact nat.cast_add_one_pos N,
  },
  { exact nat.one_div_pos_of_nat }
end

-- Example 3.5
example : is_limit (λ n, (n + 5) / (n + 1)) 1 := begin
  intros ε hε,
  have hε' : 0 < 4 / ε := div_pos (by norm_num) hε,
  cases exists_nat_gt (4 / ε) with N hN,
  existsi N + 1,
  intros n hn,
  change abs ((↑n + 5) / (↑n + 1) - 1) < ε,
  have hN' : 0 < (↑N : ℝ) + 1 := nat.cast_add_one_pos N,
  have hn' : 0 < (↑n : ℝ) + 1 := nat.cast_add_one_pos n,
  rw abs_of_pos,
  { calc
      (↑n + 5) / (↑n + 1) - 1 = (↑n + 5) / (↑n + 1) - (↑n + 1) / (↑n + 1) : by {
          simp,
          refine (div_self _).symm,
          rw add_comm,
          exact ne_of_gt hn'
        }
        ... = 4 / ((↑n : ℝ) + 1) : by ring
        ... < 4 / ((↑N : ℝ) + 1) : by {
          rw div_lt_div_left (by norm_num : (0 < (4 : ℝ))) hn' hN',
          norm_cast,
          exact add_lt_add_right hn 1
        }
        ... < ε : by {
          rw div_lt_iff'' hN' hε,
          exact lt_trans hN (lt_add_one ↑N)
        },
  },
  { rw [gt_iff_lt, sub_pos],
    refine one_lt_div_of_lt (↑n + 5) hn' _,
    norm_num,
  }
end

-- Example 3.6
example : is_limit (λ n, (n + 2) / (n - 2)) 1 := begin
  intros ε hε,
  cases exists_nat_gt (max 4 (8 / ε)) with N hN,
  existsi N,
  intros n hn,
  have hn_gt_4 : (n : ℝ) > 4 := calc
    (n : ℝ) ≥ N : by { norm_cast, exact hn }
      ... > max 4 (8 / ε) : hN
      ... ≥ 4 : le_max_left 4 (8 / ε),
  have hn_gt_2 : (n : ℝ) > 2 := lt_trans (by norm_num) hn_gt_4,
  have hn_pos : (n : ℝ) > 0 := lt_trans (by norm_num) hn_gt_4,
  change abs ((↑n + 2) / (↑n - 2) - 1) < ε,
  calc
    abs (((n : ℝ) + 2) / (n - 2) - 1) = abs (4 / ((n : ℝ) - 2)) : by {
        have hn' : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hn_gt_2),
        apply congr_arg,
        conv_lhs { congr, skip, rw ←div_self hn' },
        field_simp [hn],
        norm_num,
      }
      ... = 4 / ((n : ℝ) - 2) : by {
        refine abs_of_pos (div_pos (by norm_num) _),
        rw sub_pos,
        exact hn_gt_2
      }
      ... < 4 / ((n : ℝ) / 2) : by {
        rw div_lt_div_left,
        all_goals { linarith [hn_gt_4] }
      }
      ... = 8 / (n : ℝ) : by { rw div_div_eq_mul_div, ring }
      ... < ε : by {
        rw div_lt_iff'' hn_pos hε,
        calc
          8 / ε ≤ max 4 (8 / ε) : le_max_right 4 (8 / ε)
            ... < N : hN
            ... ≤ n : nat.cast_le.mpr hn,
      },
end

-- Example 3.8
example (δ : ℝ) (h₁ : δ > 0) : seq_diverges (λ n, (-1) ^ n * δ) := begin
  unfold seq_diverges,
  by_contradiction h₂,
  cases h₂ with l hl,
  cases hl δ h₁ with N hN,
  have h₂ : N ≤ 2 * N := by { rw two_mul, exact nat.le_add_right N N },
  have h₃ : N ≤ 2 * N + 1 := nat.le_succ_of_le h₂,
  have h₄ : abs (δ - l) < δ := begin
    have H : abs ((-1) ^ (2 * N) * δ - l) < δ := hN (2 * N) h₂,
    rwa [neg_one_pow_eq_pow_mod_two, nat.mul_mod_right, pow_zero, one_mul] at H,
  end,
  have h₅ : abs (δ + l) < δ := begin
    have H : abs ((-1) ^ (2 * N + 1) * δ - l) < δ := hN (2 * N + 1) h₃,
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
lemma bdd_of_converges {a : ℕ → ℝ} : seq_converges a → seq_bdd a := begin
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
        ... ≥ 0 + 1 : add_le_add_right (abs_nonneg l) 1
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
def const_seq (x : ℝ) : ℕ → ℝ := λ _, x
def add_seq (a b : ℕ → ℝ) : ℕ → ℝ := λ n, a n + b n
def mul_seq (a b : ℕ → ℝ) : ℕ → ℝ := λ n, a n * b n
noncomputable def div_seq (a b : ℕ → ℝ) : ℕ → ℝ := λ n, a n / b n

-- Theorem 3.11 (Algebra of limits)
theorem lim_add_eq_add_lim {a b : ℕ → ℝ} {la lb : ℝ} (hla : is_limit a la) (hlb : is_limit b lb) : is_limit (add_seq a b) (la + lb) := begin
  intros ε hε,
  cases hla (ε / 2) (half_pos hε) with Na hNa,
  cases hlb (ε / 2) (half_pos hε) with Nb hNb,
  let N := max Na Nb,
  existsi N,
  intros n Hn,
  replace hNa := hNa n (le_trans (le_max_left Na Nb) Hn),
  replace hNb := hNb n (le_trans (le_max_right Na Nb) Hn),
  unfold add_seq,
  calc
    abs (a n + b n - (la + lb)) = abs ((a n - la) + (b n - lb)) : congr_arg abs (by ring)
      ... ≤ abs (a n - la) + abs (b n - lb) : abs_add (a n - la) (b n - lb)
      ... < ε / 2 + ε / 2 : add_lt_add hNa hNb
      ... = ε : add_halves ε,
end

theorem lim_mul_eq_mul_lim {a b : ℕ → ℝ} {la lb : ℝ} (hla : is_limit a la) (hlb : is_limit b lb) : is_limit (mul_seq a b) (la * lb) := begin
  intros ε hε,
  rcases bdd_of_converges (seq_converges_of_has_limit hla) with ⟨A, ⟨hA₁, hA₂⟩⟩,
  have H : 2 * (abs lb + 1) > 0 := mul_pos' zero_lt_two (lt_of_le_of_lt (abs_nonneg lb) (lt_add_one (abs lb))),
  cases hla (ε / (2 * (abs lb + 1))) _ with Na hNa,
  cases hlb (ε / (2 * A)) _ with Nb hNb,
  show ε / (2 * (abs lb + 1)) > 0, from div_pos hε H,
  show ε / (2 * A) > 0, from div_pos hε (mul_pos' zero_lt_two hA₁),
  let N := max Na Nb,
  existsi N,
  intros n Hn,
  replace hNa := hNa n (le_trans (le_max_left Na Nb) Hn),
  replace hNb := hNb n (le_trans (le_max_right Na Nb) Hn),
  replace hA₂ := hA₂ n,
  unfold mul_seq,
  have h₁ : abs (a n - la) * abs lb < ε / 2 := calc
      abs (a n - la) * abs lb ≤ (ε / (2 * (abs lb + 1))) * abs lb : mul_le_mul_of_nonneg_right (le_of_lt hNa) (abs_nonneg lb)
        ... = ε * abs lb / (2 * (abs lb + 1)) : by field_simp
        ... < ε / 2 : by {
          rw [div_lt_iff' H, ←mul_lt_mul_right zero_lt_two, ←sub_pos],
          field_simp,
          ring,
          exact mul_pos' zero_lt_two hε,
        },
  have h₂ : abs (a n) * abs (b n - lb) ≤  ε / 2 := calc
      abs (a n) * abs (b n - lb) ≤ A * (ε / (2 * A)) : mul_le_mul hA₂ (le_of_lt hNb) (abs_nonneg (b n - lb)) (le_of_lt hA₁)
        ... = ε / 2 : by { field_simp [ne_of_gt hA₁], ring, },
  calc
    abs (a n * b n - la * lb) = abs ((a n - la) * lb + a n * (b n - lb)) : by ring
      ... ≤ abs ((a n - la) * lb) + abs(a n * (b n - lb)) : abs_add ((a n - la) * lb) (a n * (b n - lb))
      ... = abs (a n - la) * abs lb + abs (a n) * abs (b n - lb) : by rw [abs_mul, abs_mul]
      ... < ε / 2 + ε / 2 : add_lt_add_of_lt_of_le h₁ h₂
      ... = ε : add_halves ε,
end

theorem lim_div_eq_div_lim {a b : ℕ → ℝ} {la lb : ℝ} (hlb_ne_zero : lb ≠ 0) (hla : is_limit a la) (hlb : is_limit b lb) : is_limit (div_seq a b) (la / lb) := begin
  have hla' : 4 * abs la + 1 > 0 := by linarith only [abs_nonneg la],
  have hlb' : abs lb > 0 := abs_pos_of_ne_zero hlb_ne_zero,
  intros ε hε,
  cases hlb (abs lb / 2) (div_pos hlb' zero_lt_two) with N₁ hN₁,
  cases hla (ε * abs lb / 4) _ with N₂ hN₂,
  cases hlb (ε * (abs lb) ^ 2 / (4 * abs la + 1)) _ with N₃ hN₃,
  show ε * abs lb / 4 > 0, from div_pos (mul_pos hε hlb') (by norm_num),
  show ε * abs lb ^ 2 / (4 * abs la + 1) > 0, from div_pos (mul_pos hε (pow_pos hlb' 2)) hla',
  let N := max N₁ (max N₂ N₃),
  existsi N,
  intros n Hn,
  replace hN₁ := hN₁ n (le_trans (le_max_left _ _) Hn),
  have hN₁' : abs (b n) > abs lb / 2 := begin
    have h : abs lb - abs (b n) < abs lb / 2 := calc
      abs lb - abs (b n) ≤ abs (lb - b n) : abs_sub_abs_le_abs_sub lb (b n)
        ... = abs (b n - lb) : by rw abs_sub
        ... < abs lb / 2 : hN₁,
    rw sub_lt_iff_lt_add at h,
    linarith only [h],
  end,
  clear hN₁,
  rename hN₁' hN₁,
  replace hN₂ := hN₂ n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) Hn),
  replace hN₃ := hN₃ n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) Hn),
  unfold div_seq,
  have hbn : b n ≠ 0 := abs_pos_iff.mp (lt_trans (half_pos hlb') hN₁),
  have h_main : abs ((a n - la) * lb + la * (lb - b n)) < ε * abs lb * abs lb / 2 := calc
    abs ((a n - la) * lb + la * (lb - b n)) ≤ abs ((a n - la) * lb) + abs (la * (lb - b n)) : abs_add _ _
      ... = abs (a n - la) * abs lb + abs la * abs (b n - lb) : by rw [abs_mul, abs_mul, abs_sub lb (b n)]
      ... < (ε * abs lb / 4) * abs lb + abs la * ε * abs lb ^ 2 / (4 * abs la + 1) : by {
        refine add_lt_add_of_lt_of_le _ _,
        { exact mul_lt_mul_of_pos_right hN₂ hlb' },
        { have hsimp : abs la * ε * abs lb ^ 2 / (4 * abs la + 1) = abs la * (ε * abs lb ^ 2 / (4 * abs la + 1)) := by ring,
          rw hsimp,
          exact mul_le_mul_of_nonneg_left (le_of_lt hN₃) (abs_nonneg la),
        }
      }
      ... = ε * abs lb * abs lb * (1 / 4 + abs la / (4 * abs la + 1)) : by { rw pow_two, ring }
      ... < (ε * abs lb * abs lb) * (1 / 2) : by {
        refine mul_lt_mul_of_pos_left _ (mul_pos (mul_pos hε hlb') hlb'),
        have hsimp : (1 / 2 : ℝ) = 1 / 4 + 1 / 4 := by norm_num,
        rw [hsimp, add_lt_add_iff_left, div_lt_iff hla'],
        linarith,
      }
      ... = ε * abs lb * abs lb / 2 : by ring,
  calc
    abs (a n / b n - la / lb) = abs ((a n * lb - b n * la) / (b n * lb)) : congr_arg abs (div_sub_div (a n) la hbn hlb_ne_zero)
      ... = abs (a n * lb - b n * la) / abs (b n * lb) : by rw abs_div
      ... = abs (a n * lb - b n * la) / (abs (b n) * abs lb) : by rw abs_mul
      ... = abs (a n * lb - b n * la) / (abs lb * abs (b n)) : by rw mul_comm (abs (b n)) (abs lb)
      ... = (abs (a n * lb - b n * la) / abs lb) * (1 / abs (b n)) : by rw div_mul_eq_div_mul_one_div 
      ... ≤ (abs (a n * lb - b n * la) / abs lb) * (2 / abs lb) : by {
        refine mul_le_mul_of_nonneg_left _ (div_nonneg (abs_nonneg _) hlb'),
        rw div_le_div_iff,
        { linarith only [hN₁] },
        { exact abs_pos_of_ne_zero hbn },
        { exact hlb' }
      }
      ... = abs (a n * lb - b n * la) * (2 / (abs lb * abs lb)) : by field_simp
      ... = abs ((a n - la) * lb + la * (lb - b n)) * (2 / (abs lb * abs lb)) : congr_arg (λ x, (abs x) * (2 / (abs lb * abs lb))) (by ring)
      ... < (ε * abs lb * abs lb / 2) * (2 / (abs lb * abs lb)) : mul_lt_mul_of_pos_right h_main (div_pos (by norm_num) (mul_pos hlb' hlb'))
      ... = ε : by { field_simp [ne_of_gt hlb'], ring },
end

-- Some useful limits (not in notes)
lemma lim_of_const_seq {a : ℝ} : is_limit (const_seq a) a := begin
  intros ε hε,
  existsi 0,
  intros n Hn,
  unfold const_seq,
  rw [sub_self, abs_zero],
  exact hε,
end

lemma lim_of_neg_pow {k : ℕ} : is_limit (λ n, (1 : ℝ) / ((n + 1) ^ (k + 1))) 0 := begin
  induction k with k hk,
  { conv { congr, funext, rw [zero_add, pow_one] },
    exact limit_of_reciprocal,
  },
  { conv {
      congr,
      { funext, rw [pow_succ, ←one_div_mul_one_div] },
      { rw ←mul_zero (0 : ℝ) }
    },
    change is_limit (mul_seq (λ n, 1 / (↑n + 1)) (λ n, (1 / (↑n + 1) ^ (k + 1)))) (0 * 0),
    exact lim_mul_eq_mul_lim limit_of_reciprocal hk,
  }
end

-- Remark 3.12
example : is_limit (λ n, ((n + 1) ^ 2 + 5) / ((n + 1) ^ 3 - (n + 1) + 6)) 0 := begin
  have hsimp : (λ (n : ℕ), (((↑n : ℝ) + 1) ^ 2 + 5) / ((↑n + 1) ^ 3 - (↑n + 1) + 6)) =
    (λ (n : ℕ), (1 / (↑n + 1) + 5 * (1 / (↑n + 1) ^ 3)) / (1  + -1 * (1 / (↑n + 1) ^ 2) + 6 * (1 / (↑n + 1) ^ 3))) :=
  begin
    funext,
    have hn : 1 + (n : ℝ) ≠ 0 := by { norm_cast, norm_num },
    conv_rhs { rw ←mul_div_mul_right' _ _ (pow_ne_zero 3 hn) },
    refine congr (congr_arg has_div.div _) _,
    all_goals { field_simp [hn], ring }
  end,
  conv_rhs at hsimp {
    change
      div_seq
        (add_seq
          (λ n, 1 / (↑n + 1))
          (mul_seq
            (const_seq 5)
            (λ n, 1 / (↑n + 1) ^ 3)))
        (add_seq
          (add_seq
            (const_seq 1)
            (mul_seq
              (const_seq (-1))
              (λ n, 1 / (↑n + 1) ^ 2)))
          (mul_seq
            (const_seq 6)
            (λ n, 1 / (↑n + 1) ^ 3)))
  },
  have hsimp' : (0 : ℝ) = (0 + 5 * 0) / (1 + (-1) * 0 + 6 * 0) := by norm_num,
  conv { congr, { rw hsimp }, { rw hsimp' } },
  exact lim_div_eq_div_lim (by norm_num)
    (lim_add_eq_add_lim
      limit_of_reciprocal
      (lim_mul_eq_mul_lim
        lim_of_const_seq
        lim_of_neg_pow))
    (lim_add_eq_add_lim
      (lim_add_eq_add_lim
        lim_of_const_seq
        (lim_mul_eq_mul_lim
          lim_of_const_seq
          lim_of_neg_pow))
      (lim_mul_eq_mul_lim
        lim_of_const_seq
        lim_of_neg_pow)),
end

end MATH40002