import seq_def
import data.set.intervals.basic

namespace MATH40002

open real_seq
open classical

local attribute [instance] classical.prop_decidable

-- Some useful lemmas
lemma div_lt_iff'' {a b c : ℝ} (hb : b > 0) (hc : c > 0) : a / b < c ↔ a / c < b :=
  by rw [div_lt_iff hb, div_lt_iff' hc]

-- Chapter 3 : Sequences

-- Section 3.1 : Convergence of Sequences
section sec_3_1

-- Example 3.4
lemma lim_of_reciprocal : is_limit (λ n, 1 / (n + 1)) 0 := begin
  intros ε hε,
  cases exists_nat_one_div_lt hε with N hN,
  existsi N,
  intros n hn,
  rw sub_zero,
  dsimp,
  rw abs_of_pos (nat.one_div_pos_of_nat : 1 / ((n : ℝ) + 1) > 0),
  refine lt_of_le_of_lt _ hN,
  rw one_div_le_one_div (nat.cast_add_one_pos n : 0 < (n : ℝ) + 1) (nat.cast_add_one_pos N : 0 < (N : ℝ) + 1),
  norm_cast,
  exact add_le_add_right' hn,
end

-- Example 3.5
example : is_limit (λ n, (n + 5) / (n + 1)) 1 := begin
  intros ε hε,
  have hε' : 0 < 4 / ε := div_pos four_pos hε,
  cases exists_nat_gt (4 / ε) with N hN,
  existsi N + 1,
  intros n hn,
  change abs (((n : ℝ) + 5) / (n + 1) - 1) < ε,
  have hN' : 0 < (N : ℝ) + 1 := nat.cast_add_one_pos N,
  have hn' : 0 < (n : ℝ) + 1 := nat.cast_add_one_pos n,
  rw abs_of_pos,
  show ((n : ℝ) + 5) / (n + 1) - 1 > 0, by {
    rw [gt_iff_lt, sub_pos],
    refine one_lt_div_of_lt (n + 5) hn' _,
    norm_num,
  },
  calc
    ((n : ℝ) + 5) / (n + 1) - 1 = (n + 5) / (n + 1) - (n + 1) / (n + 1) : by rw div_self (ne_of_gt hn')
      ... = 4 / (n + 1) : by ring
      ... < 4 / (N + 1) : by {
        rw div_lt_div_left four_pos hn' hN',
        norm_cast,
        exact add_lt_add_right hn 1,
      }
      ... < ε : by {
        rw div_lt_iff'' hN' hε,
        exact lt_trans hN (lt_add_one ↑N),
      },
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
  have hn_pos : (n : ℝ) > 0 := lt_trans four_pos hn_gt_4,
  change abs (((n : ℝ) + 2) / (n - 2) - 1) < ε,
  calc
    abs (((n : ℝ) + 2) / (n - 2) - 1) = abs (4 / ((n : ℝ) - 2)) : by {
        have hn' : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hn_gt_2),
        refine congr_arg abs _,
        conv_lhs {
          congr,
          skip,
          rw ←div_self hn'
        },
        field_simp [hn],
        ring
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
  have h_even : N ≤ 2 * N := nat.le_mul_of_pos_left zero_lt_two,
  have h_odd : N ≤ 2 * N + 1 := nat.le_succ_of_le h_even,
  replace h_even : abs (δ - l) < δ := begin
    have H : abs ((-1) ^ (2 * N) * δ - l) < δ := hN (2 * N) h_even,
    rwa [neg_one_pow_eq_pow_mod_two, nat.mul_mod_right, pow_zero, one_mul] at H,
  end,
  replace h_odd : abs (δ + l) < δ := begin
    have H : abs ((-1) ^ (2 * N + 1) * δ - l) < δ := hN (2 * N + 1) h_odd,
    rw [neg_one_pow_eq_pow_mod_two, add_comm, nat.add_mul_mod_self_left] at H,
    change 1 % 2 with 1 at H,
    rwa [pow_one, neg_one_mul, ←abs_neg, sub_eq_add_neg, neg_add, neg_neg, neg_neg] at H,
  end,
  refine lt_irrefl (2 * δ) _,
  calc
    2 * δ = abs (2 * δ) : eq.symm (abs_of_pos (mul_pos' zero_lt_two h₁))
      ... = abs ((δ - l) + (δ + l)) : congr_arg abs (by ring)
      ... ≤ abs (δ - l) + abs (δ + l) : abs_add (δ - l) (δ + l)
      ... < δ + δ : add_lt_add h_even h_odd
      ... = 2 * δ : eq.symm (two_mul δ)
end

lemma close_implies_eq (a b : ℝ) : (∀ ε > 0, abs (a - b) < ε) → a = b := begin
  intro h,
  rw ←sub_eq_zero,
  by_contradiction h',
  exact lt_irrefl (abs (a - b)) (h (abs (a - b)) (abs_pos_of_ne_zero h')),
end

-- Theorem 3.9 (Uniqueness of limits)
theorem limit_unique {a : seq} {l₁ l₂ : ℝ} (h₁ : is_limit a l₁) (h₂ : is_limit a l₂) : l₁ = l₂ := begin
  refine close_implies_eq l₁ l₂ _,
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
lemma bdd_of_converges {a : seq} : seq_converges a → seq_bdd a := begin
  intro ha,
  cases ha with l hl,
  cases hl 1 zero_lt_one with N hN,
  let head : finset ℝ := (finset.range (N + 1)).image (abs ∘ a),
  have head_has_mem : abs (a 0) ∈ head := begin
    refine finset.mem_image_of_mem (abs ∘ a) _,
    rw finset.mem_range,
    exact nat.succ_pos N,
  end,
  cases finset.max_of_mem head_has_mem with B hB,
  let M := max B (abs l + 1),
  have hM : M > 0 := begin
    refine lt_of_lt_of_le zero_lt_one (le_max_right_of_le _),
    rw le_add_iff_nonneg_left,
    exact abs_nonneg l,
  end,
  existsi [M, hM],
  intro n,
  cases le_or_gt n N with h h,
  { refine le_trans (finset.le_max_of_mem _ hB) (le_max_left B (abs l + 1)),
    refine finset.mem_image_of_mem (abs ∘ a) _,
    rw finset.mem_range,
    exact nat.lt_succ_of_le h,
  },
  { have h' : abs (a n) - abs l < 1 := lt_of_le_of_lt (abs_sub_abs_le_abs_sub (a n) l) (hN n (le_of_lt h)),
    rw sub_lt_iff_lt_add' at h',
    exact le_trans (le_of_lt h') (le_max_right B (abs l + 1)),
  }
end

-- Theorem 3.11 (Algebra of limits)
theorem lim_add_eq_add_lim {a b : seq} {la lb : ℝ} (hla : is_limit a la) (hlb : is_limit b lb) :
  is_limit (a + b) (la + lb) :=
begin
  intros ε hε,
  cases hla (ε / 2) (half_pos hε) with Na hNa,
  cases hlb (ε / 2) (half_pos hε) with Nb hNb,
  let N := max Na Nb,
  existsi N,
  intros n Hn,
  replace hNa := hNa n (le_trans (le_max_left Na Nb) Hn),
  replace hNb := hNb n (le_trans (le_max_right Na Nb) Hn),
  calc
    abs (a n + b n - (la + lb)) = abs ((a n - la) + (b n - lb)) : congr_arg abs (by ring)
      ... ≤ abs (a n - la) + abs (b n - lb) : abs_add (a n - la) (b n - lb)
      ... < ε / 2 + ε / 2 : add_lt_add hNa hNb
      ... = ε : add_halves ε,
end

theorem lim_mul_eq_mul_lim {a b : seq} {la lb : ℝ} (hla : is_limit a la) (hlb : is_limit b lb) :
  is_limit (a * b) (la * lb) :=
begin
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
  have h₁ : abs (a n - la) * abs lb < ε / 2 := calc
      abs (a n - la) * abs lb ≤ (ε / (2 * (abs lb + 1))) * abs lb : mul_le_mul_of_nonneg_right (le_of_lt hNa) (abs_nonneg lb)
        ... = ε * abs lb / (2 * (abs lb + 1)) : by field_simp
        ... < ε / 2 : by {
          rw [div_lt_iff' H, ←mul_lt_mul_right zero_lt_two, ←sub_pos],
          field_simp,
          ring,
          exact mul_pos' zero_lt_two hε,
        },
  have h₂ : abs (a n) * abs (b n - lb) ≤ ε / 2 := calc
      abs (a n) * abs (b n - lb) ≤ A * (ε / (2 * A)) : mul_le_mul hA₂ (le_of_lt hNb) (abs_nonneg (b n - lb)) (le_of_lt hA₁)
        ... = ε / 2 : by { field_simp [ne_of_gt hA₁], ring, },
  calc
    abs (a n * b n - la * lb) = abs ((a n - la) * lb + a n * (b n - lb)) : by ring
      ... ≤ abs ((a n - la) * lb) + abs(a n * (b n - lb)) : abs_add ((a n - la) * lb) (a n * (b n - lb))
      ... = abs (a n - la) * abs lb + abs (a n) * abs (b n - lb) : by rw [abs_mul, abs_mul]
      ... < ε / 2 + ε / 2 : add_lt_add_of_lt_of_le h₁ h₂
      ... = ε : add_halves ε,
end

theorem lim_div_eq_div_lim {a b : seq} {la lb : ℝ} (hlb_ne_zero : lb ≠ 0) (hla : is_limit a la) (hlb : is_limit b lb) :
  is_limit (a / b) (la / lb) :=
begin
  have hla' : 4 * abs la + 1 > 0 := lt_of_le_of_lt (mul_nonneg (by norm_num) (abs_nonneg la)) (lt_add_one (4 * abs la)),
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
  have hbn : b n ≠ 0 := abs_pos_iff.mp (lt_trans (half_pos hlb') hN₁),
  have h_main : abs ((a n - la) * lb + la * (lb - b n)) < ε * abs lb * abs lb / 2 := calc
    abs ((a n - la) * lb + la * (lb - b n)) ≤ abs ((a n - la) * lb) + abs (la * (lb - b n)) : abs_add _ _
      ... = abs (a n - la) * abs lb + abs la * abs (b n - lb) : by rw [abs_mul, abs_mul, abs_sub lb (b n)]
      ... < (ε * abs lb / 4) * abs lb + abs la * ε * abs lb ^ 2 / (4 * abs la + 1) : by {
        refine add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_right hN₂ hlb') _,
        have hsimp : abs la * ε * abs lb ^ 2 / (4 * abs la + 1) = abs la * (ε * abs lb ^ 2 / (4 * abs la + 1)) := by ring,
        rw hsimp,
        exact mul_le_mul_of_nonneg_left (le_of_lt hN₃) (abs_nonneg la),
      }
      ... = ε * abs lb * abs lb * (1 / 4 + abs la / (4 * abs la + 1)) : by { rw pow_two, ring }
      ... < (ε * abs lb * abs lb) * (1 / 2) : by {
        refine mul_lt_mul_of_pos_left _ (mul_pos (mul_pos hε hlb') hlb'),
        have hsimp : (1 / 2 : ℝ) = 1 / 4 + 1 / 4 := by norm_num,
        rw [hsimp, add_lt_add_iff_left, div_lt_iff' hla', ←div_eq_mul_one_div, lt_div_iff' (by norm_num : (0 : ℝ) < 4)],
        exact lt_add_one (4 * abs la),
      }
      ... = ε * abs lb * abs lb / 2 : by ring,
  calc
    abs (a n / b n - la / lb) = abs ((a n * lb - b n * la) / (b n * lb)) : congr_arg abs (div_sub_div (a n) la hbn hlb_ne_zero)
      ... = abs (a n * lb - b n * la) / abs (b n * lb) : abs_div _ _
      ... = abs (a n * lb - b n * la) / (abs (b n) * abs lb) : by rw abs_mul
      ... = abs (a n * lb - b n * la) / (abs lb * abs (b n)) : by rw mul_comm (abs (b n)) (abs lb)
      ... = (abs (a n * lb - b n * la) / abs lb) * (1 / abs (b n)) : by rw div_mul_eq_div_mul_one_div 
      ... ≤ (abs (a n * lb - b n * la) / abs lb) * (2 / abs lb) : by {
        refine mul_le_mul_of_nonneg_left _ (div_nonneg (abs_nonneg _) hlb'),
        rw [div_le_div_iff (abs_pos_of_ne_zero hbn) hlb', one_mul],
        rw [gt_iff_lt, div_lt_iff' two_pos] at hN₁,
        exact le_of_lt hN₁,
      }
      ... = abs (a n * lb - b n * la) * (2 / (abs lb * abs lb)) : by field_simp
      ... = abs ((a n - la) * lb + la * (lb - b n)) * (2 / (abs lb * abs lb)) : congr_arg (λ x, (abs x) * (2 / (abs lb * abs lb))) (by ring)
      ... < (ε * abs lb * abs lb / 2) * (2 / (abs lb * abs lb)) : mul_lt_mul_of_pos_right h_main (div_pos (by norm_num) (mul_pos hlb' hlb'))
      ... = ε : by { field_simp [ne_of_gt hlb'], ring },
end

-- Additional stuff related to algebra of limits
lemma lim_of_const_seq {a : ℝ} : is_limit (const_seq a) a := begin
  intros ε hε,
  existsi 0,
  intros n Hn,
  unfold const_seq,
  rwa [sub_self, abs_zero],
end

theorem lim_neg_eq_neg_lim {a : seq} {la : ℝ} (hla : is_limit a la) : is_limit (-a) (-la) := begin
  conv {
    congr,
    { change (λ n, -a n), funext, rw neg_eq_neg_one_mul },
    { rw neg_eq_neg_one_mul }
  },
  exact lim_mul_eq_mul_lim lim_of_const_seq hla,
end

theorem lim_sub_eq_sub_lim {a b : seq} {la lb : ℝ} (hla : is_limit a la) (hlb : is_limit b lb) :
  is_limit (a - b) (la - lb) := lim_add_eq_add_lim hla (lim_neg_eq_neg_lim hlb)

theorem lim_abs_eq_abs_lim {a : seq} {la : ℝ} (hla : is_limit a la) : is_limit (abs ∘ a) (abs la) := begin
  intros ε hε,
  cases hla ε hε with N hN,
  existsi N,
  intros n hn,
  exact lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub (a n) la) (hN n hn),
end

theorem lim_pow_eq_pow_lim {a : seq} {la : ℝ} {n : ℕ} (hla : is_limit a la) : is_limit ((^ n) ∘ a) (la ^ n) := begin
  induction n with n hn,
  { simp,
    exact lim_of_const_seq,
  },
  { conv {
      congr,
      { change (λ k, (a k) ^ (n + 1)),
        funext,
        rw pow_succ,
      },
      { rw pow_succ }
    },
    exact lim_mul_eq_mul_lim hla hn,
  }
end

theorem lim_sqrt_eq_sqrt_lim {a : seq} {la : ℝ} (ha : ∀ n, a n ≥ 0) (hla : is_limit a la) :
  is_limit (real.sqrt ∘ a) (real.sqrt la) :=
begin
  sorry,
end

lemma lim_of_tail {a : seq} {la : ℝ} (k : ℕ) (hla : is_limit a la) : is_limit (a ∘ (+ k)) la := begin
  intros ε hε,
  cases hla ε hε with N hN,
  existsi N,
  intros n hn,
  exact hN (n + k) (le_add_right hn),
end

lemma lim_of_neg_pow {k : ℕ} : is_limit (λ n, (1 : ℝ) / ((n + 1) ^ (k + 1))) 0 := begin
  have h : ∀ (n : ℕ), (n : ℝ) + 1 ≠ 0 := begin
    intro n,
    norm_cast,
    exact nat.succ_ne_zero n,
  end,
  conv {
    congr,
    { funext,
      rw [pow_succ, ←one_div_mul_one_div, ←one_div_pow (h n)],
    },
    { rw ←zero_mul (0 ^ k : ℝ) }
  },
  refine lim_mul_eq_mul_lim (lim_of_reciprocal) (lim_pow_eq_pow_lim lim_of_reciprocal),
end

-- Remark 3.12
example : is_limit (λ n, ((n + 1) ^ 2 + 5) / ((n + 1) ^ 3 - (n + 1) + 6)) 0 := begin
  have hsimp : (λ (n : ℕ), (((↑n : ℝ) + 1) ^ 2 + 5) / ((↑n + 1) ^ 3 - (↑n + 1) + 6)) =
    (λ (n : ℕ), (1 / (↑n + 1) + 5 * (1 / (↑n + 1) ^ 3)) / (1 - (1 / (↑n + 1) ^ 2) + 6 * (1 / (↑n + 1) ^ 3))) :=
  begin
    funext,
    have hn : 1 + (n : ℝ) ≠ 0 := by { norm_cast, norm_num },
    conv_rhs { rw ←mul_div_mul_right' _ _ (pow_ne_zero 3 hn) },
    refine congr (congr_arg has_div.div _) _,
    all_goals { field_simp [hn], ring }
  end,
  have hsimp' : (0 : ℝ) = (0 + 5 * 0) / (1 - 0 + 6 * 0) := by norm_num,
  conv {
    congr,
    { rw hsimp },
    { rw hsimp' }
  },
  exact
    lim_div_eq_div_lim (by norm_num)
      (lim_add_eq_add_lim
        lim_of_reciprocal
        (lim_mul_eq_mul_lim
          lim_of_const_seq
          lim_of_neg_pow))
      (lim_add_eq_add_lim
        (lim_sub_eq_sub_lim
          lim_of_const_seq
          lim_of_neg_pow)
        (lim_mul_eq_mul_lim
          lim_of_const_seq
          lim_of_neg_pow)),
end

-- Theorem 3.13 (Monotone convergence theorem)
theorem lim_of_bounded_increasing_seq {a : seq} (ha : seq_increasing a) (ha' : seq_bdd_above a) :
  is_limit a (real.Sup (set.range a)) :=
begin
  set l := real.Sup (set.range a),
  intros ε hε,
  have h : is_lub (set.range a) l := begin 
    cases ha' with b hb,
    exact real.is_lub_Sup (set.mem_range_self 0) hb,
  end,
  have h' : l - ε < l := by linarith only [hε],
  rw lt_is_lub_iff h at h',
  rcases h' with ⟨x, ⟨⟨N, hx⟩, haN⟩⟩,
  rw ←hx at haN,
  clear h hx x,
  existsi N,
  intros n hn,
  rw abs_lt,
  split,
  { rw lt_sub_iff_add_lt',
    exact lt_of_lt_of_le haN (ha hn),
  },
  { refine lt_of_le_of_lt _ hε,
    rw sub_nonpos,
    exact real.le_Sup (set.range a) ha' (set.mem_range_self n),
  }
end

theorem lim_of_bounded_decreaing_seq {a : seq} (ha : seq_decreasing a) (ha' : seq_bdd_below a) :
  is_limit a (real.Inf (set.range a)) :=
begin
  let b : seq := -a,
  have h_simp : set.range a = (λ x, -x) '' set.range (b : seq) := begin
    rw ←neg_neg a,
    exact set.range_comp,
  end,
  conv {
    congr,
    { rw ←neg_neg a, change -b },
    { rw h_simp }
  },
  refine lim_neg_eq_neg_lim _,
  simp,
  refine lim_of_bounded_increasing_seq ha _,
  cases ha' with x hx,
  existsi -x,
  rintros y ⟨n, hn⟩,
  rw ←hn,
  clear hn y,
  change -(a n) ≤ -x,
  rw neg_le_neg_iff,
  exact hx (set.mem_range_self n),
end

-- Example 3.14 (Order limit theorem)
theorem lim_le_of_seq_le {a b : seq} {la lb : ℝ} (hab : ∀ n, a n ≤ b n) (hla : is_limit a la) (hlb : is_limit b lb) :
  la ≤ lb :=
begin
  by_contradiction h,
  rw [not_le, ←sub_pos] at h,
  cases lim_sub_eq_sub_lim hla hlb (la - lb) h with N hN,
  replace hN := lt_of_le_of_lt (neg_le_abs_self _) (hN N (le_refl N)),
  simp at hN,
  rw neg_lt_zero at hN,
  change 0 < a N - b N at hN,
  rw sub_pos at hN,
  exact lt_irrefl _ (lt_of_lt_of_le hN (hab N)),
end

-- Problem Sheet 5: Question 1
lemma bernoulli_inequality {n : ℕ} {x : ℝ} (hx : x > -1) : (1 + x) ^ n ≥ 1 + n * x := begin
  induction n with n hn,
  { simp },
  { have hx' : 1 + x > 0 := by rwa [gt_iff_lt, ←sub_pos, sub_neg_eq_add, add_comm] at hx,
    calc
    (1 + x) ^ (n + 1) = (1 + x) * (1 + x) ^ n : by rw pow_succ
      ... ≥ (1 + x) * (1 + n * x) : by { rw ge_iff_le, rw mul_le_mul_left hx', exact hn }
      ... = 1 + (n + 1) * x + n * (x ^ 2) : by ring
      ... ≥ 1 + (n + 1) * x : le_add_of_nonneg_right (mul_nonneg (nat.cast_nonneg n) (pow_two_nonneg x)),
  }
end

lemma lim_of_geom_zero_aux {x : ℝ} (hx : x > 0) : is_limit (λ n, 1 / (1 + x) ^ n) 0 := begin
  intros ε hε,
  cases exists_nat_gt (1 / (ε * x)) with N hN,
  existsi N,
  intros n hn,
  have hx' : (1 + x) ^ n > 0 := pow_pos (add_pos zero_lt_one hx) n,
  rw sub_zero,
  rw abs_of_pos (one_div_pos_of_pos hx'),
  rw div_lt_iff'' hx' hε,
  calc
    1 / ε < N * x : by { rw ←div_lt_iff hx, rw div_div_eq_div_mul, exact hN }
      ... < 1 + N * x : lt_one_add (N * x)
      ... ≤ 1 + n * x : by { refine add_le_add_left _ 1, rw mul_le_mul_right hx, exact nat.cast_le.mpr hn }
      ... ≤ (1 + x) ^ n : bernoulli_inequality (lt_trans (by norm_num) hx),
end

lemma lim_of_geom_zero {r : ℝ} (hr : r ∈ set.Ioo (0 : ℝ) (1 : ℝ)) : is_limit (λ n, r ^ n) 0 := begin
  let x := 1 / r - 1,
  cases hr with hr_pos hr_lt_one,
  have hx' : ∀ (n : ℕ), r ^ n = 1 / (1 + x) ^ n := begin
    have h : r = 1 / (1 + x) := begin
      change r = 1 / (1 + (1 / r - 1)),
      field_simp,
    end,
    intro n,
    rw h,
    refine one_div_pow _ n,
    change ¬ 1 + (1 / r - 1) = 0,
    simp,
    exact ne_of_gt hr_pos,
  end,
  conv {
    congr,
    { funext,
      rw hx'
    }
  },
  refine lim_of_geom_zero_aux _,
  change 0 < (1 / r) - 1,
  rw sub_pos,
  exact one_lt_one_div hr_pos hr_lt_one,
end

lemma lim_of_geom_inf {r : ℝ} (hr : r ∈ set.Ioi (1 : ℝ)) : seq_diverges_to_pos_inf (λ n, r ^ n) := begin
  let x := r - 1,
  simp at hr,
  have hx : r = 1 + x := begin
    change r = 1 + (r - 1),
    rw add_eq_of_eq_sub',
    refl,
  end,
  have hx' : x > 0 := sub_pos_of_lt hr,
  intros M hM,
  cases exists_nat_gt (M / x) with N hN,
  existsi N,
  intros n hn,
  calc
    r ^ n = (1 + x) ^ n : congr_fun (congr_arg pow hx) n
      ... ≥ 1 + n * x : bernoulli_inequality (lt_trans (by norm_num) hx')
      ... > n * x : lt_one_add (n * x)
      ... ≥ N * x : by { rw [ge_iff_le, mul_le_mul_right hx'], exact nat.cast_le.mpr hn }
      ... > M : (div_lt_iff hx').mp hN,
end

-- Example 3.15
example (a : seq) (L : ℝ) (ha : ∀ n, a n ≠ 0) (hL_lt_one : L < 1) (hL : is_limit (λ n, abs (a (n + 1) / a n)) L) :
  is_limit a 0 :=
begin
  have hL_bd : L ∈ set.Ico (0 : ℝ) (1 : ℝ) := begin
    refine ⟨lim_le_of_seq_le _ lim_of_const_seq hL, hL_lt_one⟩,
    intro n,
    exact abs_nonneg _, 
  end,
  clear hL_lt_one,
  intros ε hε,
  cases hL ((1 - L) / 2) _ with N hN,
  show (1 - L) / 2 > 0, from half_pos (sub_pos.2 hL_bd.2),
  set L' := (1 + L) / 2,
  have hL'_bd : L' ∈ set.Ioo (0 : ℝ) (1 : ℝ) := begin
    change L' with (1 + L) / 2,
    split,
    all_goals { linarith only [hL_bd.1, hL_bd.2] },
  end,
  have hL' : ∀ k, abs (a (N + k)) ≤ L' ^ k * abs (a N) := begin
    intro k,
    induction k with k hk,
    { rw [add_zero, pow_zero, one_mul] },
    { calc
        abs (a (N + k + 1)) ≤ L' * abs (a (N + k)) : by {
            rw [←div_le_iff (abs_pos_of_ne_zero (ha (N + k))), ←abs_div],
            refine le_of_lt _,
            have h : L' = (1 - L) / 2 + L := begin
              change (1 + L) / 2 = (1 - L) / 2 + L,
              ring,
            end,
            rw [h, ←sub_lt_iff_lt_add],
            exact lt_of_le_of_lt (le_abs_self _) (hN (N + k) (nat.le_add_right N k)),
          }
          ... ≤ L' * (L' ^ k * abs (a N)) : by { rw mul_le_mul_left hL'_bd.1, exact hk }
          ... = L' ^ (k + 1) * abs (a N) : by rw [←mul_assoc, ←pow_succ],
    }
  end,
  cases lim_of_geom_zero hL'_bd (ε / abs (a N)) _ with M hM,
  show ε / abs (a N) > 0, from div_pos hε (abs_pos_of_ne_zero (ha N)),
  existsi N + M,
  intros n hn,
  cases nat.le.dest hn with k hk,
  rw [sub_zero, ←hk],
  replace hM := hM M (le_refl M),
  simp at hM,
  rw [lt_div_iff (abs_pos_of_ne_zero (ha N)), abs_of_pos (pow_pos (hL'_bd.1) M)] at hM,
  replace hL' := hL' (M + k),
  rw ←add_assoc at hL',
  calc
    abs (a (N + M + k)) ≤ L' ^ (M + k) * abs (a N) : hL'
      ... ≤ L' ^ M * abs (a N) : by {
        rw [mul_le_mul_right (abs_pos_of_ne_zero (ha N)), pow_add, mul_le_iff_le_one_right (pow_pos (hL'_bd.1) M)],
        exact pow_le_one k (le_of_lt hL'_bd.1) (le_of_lt hL'_bd.2)
      }
      ... < ε : hM,
end

end sec_3_1

-- Section 3.2 : Cauchy Sequences
section sec_3_2

-- Proposition 3.17
lemma cauchy_of_converges {a : seq} : seq_converges a → seq_cauchy a := begin
  rintros ⟨l, hl⟩ ε hε,
  cases hl (ε / 2) (half_pos hε) with N hN,
  existsi N,
  intros m hm n hn,
  calc
    abs (a n - a m) = abs ((a n - l) + (l - a m)) : by ring
      ... ≤ abs (a n - l) + abs (l - a m) : abs_add (a n - l) (l - a m)
      ... = abs (a n - l) + abs (a m - l) : by rw abs_sub l (a m)
      ... < ε / 2 + ε / 2 : add_lt_add (hN n hn) (hN m hm)
      ... = ε : add_halves ε,
end

-- Lemma 3.18
lemma bdd_of_cauchy {a : seq} : seq_cauchy a → seq_bdd a := begin
  intro ha,
  cases ha 1 zero_lt_one with N hN,
  replace hN := hN N (le_refl N),
  let head : finset ℝ := (finset.range (N + 1)).image (abs ∘ a),
  have head_has_mem : abs (a 0) ∈ head := begin
    refine finset.mem_image_of_mem (abs ∘ a) _,
    rw finset.mem_range,
    exact nat.succ_pos N,
  end,
  cases finset.max_of_mem head_has_mem with B hB,
  let M := max B (abs (a N) + 1),
  have hM : M > 0 := begin
    refine lt_of_lt_of_le zero_lt_one (le_max_right_of_le _),
    rw le_add_iff_nonneg_left,
    exact abs_nonneg (a N),
  end,
  existsi [M, hM],
  intro n,
  cases le_or_gt n N with h h,
  { refine le_trans (finset.le_max_of_mem _ hB) (le_max_left B (abs (a N) + 1)),
    refine finset.mem_image_of_mem (abs ∘ a) _,
    rw finset.mem_range,
    exact nat.lt_succ_of_le h,
  },
  { have h' : abs (a n) - abs (a N) < 1 := lt_of_le_of_lt (abs_sub_abs_le_abs_sub (a n) (a N)) (hN n (le_of_lt h)),
    rw sub_lt_iff_lt_add' at h',
    exact le_trans (le_of_lt h') (le_max_right B (abs (a N) + 1)),
  }
end

lemma bdd_above_of_cauchy {a : seq} : seq_cauchy a → seq_bdd_above a :=
  λ ha, seq_bdd_above_of_bdd $ bdd_of_cauchy ha

lemma bdd_below_of_cauchy {a : seq} : seq_cauchy a → seq_bdd_below a :=
  λ ha, seq_bdd_below_of_bdd $ bdd_of_cauchy ha

-- Some lemmas for Theorem 3.19
lemma Sup_subset_le_Sup {A B : set ℝ} (h : B ⊆ A) (ha_bdd : bdd_above A) (hb_nonempty : B ≠ ∅) : real.Sup B ≤ real.Sup A := begin
  refine real.Sup_le_ub B (set.exists_mem_of_ne_empty hb_nonempty) _,
  intros x hx,
  exact real.le_Sup A ha_bdd (h hx),
end

lemma Inf_le_Inf_subset {A B : set ℝ} (h : B ⊆ A) (ha_bdd : bdd_below A) (hb_nonempty : B ≠ ∅) : real.Inf A ≤ real.Inf B := begin
  refine real.lb_le_Inf B (set.exists_mem_of_ne_empty hb_nonempty) _,
  intros x hx,
  exact real.Inf_le A ha_bdd (h hx),
end

lemma bdd_above_of_tail {a : seq} (k : ℕ) (ha : seq_bdd_above a) : seq_bdd_above (a ∘ (+ k)) := 
  bdd_above_subset (set.range_comp_subset_range (+ k) a) ha

lemma bdd_below_of_tail {a : seq} (k : ℕ) (ha : seq_bdd_below a) : seq_bdd_below (a ∘ (+ k)) := 
  bdd_below_subset (set.range_comp_subset_range (+ k) a) ha

lemma range_add_eq_Ici (n : ℕ) : set.range (+ n) = set.Ici n := begin
  refine set.ext _,
  intro x,
  simp,
  split,
  { rintro ⟨y, hy⟩,
    exact nat.le.intro hy,
  },
  { exact nat.le.dest }
end

lemma range_add_subset_range_add {m n : ℕ} (h : m ≤ n) : set.range (+ n) ⊆ set.range (+ m) := begin
  rw [range_add_eq_Ici, range_add_eq_Ici],
  intros x hx,
  exact le_trans h hx,
end

lemma Inf_decreasing_eq_Inf_tail {a : seq} (n : ℕ) (ha_decr : seq_decreasing a) (ha_bdd : seq_bdd_below a) :
  real.Inf (set.range a) = real.Inf (set.range (a ∘ (+ n))) :=
begin
  refine le_antisymm _ _,
  { refine Inf_le_Inf_subset _ ha_bdd _,
    { exact set.range_comp_subset_range (+ n) a },
    { exact set.range_ne_empty (a ∘ (+ n)) },
  },
  { refine real.lb_le_Inf (set.range a) _ _,
    { exact set.exists_mem_of_ne_empty (set.range_ne_empty a) },
    { rintros x ⟨k, hk⟩,
      rw ←hk,
      cases le_or_gt n k with h h,
      { refine real.Inf_le (set.range (a ∘ (+ n))) (bdd_below_of_tail n ha_bdd) _,
        rw set.range_comp,
        refine set.mem_image_of_mem a _,
        simp,
        exact nat.le.dest h,
      },
      { replace h := ha_decr (le_of_lt h),
        change -a k ≤ -a n at h,
        rw neg_le_neg_iff at h,
        refine le_trans _ h,
        refine real.Inf_le (set.range (a ∘ (+ n))) (bdd_below_of_tail n ha_bdd) _,
        existsi 0,
        simp,
      }
    }
  }
end

-- Theorem 3.19
theorem converges_of_cauchy {a : seq} : seq_cauchy a → seq_converges a := begin
  intro ha,
  have ha_bdd_above := bdd_above_of_cauchy ha,
  let b : seq := λ n, real.Sup (set.range (a ∘ (+ n))),
  have hb_decr : seq_decreasing b := begin
    intros m n hmn,
    change -real.Sup (set.range (a ∘ (+ m))) ≤ -real.Sup (set.range (a ∘ (+ n))),
    rw neg_le_neg_iff,
    refine Sup_subset_le_Sup _ _ _,
    { rw [set.range_comp, set.range_comp],
      refine set.image_subset a _,
      exact range_add_subset_range_add hmn,
    },
    { exact bdd_above_of_tail m ha_bdd_above },
    { exact set.range_ne_empty (a ∘ (+ n)) }
  end,
  have hb_bdd_below : seq_bdd_below b := begin
    cases bdd_below_of_cauchy ha with A hA,
    existsi A,
    rintros x ⟨k, hk⟩,
    rw ←hk,
    change A ≤ real.Sup (set.range (a ∘ (+ k))),
    refine le_trans (hA (set.mem_range_self k)) _,
    refine real.le_Sup (set.range (a ∘ (+ k))) (bdd_above_of_tail k ha_bdd_above) _,
    rw set.range_comp,
    refine set.mem_image_of_mem a _,
    existsi 0,
    exact zero_add k,
  end,
  have hb := lim_of_bounded_decreaing_seq hb_decr hb_bdd_below,
  set lb := real.Inf (set.range b),
  existsi lb,
  intros ε hε,
  cases ha (ε / 2) (half_pos hε) with N hN,
  existsi N,
  intros n hn,
  refine lt_of_le_of_lt _ (half_lt_self hε),
  rw abs_le,
  split,
  { rw neg_le_sub_iff_le_add,
    change real.Inf (set.range b) ≤ a n + ε / 2,
    refine le_trans (real.Inf_le (set.range b) hb_bdd_below (set.mem_range_self N)) _,
    change real.Sup (set.range (a ∘ (+ N))) ≤ a n + ε / 2,
    refine real.Sup_le_ub (set.range (a ∘ (+ N))) _ _,
    show ∃ (x : ℝ), x ∈ set.range (a ∘ (+ N)), from set.exists_mem_of_ne_empty (set.range_ne_empty (a ∘ (+ N))),
    rintros x ⟨k, hk⟩,
    rw ←hk,
    refine le_of_lt _,
    have h := (abs_lt.1 (hN n hn (k + N) (nat.le_add_left N k))).2,
    rw sub_lt_iff_lt_add' at h,
    exact h,
  },
  { rw sub_le,
    have h : lb = real.Inf (set.range (b ∘ (+ N))) := Inf_decreasing_eq_Inf_tail N hb_decr hb_bdd_below,
    rw h,
    rw real.le_Inf,
    { rintros x ⟨k, hk⟩,
      change b (k + N) = x at hk,
      rw ←hk,
      change a n - ε / 2 ≤ real.Sup (set.range (a ∘ (+ (k + N)))),
      refine le_trans (le_of_lt _) _,
      show a n - ε / 2 < a (k + N), by {
        rw sub_lt,
        exact (abs_lt.1 (hN (k + N) (nat.le_add_left N k) n hn)).2,
      },
      refine real.le_Sup (set.range (a ∘ (+ (k + N)))) (bdd_above_of_tail (k + N) ha_bdd_above) _,
      existsi 0,
      simp,
    },
    { exact set.exists_mem_of_ne_empty (set.range_ne_empty (b ∘ (+ N))) },
    { exact bdd_below_of_tail N hb_bdd_below }
  }
end

-- Corollary 3.20
theorem cauchy_iff_converges {a : seq} : seq_cauchy a ↔ seq_converges a := ⟨converges_of_cauchy, cauchy_of_converges⟩

-- Exercise 3.22
example (M : ℝ) (S : set ℝ) (hS : S ≠ ∅) (hM : ∀ x ∈ S, x < M) : real.Sup S ≤ M := begin
  refine real.Sup_le_ub S (set.exists_mem_of_ne_empty hS) _,
  intros x hx,
  exact le_of_lt (hM x hx),
end

end sec_3_2

-- Section 3.3 : Subsequences
section sec_3_3

-- Exercise 3.24
example (n : ℕ → ℕ) (hn : strict_mono n) : ∀ i, n i ≥ i := begin
  intro i,
  induction i with i hi,
  { exact nat.zero_le (n 0) },
  { exact nat.succ_le_of_lt (lt_of_le_of_lt hi (hn (nat.lt_succ_self i))) }
end

-- Theorem 3.26 (Bolzano-Weierstrass theorem)
theorem exists_convergent_subseq_of_bdd {a : seq} (ha : seq_bdd a) :
  ∃ (n : ℕ → ℕ) (hn : strict_mono n), seq_converges (a ∘ n) :=
begin
  sorry,
end

end sec_3_3

end MATH40002