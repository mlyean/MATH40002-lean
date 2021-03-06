import seq_def
import lemmas
import data.set.intervals.basic
import data.nat.parity

namespace real_seq

-- Chapter 3 : Sequences

-- Section 3.1 : Convergence of Sequences
section sec_3_1

section specific_limits

lemma lim_of_const_seq {a : ℝ} : const_seq a ⟶ a := begin
  intros ε hε,
  existsi 0,
  intros n Hn,
  convert hε,
  erw [sub_self, abs_zero],
end

lemma lim_of_zero : 0 ⟶ 0 := @lim_of_const_seq 0

lemma lim_of_one : 1 ⟶ 1 := @lim_of_const_seq 1

-- Example 3.4
lemma lim_of_reciprocal : (λ n, 1 / (n + 1)) ⟶ 0 := begin
  intros ε hε,
  cases exists_nat_one_div_lt hε with N hN,
  existsi N,
  intros n hn,
  rw [sub_zero, abs_of_pos (@nat.one_div_pos_of_nat ℝ _ n)],
  exact lt_of_le_of_lt (nat.one_div_le_one_div hn) hN,
end

end specific_limits

-- Example 3.5
example : (λ n, (n + 5) / (n + 1)) ⟶ 1 := begin
  intros ε hε,
  cases exists_nat_gt (4 / ε) with N hN,
  existsi N,
  intros n hn,
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
      ... = 4 / (n + 1) : by { rw ←sub_div, norm_num }
      ... ≤ 4 / (N + 1) : by {
        rw div_le_div_left four_pos hn' hN',
        exact add_le_add_right (nat.cast_le.mpr hn) 1,
      }
      ... < ε : (div_lt_iff'' hN' hε).mpr (lt_trans hN (lt_add_one N)),
end

-- Example 3.6
example : (λ n, (n + 2) / (n - 2)) ⟶ 1 := begin
  intros ε hε,
  cases exists_nat_gt (max 4 (8 / ε)) with N hN,
  existsi N,
  intros n hn,
  have hn_gt_4 : (n : ℝ) > 4 := calc
    (n : ℝ) ≥ N : nat.cast_le.mpr hn
      ... > max 4 (8 / ε) : hN
      ... ≥ 4 : le_max_left 4 (8 / ε),
  have hn_gt_2 : (n : ℝ) > 2 := lt_trans (by norm_num) hn_gt_4,
  have hn_pos : (n : ℝ) > 0 := lt_trans four_pos hn_gt_4,
  have hn_sub_2_pos := sub_pos.mpr hn_gt_2,
  change abs (((n : ℝ) + 2) / (n - 2) - 1) < ε,
  calc
    abs (((n : ℝ) + 2) / (n - 2) - 1) = abs (4 / ((n : ℝ) - 2)) : by {
        refine congr_arg abs _,
        have : (n : ℝ) - 2 ≠ 0 := begin
          rw sub_ne_zero,
          exact ne_of_gt hn_gt_2,
        end,
        field_simp [this],
        ring,
      }
      ... = 4 / ((n : ℝ) - 2) : abs_of_pos (div_pos four_pos hn_sub_2_pos)
      ... < 4 / ((n : ℝ) / 2) : by {
        rw [div_lt_div_left four_pos hn_sub_2_pos (half_pos hn_pos), lt_sub, sub_half, lt_div_iff two_pos],
        norm_num,
        exact hn_gt_4,
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
      ... = 2 * δ : eq.symm (two_mul δ),
end

lemma close_implies_eq {a b : ℝ} : (∀ ε > 0, abs (a - b) < ε) → a = b := begin
  intro h,
  rw ←sub_eq_zero,
  by_contradiction h',
  exact lt_irrefl (abs (a - b)) (h (abs (a - b)) (abs_pos_of_ne_zero h')),
end

-- Theorem 3.9 (Uniqueness of limits)
theorem limit_unique {a : seq} {l₁ l₂ : ℝ} (h₁ : a ⟶ l₁) (h₂ : a ⟶ l₂) : l₁ = l₂ := begin
  refine close_implies_eq _,
  intros ε hε,
  cases h₁ (ε / 2) (half_pos hε) with N₁ hN₁,
  cases h₂ (ε / 2) (half_pos hε) with N₂ hN₂,
  let N := max N₁ N₂,
  replace hN₁ := hN₁ N (le_max_left _ _),
  replace hN₂ := hN₂ N (le_max_right _ _),
  calc
    abs (l₁ - l₂) ≤ abs (l₁ - a N) + abs (a N - l₂) : abs_sub_le l₁ (a N) l₂
      ... = abs (a N - l₁) + abs (a N - l₂) : by rw abs_sub
      ... < ε / 2 + ε / 2 : add_lt_add hN₁ hN₂
      ... = ε : add_halves ε,
end

-- Proposition 3.10
lemma bdd_of_converges {a : seq} : seq_converges a → seq_bdd a := begin
  rintro ⟨l, hl⟩,
  cases hl 1 zero_lt_one with N hN,
  let head : finset ℝ := (finset.range N).image (abs ∘ a),
  let B := option.iget head.max,
  let M := max B (abs l) + 1,
  have hM : M > 0 :=
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left (le_trans (abs_nonneg _) (le_max_right _ _))),
  existsi [M, hM],
  intro n,
  refine le_of_lt _,
  cases lt_or_ge n N with h h,
  { refine lt_of_le_of_lt (le_trans _ (le_max_left _ _)) (lt_add_one _),
    have h₁ : head.nonempty := begin
      refine finset.nonempty.image _ (abs ∘ a),
      existsi 0,
      rw finset.mem_range,
      exact lt_of_le_of_lt (zero_le n) h,
    end,
    dsimp [B],
    cases finset.max_of_nonempty h₁ with b hb,
    rw option.iget_of_mem hb,
    refine finset.le_max_of_mem _ hb,
    refine finset.mem_image_of_mem (abs ∘ a) _,
    rw finset.mem_range,
    exact h,
  },
  { have h₁ : abs (a n) - abs l < 1 := lt_of_le_of_lt (abs_sub_abs_le_abs_sub (a n) l) (hN n h),
    rw sub_lt_iff_lt_add' at h₁,
    calc
      abs (a n) < abs l + 1 : h₁
        ... ≤ max B (abs l) + 1 : add_le_add_right' (le_max_right _ _),
  }
end

lemma bdd_above_of_converges {a : seq} : seq_converges a → seq_bdd_above a :=
  seq_bdd_above_of_bdd ∘ bdd_of_converges

lemma bdd_below_of_converges {a : seq} : seq_converges a → seq_bdd_below a :=
  seq_bdd_below_of_bdd ∘ bdd_of_converges

-- Theorem 3.11 (Algebra of limits)
section algebra_of_limits

theorem lim_add_eq_add_lim {a b : seq} {la lb : ℝ} (hla : a ⟶ la) (hlb : b ⟶ lb) :
  a + b ⟶ la + lb :=
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

theorem lim_mul_eq_mul_lim {a b : seq} {la lb : ℝ} (hla : a ⟶ la) (hlb : b ⟶ lb) :
  a * b ⟶ la * lb :=
begin
  intros ε hε,
  rcases bdd_of_converges (seq_converges_of_has_limit hla) with ⟨A, ⟨hA₁, hA₂⟩⟩,
  have h₁ : 2 * (abs lb + 1) > 0 :=
    mul_pos' zero_lt_two (lt_of_le_of_lt (abs_nonneg lb) (lt_add_one (abs lb))),
  cases hla (ε / (2 * (abs lb + 1))) (div_pos hε h₁) with Na hNa,
  cases hlb (ε / (2 * A)) (div_pos hε (mul_pos' zero_lt_two hA₁)) with Nb hNb,
  let N := max Na Nb,
  existsi N,
  intros n Hn,
  replace hNa := hNa n (le_trans (le_max_left Na Nb) Hn),
  replace hNb := hNb n (le_trans (le_max_right Na Nb) Hn),
  replace hA₂ := hA₂ n,
  have h₂ : abs (a n - la) * abs lb < ε / 2 := calc
      abs (a n - la) * abs lb ≤ (ε / (2 * (abs lb + 1))) * abs lb : mul_le_mul_of_nonneg_right (le_of_lt hNa) (abs_nonneg lb)
        ... = ε * abs lb / (2 * (abs lb + 1)) : by field_simp
        ... < ε / 2 : by {
          rw [div_lt_iff' h₁, mul_right_comm, mul_div_cancel'],
          show (2 : ℝ) ≠ 0, by { norm_cast, norm_num },
          exact mul_lt_mul_of_pos_left (lt_add_one _) hε,
        },
  have h₃ : abs (a n) * abs (b n - lb) ≤ ε / 2 := calc
      abs (a n) * abs (b n - lb) ≤ A * (ε / (2 * A)) : mul_le_mul hA₂ (le_of_lt hNb) (abs_nonneg (b n - lb)) (le_of_lt hA₁)
        ... = ε / 2 : by {
          field_simp [ne_of_gt hA₁],
          rw [mul_comm A ε, mul_comm 2 A, mul_assoc],
        },
  calc
    abs (a n * b n - la * lb) = abs ((a n - la) * lb + a n * (b n - lb)) : by ring
      ... ≤ abs ((a n - la) * lb) + abs (a n * (b n - lb)) : abs_add ((a n - la) * lb) (a n * (b n - lb))
      ... = abs (a n - la) * abs lb + abs (a n) * abs (b n - lb) : by rw [abs_mul, abs_mul]
      ... < ε / 2 + ε / 2 : add_lt_add_of_lt_of_le h₂ h₃
      ... = ε : add_halves ε,
end

theorem lim_div_eq_div_lim {a b : seq} {la lb : ℝ} (hla : a ⟶ la) (hlb : b ⟶ lb) (hlb_ne_zero : lb ≠ 0) :
  a / b ⟶ la / lb :=
begin
  have hla' : 4 * abs la + 1 > 0 := lt_of_le_of_lt (mul_nonneg (le_of_lt four_pos) (abs_nonneg la)) (lt_add_one (4 * abs la)),
  have hlb' : abs lb > 0 := abs_pos_of_ne_zero hlb_ne_zero,
  intros ε hε,
  cases hlb (abs lb / 2) (div_pos hlb' zero_lt_two) with N₁ hN₁,
  cases hla (ε * abs lb / 4) _ with N₂ hN₂,
  cases hlb (ε * (abs lb) ^ 2 / (4 * abs la + 1)) _ with N₃ hN₃,
  show ε * abs lb / 4 > 0, from div_pos (mul_pos hε hlb') four_pos,
  show ε * abs lb ^ 2 / (4 * abs la + 1) > 0, from div_pos (mul_pos hε (pow_pos hlb' 2)) hla',
  let N := max N₁ (max N₂ N₃),
  existsi N,
  intros n hn,
  replace hN₁ : abs (b n) > abs lb / 2 := begin
    have : abs lb - abs (b n) < abs lb / 2 := calc
      abs lb - abs (b n) ≤ abs (lb - b n) : abs_sub_abs_le_abs_sub lb (b n)
        ... = abs (b n - lb) : by rw abs_sub
        ... < abs lb / 2 : hN₁ n (le_trans (le_max_left _ _) hn),
    rwa [sub_lt_iff_lt_add, ←sub_lt_iff_lt_add', sub_half] at this,
  end,
  replace hN₂ := hN₂ n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn),
  replace hN₃ := hN₃ n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn),
  have hbn : b n ≠ 0 := abs_pos_iff.mp (lt_trans (half_pos hlb') hN₁),
  have h_main : abs ((a n - la) * lb + la * (lb - b n)) < ε * abs lb * abs lb / 2 := calc
    abs ((a n - la) * lb + la * (lb - b n)) ≤ abs ((a n - la) * lb) + abs (la * (lb - b n)) : abs_add _ _
      ... = abs (a n - la) * abs lb + abs la * abs (b n - lb) : by rw [abs_mul, abs_mul, abs_sub lb (b n)]
      ... < (ε * abs lb / 4) * abs lb + abs la * ε * abs lb ^ 2 / (4 * abs la + 1) : by {
        refine add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_right hN₂ hlb') _,
        have : abs la * ε * abs lb ^ 2 / (4 * abs la + 1) = abs la * (ε * abs lb ^ 2 / (4 * abs la + 1)) := by ring,
        rw this,
        exact mul_le_mul_of_nonneg_left (le_of_lt hN₃) (abs_nonneg la),
      }
      ... = ε * abs lb * abs lb * (1 / 4 + abs la / (4 * abs la + 1)) : by { rw pow_two, ring }
      ... < (ε * abs lb * abs lb) * (1 / 2) : by {
        refine mul_lt_mul_of_pos_left _ (mul_pos (mul_pos hε hlb') hlb'),
        have : (1 / 2 : ℝ) = 1 / 4 + 1 / 4 := by norm_num,
        rw [this, add_lt_add_iff_left, div_lt_iff' hla', ←div_eq_mul_one_div, lt_div_iff' four_pos],
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
        refine mul_le_mul_of_nonneg_left (le_of_lt _) (div_nonneg (abs_nonneg _) hlb'),
        rw [div_lt_div_iff (abs_pos_of_ne_zero hbn) hlb', one_mul],
        rwa [gt_iff_lt, div_lt_iff' two_pos] at hN₁,
      }
      ... = abs (a n * lb - b n * la) * (2 / (abs lb * abs lb)) : by field_simp
      ... = abs ((a n - la) * lb + la * (lb - b n)) * (2 / (abs lb * abs lb)) : congr_arg (λ x, abs x * (2 / (abs lb * abs lb))) (by ring)
      ... < (ε * abs lb * abs lb / 2) * (2 / (abs lb * abs lb)) : mul_lt_mul_of_pos_right h_main (div_pos two_pos (mul_pos hlb' hlb'))
      ... = ε : by { field_simp [ne_of_gt hlb'], ring },
end

theorem lim_smul_eq_mul_lim {a : seq} {la : ℝ} (c : ℝ) (hla : a ⟶ la) : c • a ⟶ c * la :=
  lim_mul_eq_mul_lim lim_of_const_seq hla

theorem lim_neg_eq_neg_lim {a : seq} {la : ℝ} (hla : a ⟶ la) : -a ⟶ -la := begin
  convert lim_smul_eq_mul_lim (-1) hla,
  all_goals { exact neg_eq_neg_one_mul _ },
end

theorem lim_sub_eq_sub_lim {a b : seq} {la lb : ℝ} (hla : a ⟶ la) (hlb : b ⟶ lb) :
  a - b ⟶ la - lb := lim_add_eq_add_lim hla (lim_neg_eq_neg_lim hlb)

theorem lim_abs_eq_abs_lim {a : seq} {la : ℝ} (hla : a ⟶ la) : abs ∘ a ⟶ abs la := begin
  intros ε hε,
  cases hla ε hε with N hN,
  existsi N,
  intros n hn,
  exact lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub (a n) la) (hN n hn),
end

theorem lim_pow_eq_pow_lim {a : seq} {la : ℝ} {n : ℕ} (hla : a ⟶ la) : ((^ n) ∘ a) ⟶ (la ^ n) :=
  nat.rec lim_of_one (λ n, lim_mul_eq_mul_lim hla) n

end algebra_of_limits

lemma seq_converges_iff_add_converges {a : seq} {c : ℝ} : seq_converges (a + (const_seq c)) ↔ seq_converges a := begin
  split,
  { rintro ⟨l, hl⟩,
    rw [←add_zero a, ←sub_self (const_seq c), add_sub],
    existsi l - c,
    exact lim_sub_eq_sub_lim hl lim_of_const_seq,
  },
  { rintro ⟨l, hl⟩,
    existsi l + c,
    exact lim_add_eq_add_lim hl lim_of_const_seq,
  }
end

lemma seq_converges_iff_smul_converges {a : seq} {c : ℝ} (hc : c ≠ 0) : seq_converges (c • a) ↔ seq_converges a := begin
  split,
  { rintro ⟨l, hl⟩,
    rw [←one_smul ℝ a, ←one_div_mul_cancel hc, mul_smul],
    existsi (1 / c) * l,
    exact lim_smul_eq_mul_lim (1 / c) hl,
  },
  { rintro ⟨l, hl⟩,
    existsi c * l,
    exact lim_smul_eq_mul_lim c hl,
  }
end

section specific_limits

lemma lim_of_neg_pow {k : ℕ} : (λ n, (1 : ℝ) / ((n + 1) ^ (k + 1))) ⟶ 0 := begin
  conv {
    congr,
    { funext,
      rw [pow_succ, ←one_div_mul_one_div, ←one_div_pow k],
    },
    { rw ←zero_mul (0 ^ k : ℝ) }
  },
  exact lim_mul_eq_mul_lim lim_of_reciprocal (lim_pow_eq_pow_lim lim_of_reciprocal),
end

end specific_limits

lemma lim_eq_lim_of_tail {a : seq} {la : ℝ} (k : ℕ) : (a ⟶ la) ↔ (a ∘ (+ k) ⟶ la) := begin
  split,
  { intros hla ε hε,
    cases hla ε hε with N hN,
    existsi N,
    intros n hn,
    exact hN (n + k) (le_add_right hn),
  },
  { intros hla ε hε,
    cases hla ε hε with N hN,
    existsi N + k,
    intros n hn,
    cases nat.le.dest hn with m hm,
    rw add_right_comm at hm,
    have := hN (N + m) (nat.le_add_right N m),
    change abs (a (N + m + k) - la) < ε at this,
    rwa hm at this,
  },
end

lemma seq_converges_iff_tail_converges {a : seq} (k : ℕ) : seq_converges a ↔ seq_converges (a ∘ (+ k)) :=
  exists_congr (λ l, lim_eq_lim_of_tail k)

lemma lim_abs_eq_zero_iff {a : seq} : (abs ∘ a ⟶ 0) ↔ (a ⟶ 0) := begin
  refine forall_congr (λ ε, _),
  refine imp_congr iff.rfl _,
  refine exists_congr (λ N, _),
  refine forall_congr (λ n, _),
  refine imp_congr iff.rfl _,
  rw [sub_zero, sub_zero, abs_abs],
end

-- Remark 3.12
example : (λ n, ((n + 1) ^ 2 + 5) / ((n + 1) ^ 3 - (n + 1) + 6)) ⟶ 0 := begin
  have hsimp₁ :
    (λ (n : ℕ), (((n : ℝ) + 1) ^ 2 + 5) / ((n + 1) ^ 3 - (n + 1) + 6))
      = (λ (n : ℕ), ((1 : ℝ) / (n + 1) + 5 * (1 / (n + 1) ^ 3)) / (1 - (1 / (n + 1) ^ 2) + 6 * (1 / (n + 1) ^ 3))) :=
  begin
    funext,
    have hn : (n : ℝ) + 1 ≠ 0 := by { norm_cast, norm_num },
    conv_rhs { rw ←mul_div_mul_right _ sorry (pow_ne_zero 3 hn), },
    refine congr (congr_arg has_div.div _) _,
    all_goals { field_simp [hn], ring }
  end,
  have hsimp₂ : (0 : ℝ) = (0 + 5 * 0) / (1 - 0 + 6 * 0) := by norm_num,
  conv {
    congr,
    { rw hsimp₁ },
    { rw hsimp₂ }
  },
  exact
    lim_div_eq_div_lim 
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
          lim_of_neg_pow))
      (by norm_num),
end

-- Theorem 3.13 (Monotone convergence theorem)
theorem lim_of_bdd_increasing_seq {a : seq} (ha : seq_increasing a) (ha' : seq_bdd_above a) :
  a ⟶ real.Sup a :=
begin
  let l := real.Sup a,
  intros ε hε,
  have h₁ : is_lub ↑a l := begin 
    cases ha' with b hb,
    exact real.is_lub_Sup (set.mem_range_self 0) hb,
  end,
  have h₂ : l - ε < l := sub_lt_self l hε,
  rcases (lt_is_lub_iff h₁).mp h₂ with ⟨x, ⟨⟨N, hx⟩, haN⟩⟩,
  clear h₁ h₂,
  subst hx,
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

theorem lim_of_bdd_decreaing_seq {a : seq} (ha : seq_decreasing a) (ha' : seq_bdd_below a) :
  a ⟶ real.Inf a :=
begin
  let b : seq := -a,
  rw ←neg_neg a,
  change is_limit (-b) (real.Inf (set.range ((λ x, -x) ∘ b))),
  rw set.range_comp,
  refine lim_neg_eq_neg_lim _,
  simp only [neg_inj', set.mem_range, set.mem_image, exists_eq_right],
  refine lim_of_bdd_increasing_seq ha _,
  cases ha' with x hx,
  existsi -x,
  rintros y ⟨n, hn⟩,
  subst hn,
  erw neg_le_neg_iff,
  exact hx (set.mem_range_self n),
end

theorem seq_converges_of_bdd_increasing {a : seq} (ha : seq_increasing a) (ha' : seq_bdd_above a) :
  seq_converges a := seq_converges_of_has_limit (lim_of_bdd_increasing_seq ha ha')

theorem seq_converges_of_bdd_decreasing {a : seq} (ha : seq_decreasing a) (ha' : seq_bdd_below a) :
  seq_converges a := seq_converges_of_has_limit (lim_of_bdd_decreaing_seq ha ha')

-- Example 3.14 (Order limit theorem)
lemma lim_of_nonneg_nonneg {a : seq} {la : ℝ} (ha : 0 ≤ a) (hla : a ⟶ la) : 0 ≤ la := begin
  by_contradiction h,
  rw [not_le, ←neg_pos] at h,
  cases hla (-la) h with N hN,
  have := lt_of_le_of_lt (le_abs_self _) (hN N (le_refl N)),
  erw add_lt_iff_neg_right at this,
  exact not_le_of_lt this (ha N),
end

theorem lim_le_of_seq_le {a b : seq} {la lb : ℝ} (hab : a ≤ b) (hla : a ⟶ la) (hlb : b ⟶ lb) :
  la ≤ lb :=
begin
  by_contradiction h,
  rw [not_le, ←sub_pos] at h,
  cases lim_sub_eq_sub_lim hla hlb (la - lb) h with N hN,
  have := lt_of_le_of_lt (neg_le_abs_self _) (hN N (le_refl N)),
  erw [←sub_pos, sub_neg_eq_add, add_eq_of_eq_sub' rfl, sub_pos] at this,
  exact lt_irrefl _ (lt_of_lt_of_le this (hab N)),
end

theorem lim_sqrt_eq_sqrt_lim {a : seq} {la : ℝ} (ha : a ≥ 0) (hla : a ⟶ la) :
  real.sqrt ∘ a ⟶ real.sqrt la :=
begin
  have hla_nonneg : la ≥ 0 := lim_le_of_seq_le ha lim_of_zero hla,
  cases lt_or_eq_of_le hla_nonneg with h h,
  { intros ε hε,
    cases hla (ε * (real.sqrt la)) (mul_pos hε (real.sqrt_pos.mpr h)) with N hN,
    existsi N,
    intros n hn,
    replace hN := hN n hn,
    have h : real.sqrt (a n) + real.sqrt la ≥ 0 := add_nonneg (real.sqrt_nonneg (a n)) (real.sqrt_nonneg la),
    refine lt_of_mul_lt_mul_right _ h,
    rw [←abs_of_nonneg h, ←abs_mul],
    calc
      abs ((real.sqrt (a n) - real.sqrt la) * (real.sqrt (a n) + real.sqrt la)) = abs ((real.sqrt (a n)) ^ 2 - (real.sqrt la) ^ 2) : congr_arg abs (by ring)
        ... = abs (a n - la) : by rw [real.sqr_sqrt (ha n), real.sqr_sqrt hla_nonneg]
        ... < ε * real.sqrt la : hN
        ... ≤ ε * (real.sqrt (a n) + real.sqrt la) : by {
          refine mul_le_mul_of_nonneg_left _ (le_of_lt hε),
          exact le_add_of_nonneg_left (real.sqrt_nonneg (a n)),
        }
        ... = ε * abs (real.sqrt (a n) + real.sqrt la) : by rw abs_of_nonneg h,
  },
  { intros ε hε,
    cases hla (ε ^ 2) (pow_pos hε 2) with N hN,
    existsi N,
    intros n hn,
    replace hN := hN n hn,
    rw [←h, sub_zero, abs_of_nonneg (ha n)] at hN,
    rw [←h, real.sqrt_zero, sub_zero, abs_of_nonneg (real.sqrt_nonneg (a n)), ←real.sqrt_sqr (le_of_lt hε)],
    rwa real.sqrt_lt (ha n) (le_of_lt (pow_pos hε 2)),
  }
end

-- Problem Sheet 4: Question 3 (Squeeze Theorem)
theorem squeeze_theorem {a b c : seq} {l : ℝ} (hla : a ⟶ l) (hlc : c ⟶ l) (hab : a ≤ b) (hbc : b ≤ c) :
  b ⟶ l :=
begin
  intros ε hε,
  cases hla (ε / 2) (half_pos hε) with Na hNa,
  cases hlc (ε / 2) (half_pos hε) with Nc hNc,
  let N := max Na Nc,
  existsi N,
  intros n hn,
  replace hNa := hNa n (le_trans (le_max_left _ _) hn),
  replace hNc := hNc n (le_trans (le_max_right _ _) hn),
  have h₁ : abs (b n - l) ≤ (b n - a n) + abs (a n - l) := calc
    abs (b n - l) ≤ abs (b n - a n) + abs (a n - l) : abs_sub_le (b n) (a n) l
      ... = (b n - a n) + abs (a n - l) : by { rw abs_of_nonneg, rw [ge_iff_le, sub_nonneg], exact hab n },
  have h₂ : abs (b n - l) ≤ (c n - b n) + abs (c n - l) := calc
    abs (b n - l) ≤ abs (b n - c n) + abs (c n - l) : abs_sub_le (b n) (c n) l
      ... = abs (c n - b n) + abs (c n - l) : by rw abs_sub
      ... = (c n - b n) + abs (c n - l) : by { rw abs_of_nonneg, rw [ge_iff_le, sub_nonneg], exact hbc n },
  have h₃ : 2 * abs (b n - l) ≤ 2 * (abs (a n - l) + abs (c n - l)) := calc
    2 * abs (b n - l) = abs (b n - l) + abs (b n - l) : two_mul _
      ... ≤ ((b n - a n) + abs (a n - l)) + ((c n - b n) + abs (c n - l)) : add_le_add h₁ h₂
      ... = (c n - l) + (l - a n) + abs (a n - l) + abs (c n - l) : by ring
      ... ≤ abs (c n - l) + abs (l - a n) + abs (a n - l) + abs (c n - l) : by {
          repeat { refine add_le_add_right' _ },
          exact add_le_add (le_abs_self _) (le_abs_self _),
        }
      ... = abs (c n - l) + abs (a n - l) + abs (a n - l) + abs (c n - l) : by rw abs_sub (a n) l
      ... = 2 * (abs (a n - l) + abs (c n - l)) : by ring,
  rw mul_le_mul_left zero_lt_two at h₃,
  calc
    abs (b n - l) ≤ abs (a n - l) + abs (c n - l) : h₃
      ... < ε / 2 + ε / 2 : add_lt_add hNa hNc
      ... = ε : add_halves ε,
end

-- Problem Sheet 5: Question 1 (Bernoulli Inequality)
lemma bernoulli_inequality {n : ℕ} {x : ℝ} (hx : x > -1) : (1 + x) ^ n ≥ 1 + n * x := begin
  induction n with n hn,
  { rw [pow_zero, nat.cast_zero, zero_mul, add_zero],
    exact le_refl 1,
  },
  { have hx' : 1 + x > 0 := by rwa [gt_iff_lt, ←sub_pos, sub_neg_eq_add, add_comm] at hx,
    calc
    (1 + x) ^ (n + 1) = (1 + x) * (1 + x) ^ n : pow_succ (1 + x) n
      ... ≥ (1 + x) * (1 + n * x) : by rwa [ge_iff_le, mul_le_mul_left hx'] 
      ... = 1 + (n + 1) * x + n * (x ^ 2) : by ring
      ... ≥ 1 + (n + 1) * x : le_add_of_nonneg_right (mul_nonneg (nat.cast_nonneg n) (pow_two_nonneg x)),
  }
end

section specific_limits

lemma lim_of_geom_zero_aux {x : ℝ} (hx : x > 0) : (λ n, 1 / (1 + x) ^ n) ⟶ 0 := begin
  intros ε hε,
  cases exists_nat_gt (1 / (ε * x)) with N hN,
  existsi N,
  intros n hn,
  have hx' : (1 + x) ^ n > 0 := pow_pos (add_pos zero_lt_one hx) n,
  rw [sub_zero, abs_of_pos (one_div_pos_of_pos hx'), div_lt_iff'' hx' hε],
  calc
    1 / ε < N * x : by { rw ←div_lt_iff hx, rw div_div_eq_div_mul, exact hN }
      ... < 1 + N * x : lt_one_add (N * x)
      ... ≤ 1 + n * x : by { refine add_le_add_left _ 1, rw mul_le_mul_right hx, exact nat.cast_le.mpr hn }
      ... ≤ (1 + x) ^ n : bernoulli_inequality (lt_trans zero_gt_neg_one hx),
end

lemma lim_of_geom_zero {r : ℝ} (hr : r ∈ set.Ioo (0 : ℝ) (1 : ℝ)) : (λ n, r ^ n) ⟶ 0 := begin
  let x := 1 / r - 1,
  cases hr with hr_pos hr_lt_one,
  have hx_pos : 0 < x := begin
    dsimp only [x],
    rw sub_pos,
    exact one_lt_one_div hr_pos hr_lt_one,
  end,
  convert lim_of_geom_zero_aux hx_pos,
  funext,
  have : r = 1 / (1 + x) := by { dsimp only [x], field_simp },
  rw this,
  exact one_div_pow n,
end

lemma lim_of_geom_zero' {r : ℝ} (hr : r ∈ set.Ioo (-1 : ℝ) (1 : ℝ)) : (λ n, r ^ n) ⟶ 0 := begin
  cases decidable.em (r = 0) with h h,
  { rw lim_eq_lim_of_tail 1,
    subst h,
    convert lim_of_zero,
    funext,
    change 0 ^ (x + 1) = (0 : seq) x,
    rw zero_pow (nat.succ_pos x),
    refl,
  },
  { replace h := abs_pos_of_ne_zero h,
    rw [set.mem_Ioo, ←abs_lt] at hr,
    rw ←lim_abs_eq_zero_iff,
    dsimp only [function.comp],
    have hr' : abs r ∈ set.Ioo (0 : ℝ) (1 : ℝ) := ⟨h, hr⟩,
    convert lim_of_geom_zero hr',
    funext n,
    exact (pow_abs r n).symm,
  }
end

lemma lim_of_geom_inf {r : ℝ} (hr : r ∈ set.Ioi (1 : ℝ)) : (λ n, r ^ n) ⟶+∞ := begin
  let x := r - 1,
  rw set.mem_Ioi at hr,
  have hx : r = 1 + x := by { dsimp only [x], exact (add_eq_of_eq_sub' rfl).symm, },
  have hx' : x > 0 := sub_pos_of_lt hr,
  intro M,
  cases exists_nat_gt (M / x) with N hN,
  existsi N,
  intros n hn,
  refine le_of_lt _,
  calc
    r ^ n = (1 + x) ^ n : congr_fun (congr_arg pow hx) n
      ... ≥ 1 + n * x : bernoulli_inequality (lt_trans zero_gt_neg_one hx')
      ... > n * x : lt_one_add (n * x)
      ... ≥ N * x : by { rw [ge_iff_le, mul_le_mul_right hx'], exact nat.cast_le.mpr hn }
      ... > M : (div_lt_iff hx').mp hN,
end

end specific_limits

-- Example 3.15
example {a : seq} {L : ℝ} (ha : ∀ n, a n ≠ 0) (hL_lt_one : L < 1) (hL : (λ n, abs (a (n + 1) / a n)) ⟶ L) :
  a ⟶ 0 :=
begin
  have hL_bd : L ∈ set.Ico (0 : ℝ) (1 : ℝ) := begin
    refine ⟨lim_le_of_seq_le _ lim_of_const_seq hL, hL_lt_one⟩,
    intro n,
    exact abs_nonneg _,
  end,
  clear hL_lt_one,
  intros ε hε,
  cases hL ((1 - L) / 2) _ with N hN,
  show (1 - L) / 2 > 0, from half_pos (sub_pos.mpr hL_bd.2),
  set L' := (1 + L) / 2,
  have hL'_bd : L' ∈ set.Ioo (0 : ℝ) (1 : ℝ) := begin
    dsimp only [L'],
    split,
    { exact half_pos (lt_of_le_of_lt hL_bd.1 (lt_one_add L)) },
    { rw [div_lt_iff two_pos, one_mul, ←lt_sub_iff_add_lt'],
      norm_num,
      exact hL_bd.2,
    },
  end,
  have hL' : ∀ k, abs (a (N + k)) ≤ L' ^ k * abs (a N) := begin
    intro k,
    induction k with k hk,
    { rw [add_zero, pow_zero, one_mul] },
    { calc
        abs (a (N + k + 1)) ≤ L' * abs (a (N + k)) : by {
            rw [←div_le_iff (abs_pos_of_ne_zero (ha (N + k))), ←abs_div],
            refine le_of_lt _,
            have : L' = (1 - L) / 2 + L := by { dsimp only [L'], ring, },
            rw [this, ←sub_lt_iff_lt_add],
            exact lt_of_le_of_lt (le_abs_self _) (hN (N + k) (nat.le_add_right N k)),
          }
          ... ≤ L' * (L' ^ k * abs (a N)) : by rwa mul_le_mul_left hL'_bd.1
          ... = L' ^ (k + 1) * abs (a N) : by rw [←mul_assoc, ←pow_succ],
    }
  end,
  cases lim_of_geom_zero hL'_bd (ε / abs (a N)) _ with M hM,
  show ε / abs (a N) > 0, from div_pos hε (abs_pos_of_ne_zero (ha N)),
  existsi N + M,
  intros n hn,
  cases nat.le.dest hn with k hk,
  rw sub_zero,
  subst hk,
  replace hM := hM M (le_refl M),
  simp only [add_zero, sub_eq_add_neg, neg_zero] at hM,
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

lemma cauchy_iff {a : seq} : seq_cauchy a ↔ ∀ ε > 0, ∃ N, ∀ (m ≥ N) (n ≥ m), abs (a n - a m) < ε :=
begin
  refine forall_congr (λ ε, _),
  refine imp_congr iff.rfl _,
  refine exists_congr (λ N, _),
  split,
  { intros h m hm n hn,
    exact h m hm n (le_trans hm hn),
  },
  { intros h m hm n hn,
    cases le_or_gt m n with hmn hmn,
    { exact h m hm n hmn },
    { rw abs_sub,
      exact h n hn m (le_of_lt hmn), 
    }
  }
end

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

lemma bdd_above_of_cauchy {a : seq} : seq_cauchy a → seq_bdd_above a := seq_bdd_above_of_bdd ∘ bdd_of_cauchy

lemma bdd_below_of_cauchy {a : seq} : seq_cauchy a → seq_bdd_below a := seq_bdd_below_of_bdd ∘ bdd_of_cauchy

-- Some lemmas for Theorem 3.19
lemma bdd_above_of_tail {a : seq} (k : ℕ) (ha : seq_bdd_above a) : seq_bdd_above (a ∘ (+ k)) := 
  bdd_above.mono (set.range_comp_subset_range (+ k) a) ha

lemma bdd_below_of_tail {a : seq} (k : ℕ) (ha : seq_bdd_below a) : seq_bdd_below (a ∘ (+ k)) := 
  bdd_below.mono (set.range_comp_subset_range (+ k) a) ha

lemma bdd_above_iff_tail_bdd_above {a : seq} (k : ℕ) : seq_bdd_above a ↔ seq_bdd_above (a ∘ (+ k)) := begin
  split,
  { intro ha,
    exact bdd_above.mono (set.range_comp_subset_range (+ k) a) ha,
  },
  { rintro ⟨B, hB⟩,
    let head : finset ℝ := (finset.range (k + 1)).image a,
    have head_has_mem : a 0 ∈ head := by simp only [nat.succ_pos', finset.mem_image_of_mem, finset.mem_range],
    cases finset.max_of_mem head_has_mem with B' hB',
    let M := max B B',
    existsi M,
    intros x hx,
    cases hx with n hn,
    subst hn,
    cases le_or_gt n k with h h,
    { refine le_trans (finset.le_max_of_mem _ hB') (le_max_right B B'),
      refine finset.mem_image_of_mem a _,
      rw finset.mem_range,
      exact nat.lt_succ_of_le h,
    },
    { refine le_trans (hB _) (le_max_left B B'),
      cases nat.exists_eq_add_of_lt h with x hx,
      subst hx,
      rw [add_assoc, add_comm],
      exact set.mem_range_self (x + 1),
    }
  }
end

lemma Inf_decreasing_eq_Inf_tail {a : seq} (n : ℕ) (ha_decr : seq_decreasing a) (ha_bdd : seq_bdd_below a) :
  real.Inf a = real.Inf (set.range (a ∘ (+ n))) :=
begin
  refine le_antisymm _ _,
  { exact Inf_le_Inf_subset (set.range_comp_subset_range (+ n) a) ha_bdd (set.range_nonempty (a ∘ (+ n))) },
  { refine real.lb_le_Inf (set.range a) _ _,
    { exact set.range_nonempty a },
    { rintros x ⟨k, hk⟩,
      subst hk,
      cases le_or_gt n k with h h,
      { refine real.Inf_le (set.range (a ∘ (+ n))) (bdd_below_of_tail n ha_bdd) _,
        rw set.range_comp,
        refine set.mem_image_of_mem a _,
        rw set.mem_range,
        simp only [add_comm, nat.le.dest h],
      },
      { replace h := ha_decr (le_of_lt h),
        erw neg_le_neg_iff at h,
        refine le_trans (real.Inf_le (set.range (a ∘ (+ n))) (bdd_below_of_tail n ha_bdd) _) h,
        rw set.range_comp,
        refine set.mem_image_of_mem a _,
        existsi 0,
        exact zero_add n,
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
    refine Sup_subset_le_Sup _ (bdd_above_of_tail m ha_bdd_above) (set.range_nonempty (a ∘ (+ n))),
    rw [set.range_comp, set.range_comp],
    refine set.image_subset a (range_add_subset_range_add hmn),
  end,
  have hb_bdd_below : seq_bdd_below b := begin
    cases bdd_below_of_cauchy ha with A hA,
    existsi A,
    rintros x ⟨k, hk⟩,
    subst hk,
    dsimp only [b],
    refine le_trans (hA (set.mem_range_self k)) _,
    refine real.le_Sup _ (bdd_above_of_tail k ha_bdd_above) _,
    rw set.range_comp,
    refine set.mem_image_of_mem a _,
    existsi 0,
    exact zero_add k,
  end,
  have hb := lim_of_bdd_decreaing_seq hb_decr hb_bdd_below,
  let lb := real.Inf b,
  existsi lb,
  intros ε hε,
  cases ha (ε / 2) (half_pos hε) with N hN,
  existsi N,
  intros n hn,
  refine lt_of_le_of_lt _ (half_lt_self hε),
  rw abs_le,
  split,
  { rw neg_le_sub_iff_le_add,
    dsimp only [lb],
    refine le_trans (real.Inf_le b hb_bdd_below (set.mem_range_self N)) _,
    dsimp only [b],
    refine real.Sup_le_ub (set.range (a ∘ (+ N))) _ _,
    show (set.range (a ∘ (+ N))).nonempty, from set.range_nonempty (a ∘ (+ N)),
    rintros x ⟨k, hk⟩,
    subst hk,
    refine le_of_lt _,
    have := (abs_lt.mp (hN n hn (k + N) (nat.le_add_left N k))).right,
    rwa sub_lt_iff_lt_add' at this,
  },
  { rw sub_le,
    have : lb = real.Inf (set.range (b ∘ (+ N))) := Inf_decreasing_eq_Inf_tail N hb_decr hb_bdd_below,
    rw this,
    refine (real.le_Inf (set.range (b ∘ (+ N))) _ _).mpr _,
    show (set.range (b ∘ (+ N))).nonempty, from set.range_nonempty (b ∘ (+ N)),
    show seq_bdd_below (b ∘ (+ N)), from bdd_below_of_tail N hb_bdd_below,
    rintros x ⟨k, hk⟩,
    dsimp at hk,
    subst hk,
    dsimp only [b],
    refine le_trans (le_of_lt _) _,
    show a n - ε / 2 < a (k + N), from sub_lt.mpr (abs_lt.mp (hN (k + N) (nat.le_add_left N k) n hn)).right,
    refine real.le_Sup (set.range (a ∘ (+ (k + N)))) (bdd_above_of_tail (k + N) ha_bdd_above) _,
    rw set.range_comp,
    refine set.mem_image_of_mem a _,
    existsi 0,
    exact zero_add (k + N),
  }
end

-- Corollary 3.20
theorem converges_iff_cauchy {a : seq} : seq_converges a ↔ seq_cauchy a := ⟨cauchy_of_converges, converges_of_cauchy⟩

-- Exercise 3.22
example (M : ℝ) (S : set ℝ) (hS : S.nonempty) (hM : ∀ x ∈ S, x < M) : real.Sup S ≤ M := begin
  refine real.Sup_le_ub S hS _,
  intros x hx,
  exact le_of_lt (hM x hx),
end

end sec_3_2

-- Section 3.3 : Subsequences
section sec_3_3

-- Exercise 3.24
lemma nat.ge_index_of_strict_mono {n : ℕ → ℕ} (hn : strict_mono n) : ∀ i, n i ≥ i := begin
  intro i,
  induction i with i hi,
  { exact nat.zero_le (n 0) },
  { exact nat.succ_le_of_lt (lt_of_le_of_lt hi (hn (nat.lt_succ_self i))) }
end

-- Theorem 3.26 (Bolzano-Weierstrass theorem)
section thm_3_26

parameter (a : seq)

def is_peak_point : ℕ → Prop := λ j, ∀ k > j, a k < a j

lemma not_peak_point (j : ℕ) : ¬is_peak_point j ↔ ∃ k > j, a k ≥ a j := begin
  unfold is_peak_point,
  push_neg,
  simp only [exists_prop, gt_iff_lt, ge_iff_le, iff_self],
end

theorem exists_convergent_subseq_of_bdd (ha : seq_bdd a) :
  ∃ (b : seq) (hb : is_subseq_of a b), seq_converges b :=
begin
  let peak_points : set ℕ := is_peak_point a,
  rw seq_bdd_iff at ha,
  cases classical.em (set.finite peak_points) with hfin hnfin,
  { let m := option.iget hfin.to_finset.max + 1,
    have hm : ∀ k ≥ m, ¬is_peak_point a k := begin
      intros k hk hk',
      change k ∈ peak_points at hk',
      cases h : hfin.to_finset.max with x,
      { refine finset.not_mem_empty k _,
        convert set.finite.mem_to_finset.mpr hk',
        rw finset.max_eq_none at h,
        exact h.symm,
      },
      { have : m = x + 1 := begin
          dsimp [m],
          rw h,
        end,
        rw this at hk,
        refine lt_irrefl x (lt_of_lt_of_le hk _),
        exact finset.le_max_of_mem (set.finite.mem_to_finset.mpr hk') h,
      }
    end,
    let a_aux := a ∘ (+ m),
    replace hm : ∀ k, ∃ j > k, a_aux j ≥ a_aux k := begin
      intro k,
      obtain ⟨j, hj₁, hj₂⟩ := (not_peak_point _ _).mp (hm (k + m) (nat.le_add_left m k)),
      existsi [j - m, nat.lt_sub_right_of_add_lt hj₁],
      convert hj₂,
      change a (j - m + m) = a j,
      congr,
      exact nat.sub_add_cancel (le_of_lt (lt_of_le_of_lt (nat.le_add_left m k) hj₁)),
    end,
    let n_aux : ℕ → ℕ := nat.rec 0 (λ x y, classical.some (hm y)),
    let n : ℕ → ℕ := (+ m) ∘ n_aux,
    let b := a ∘ n,
    have hn : strict_mono n := begin
      refine strict_mono.nat _,
      intro k,
      erw add_lt_add_iff_right,
      exact classical.some (classical.some_spec (hm (n_aux k))),
    end,
    have hb : seq_increasing b := begin
      refine monotone_of_monotone_nat _,
      intro k,
      exact classical.some_spec (classical.some_spec (hm (n_aux k))),
    end,
    have hb' : is_subseq_of a b := Exists.intro (psigma.mk n hn) rfl,
    existsi [b, hb'],
    exact seq_converges_of_bdd_increasing hb (bdd_above_of_subseq ha.1 hb'),
  },
  { change set.infinite peak_points at hnfin,
    rw infinite.nat at hnfin,
    let n_aux : ℕ → ℕ := nat.rec 0 (λ x y, classical.some (hnfin y)),
    let n := n_aux ∘ (+ 1),
    have hn : strict_mono n := begin
      refine strict_mono.nat _,
      intro k,
      exact classical.some (classical.some_spec (hnfin (n k))),
    end,
    let b := a ∘ n,
    have hb : seq_decreasing b := begin
      refine monotone_of_monotone_nat _,
      intro k,
      erw neg_le_neg_iff,
      refine le_of_lt _,
      dsimp [b],
      have h := classical.some_spec (classical.some_spec (hnfin (n_aux k))),
      refine h _ _,
      exact classical.some (classical.some_spec (hnfin (n k))),
    end,
    have hb' : is_subseq_of a b := Exists.intro (psigma.mk n hn) rfl,
    existsi [b, hb'],
    exact seq_converges_of_bdd_decreasing hb (bdd_below_of_subseq ha.2 hb'),
  },
end

end thm_3_26

-- Proposition 3.28
lemma lim_of_subseq {a b : seq} {l : ℝ} (h : is_subseq_of a b) (hl : a ⟶ l) : b ⟶ l := begin
  rcases h with ⟨n, hn⟩,
  subst hn,
  intros ε hε,
  cases hl ε hε with N hN,
  existsi N,
  intros k hk,
  exact hN (n.fst k) (le_trans hk (nat.ge_index_of_strict_mono n.snd k)),
end

lemma diveregs_of_distinct_limits {a b c : seq} {lb lc : ℝ} (hb : is_subseq_of a b)
  (hlb : b ⟶ lb) (hc : is_subseq_of a c) (hlc : c ⟶ lc) (hbc : lb ≠ lc) : seq_diverges a :=
begin
  rintro ⟨la, hla⟩,
  have hlb' := limit_unique hlb (lim_of_subseq hb hla),
  have hlc' := limit_unique hlc (lim_of_subseq hc hla),
  exact hbc (eq.trans hlb' (eq.symm hlc')),
end

-- Unseen Sheet 4: Question 4
lemma seq_converges_iff_even_and_odd_converge {a : seq} {la : ℝ} :
  (a ⟶ la) ↔ (a ∘ (λ n, 2 * n) ⟶ la) ∧ (a ∘ (λ n, 2 * n + 1) ⟶ la) :=
begin
  split,
  { intro ha,
    split,
    all_goals {
      intros ε hε,
      cases ha ε hε with N hN,
      existsi N,
      intros n hn,
    },
    { refine hN (2 * n) _,
      rw two_mul,
      exact le_add_right hn,
    },
    { refine hN (2 * n + 1) _,
      rw [two_mul, add_assoc],
      exact le_add_right hn,
    }
  },
  { rintros ⟨h_even, h_odd⟩,
    intros ε hε,
    cases h_even ε hε with N₁ hN₁,
    cases h_odd ε hε with N₂ hN₂,
    let N := max (2 * N₁) (2 * N₂ + 1),
    existsi N,
    intros n hn,
    cases dec_em (nat.even n) with hn_even hn_odd,
    { cases hn_even with k hk,
      subst hk,
      refine hN₁ k (le_of_mul_le_mul_left _ zero_lt_two),
      exact le_trans (le_max_left _ _) hn,
    },
    { rw nat.not_even_iff at hn_odd,
      have := calc
        n = n % 2 + 2 * (n / 2) : (nat.mod_add_div n 2).symm
          ... = 2 * (n / 2) + 1 : by rw [hn_odd, add_comm],
      rw this,
      refine hN₂ (n / 2) _,
      rw ←nat.mul_div_cancel N₂ (zero_lt_two),
      refine nat.div_le_div_right _,
      rw mul_comm,
      calc
        2 * N₂ ≤ 2 * N₂ + 1 : nat.le_succ _
          ... ≤ N : le_max_right _ _
          ... ≤ n : hn,
    }
  }
end

lemma seq_not_bdd_above_iff {a : seq} :
  ¬ seq_bdd_above a ↔ ∃ (b : seq) (hb : is_subseq_of a b), seq_diverges_to_pos_inf b :=
begin
  split,
  { intro h,
    rw seq_bdd_above_iff at h,
    push_neg at h,
    have h₁ : ∀ (A : ℝ) (n : ℕ), ∃ j > n, a j > A := begin
      intros A n,
      let head := (finset.range (n + 1)).image a,
      have h₂ : head.nonempty := begin
        refine finset.nonempty.image _ a,
        existsi 0,
        rw finset.mem_range,
        exact nat.succ_pos',
      end,
      cases finset.max_of_nonempty h₂ with B hB,
      let C := max A B,
      cases h C with j hj,
      have hj' : j > n := begin
        refine lt_of_not_ge' _,
        intro hj'',
        refine not_le_of_lt hj (le_trans _ (le_max_right _ _)),
        refine finset.le_max_of_mem (finset.mem_image_of_mem a _) hB,
        rw finset.mem_range,
        exact nat.lt_succ_of_le hj'',
      end,
      existsi [j, hj'],
      exact lt_of_le_of_lt (le_max_left _ _) hj,
    end,
    let n_aux : ℕ → ℕ := nat.rec 0 (λ (x y : ℕ), classical.some (h₁ x y)),
    let n := n_aux ∘ (+ 1),
    have hn : strict_mono n := begin
      refine strict_mono.nat _,
      intro k,
      exact classical.some (classical.some_spec (h₁ (k + 1) (n k))),
    end,
    let b := a ∘ n,
    have hb : is_subseq_of a b := Exists.intro (psigma.mk n hn) rfl,
    existsi [b, hb],
    intro M,
    let N := nat_ceil M,
    existsi N,
    intros n hn,
    refine le_of_lt (lt_of_le_of_lt (nat_ceil_le.mp hn) _),
    have hb' : ∀ k, b k > k := begin
      intro k,
      exact classical.some_spec (classical.some_spec (h₁ k (n_aux k))),
    end,
    exact hb' n,
  },
  { rintros ⟨b, ⟨⟨p, hp⟩, hb⟩⟩,
    subst hp,
    change ¬ ∃ x, ∀ y ∈ set.range a, y ≤ x,
    push_neg,
    intro x,
    cases hb (x + 1) with N hN,
    existsi a (p.fst N),
    split,
    { exact set.mem_range_self (p.fst N) },
    { exact lt_of_lt_of_le (lt_add_one x) (hN N (le_refl N)) }
  }
end

lemma seq_not_bdd_below_iff {a : seq} :
  ¬ seq_bdd_below a ↔ ∃ (b : seq) (hb : is_subseq_of a b), seq_diverges_to_neg_inf b :=
begin
  split,
  { intro h,
    rw seq_bdd_below_iff at h,
    push_neg at h,
    have h₁ : ∀ (A : ℝ) (n : ℕ), ∃ j > n, a j < A := begin
      intros A n,
      let head := (finset.range (n + 1)).image a,
      have h₂ : head.nonempty := begin
        refine finset.nonempty.image _ a,
        existsi 0,
        rw finset.mem_range,
        exact nat.succ_pos',
      end,
      cases finset.min_of_nonempty h₂ with B hB,
      let C := min A B,
      cases h C with j hj,
      have hj' : j > n := begin
        refine lt_of_not_ge' _,
        intro hj'',
        refine not_le_of_lt hj (le_trans (min_le_right _ _) _),
        refine finset.min_le_of_mem (finset.mem_image_of_mem a _) hB,
        rw finset.mem_range,
        exact nat.lt_succ_of_le hj'',
      end,
      existsi [j, hj'],
      exact lt_of_lt_of_le hj (min_le_left _ _),
    end,
    let n_aux : ℕ → ℕ := nat.rec 0 (λ (x y : ℕ), classical.some (h₁ (-x) y)),
    let n := n_aux ∘ (+ 1),
    have hn : strict_mono n := begin
      refine strict_mono.nat _,
      intro k,
      exact classical.some (classical.some_spec (h₁ (-(k + 1)) (n k))),
    end,
    let b := a ∘ n,
    have hb : is_subseq_of a b := Exists.intro (psigma.mk n hn) rfl,
    existsi [b, hb],
    intro M,
    let N := nat_ceil (-M),
    existsi N,
    intros n hn,
    rw ←neg_le_neg_iff,
    refine le_of_lt (lt_of_le_of_lt (nat_ceil_le.mp hn) _),
    rw lt_neg,
    have hb' : ∀ k, b k < -k := begin
      intro k,
      exact classical.some_spec (classical.some_spec (h₁ (-k) (n_aux k))),
    end,
    exact hb' n,
  },
  { rintros ⟨b, ⟨⟨p, hp⟩, hb⟩⟩,
    subst hp,
    change ¬ ∃ x, ∀ y ∈ set.range a, y ≥ x,
    push_neg,
    intro x,
    cases hb (x - 1) with N hN,
    existsi a (p.fst N),
    split,
    { exact set.mem_range_self (p.fst N) },
    { exact lt_of_le_of_lt (hN N (le_refl N)) (sub_one_lt x) }
  }
end

-- Problem Sheet 5: Question 5
lemma subseq_trichotomy {a : seq} :
  ∃ (b : seq) (hb : is_subseq_of a b), seq_converges b ∨ seq_diverges_to_pos_inf b ∨ seq_diverges_to_neg_inf b :=
begin
  cases classical.em (seq_bdd a) with ha ha,
  { rcases exists_convergent_subseq_of_bdd a ha with ⟨b, ⟨hb, hb'⟩⟩,
    existsi [b, hb],
    left,
    exact hb',
  },
  { rw [seq_bdd_iff, classical.not_and_distrib, seq_not_bdd_above_iff, seq_not_bdd_below_iff] at ha,
    cases ha with ha ha,
    all_goals {
      rcases ha with ⟨b, ⟨hb, hb'⟩⟩,
      existsi [b, hb],
      right,
      cc,
    },
  }
end

end sec_3_3

namespace limit_func

local attribute [instance] classical.prop_decidable

noncomputable def limit (a : seq) : option ℝ :=
  if h : seq_converges a
    then option.some (classical.some h)
    else option.none

-- Prove the equivalence of a ⟶ l and limit a = some l

lemma limit_eq {a : seq} {l : ℝ} (hl : a ⟶ l) : limit a = some l :=
  eq.trans (dif_pos ⟨l, hl⟩) (congr_arg _ (limit_unique (classical.some_spec _) hl))

lemma limit_eq' {a : seq} {l : ℝ} (hl : limit a = some l) : a ⟶ l := begin
  have h : seq_converges a := begin
    by_contradiction h',
    exact option.no_confusion (eq.trans hl.symm (dif_neg h')),
  end,
  replace hl := option.some.inj (eq.trans hl.symm (dif_pos h)),
  rw hl,
  exact classical.some_spec _,
end

lemma limit_zero : limit 0 = some 0 := limit_eq lim_of_zero

end limit_func

end real_seq