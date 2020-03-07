import seq

namespace continuity

section sec_5_1

def limit_eq (f : ℝ → ℝ) (a b : ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < abs (x - a) ∧ abs (x - a) < δ → abs (f x - b) < ε

end sec_5_1

section sec_5_2

def continuous_at (f : ℝ → ℝ) (a : ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - f a) < ε

def continuous (f : ℝ → ℝ) := ∀ a, continuous_at f a

end sec_5_2

end continuity
