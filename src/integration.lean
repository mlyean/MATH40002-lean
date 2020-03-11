import integration_def

namespace integration

-- Example 3.1
example (n : ℕ) (a b c : ℝ) (hab : a < b) (p : partition n a b) : lower_sum (λ x, c) p = c * (b - a) := begin
  sorry,
end

example (n : ℕ) (a b c : ℝ) (hab : a < b) (p : partition n a b) : upper_sum (λ x, c) p = c * (b - a) := begin
  sorry,
end

end integration