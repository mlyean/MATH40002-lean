import data.real.basic
import data.list.basic

namespace integration

structure partition (n : ℕ) (a b : ℝ) :=
  (x : vector ℝ (n + 1))
  (hx₁ : x.head = a)
  (hx₂ : x.nth n = b)
  (mono : strict_mono x.nth)

namespace partition

variables {n : ℕ} {a b : ℝ} (p : partition n a b)

def nth (k : fin (n + 1)) : ℝ := p.x.nth k

def del (k : fin n) : ℝ := p.nth (k + 1) - p.nth k

noncomputable def m (f : ℝ → ℝ) (k : fin n) : ℝ := real.Inf (f '' set.Icc (p.nth k) (p.nth (k + 1)))

noncomputable def M (f : ℝ → ℝ) (k : fin n) : ℝ := real.Sup (f '' set.Icc (p.nth k) (p.nth (k + 1)))

end partition

section sec_3_1

noncomputable def lower_sum {n : ℕ} {a b : ℝ} (f : ℝ → ℝ) (p : partition n a b) :=
  (fintype.elems (fin n)).sum (λ (i : fin n), (p.m f i) * (p.del i))

noncomputable def upper_sum {n : ℕ} {a b : ℝ} (f : ℝ → ℝ) (p : partition n a b) :=
  (fintype.elems (fin n)).sum (λ (i : fin n), (p.M f i) * (p.del i))

end sec_3_1

end integration