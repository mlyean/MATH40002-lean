import data.real.basic

lemma div_lt_iff'' {a b c : ℝ} (hb : b > 0) (hc : c > 0) : a / b < c ↔ a / c < b :=
  by rw [div_lt_iff hb, div_lt_iff' hc]