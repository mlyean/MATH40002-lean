# MATH40002 &ndash; Analysis I

Some Analysis I related stuff in Lean, currently there are only real-valued sequences and their properties.

- `src/lemmas.lean` contains lemmas related to real numbers.
- `src/seq_def.lean` contains definitions related to real sequences.
    + Bounded sequences
    + Limits and convergence
    + Monotonicity
    + Cauchy sequences
    + Subsequences
- `src/seq.lean` contains examples and propositions.
    + Uniqueness of limits
    + Algebra of limits
    + Monotone convergence theorem
    + Order limit theorem
    + Cauchy if and only if convergent
    + Bolzano-Weierstrass theorem
    + Some particular limits (`x ^ n`, `1 / n ^ k`, etc.)
- `src/series_def.lean` contains definitions related to real series.
    + Partial sums
    + Convergence of series
- `src/series.lean` contains examples and propotitions.
    + Limit test
    + Some particular series (geometric, harmonic, etc.)