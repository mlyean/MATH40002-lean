# MATH40002 &ndash; Analysis I

Some Analysis I related stuff in Lean, currently there are only real-valued sequences and their properties. Sections 3.1 and 3.2 are mostly typed up, and section 3.3 is WIP.

1. Chapter 3 &ndash; Sequences
- `src/seq_def.lean` contains definitions related to real sequences, including
    + Bounded sequences
    + Limits and convergence
    + Monotonicity
    + Cauchy sequences
    + Subsequences
- `src/seq.lean` contains examples and propositions as in the lecture notes. Among the proven theorems are
    + Uniqueness of limits
    + Algebra of limits
    + Monotone convergence theorem
    + Order limit theorem
    + Cauchy if and only if convergent
    + Some particular limits (`x ^ n`, `1 / n ^ k`, etc.)
