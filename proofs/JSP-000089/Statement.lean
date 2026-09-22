import Main

namespace JSP000089

/-- The count of members of `S` in `{1, ..., n}`. -/
noncomputable def initialSegmentCount (S : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter fun k => 0 < k ∧ k ∈ S).card

/-- A set of positive integers has density zero when every positive rational
bound eventually exceeds its initial-segment proportion. -/
def DensityZero (S : Set ℕ) : Prop :=
  ∀ numerator denominator : ℕ, 0 < numerator → 0 < denominator →
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      denominator * initialSegmentCount S n ≤ numerator * n

/-- The source's explicit `O(n^0.99)` conclusion. -/
def SourceSparsity099 (S : Set ℕ) : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ,
    initialSegmentCount S n ^ 100 ≤ K ^ 100 * n ^ 99

/-- The cross-multiplied, division-free meaning of average degree at least `c`. -/
noncomputable def averageDegreeAtLeast {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c : ℕ) : Prop := by
  classical
  exact 0 < Fintype.card V ∧ c * Fintype.card V ≤ 2 * G.edgeFinset.card

/-- The intended, unproved top-level target corresponding to Verstraëte's
Theorem 1. This definition is a statement contract, not a completion claim. -/
noncomputable def jsp_000089_statement : Prop :=
  ∃ S : Set ℕ, SourceSparsity099 S ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      averageDegreeAtLeast G 10 → HasCycleLengthIn G S

end JSP000089
