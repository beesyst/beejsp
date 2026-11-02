import SubspaceBridge.SourceSchmidtBudgetBounds10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFixedBudget10
open SourceSchmidtGrowth10 SourceSchmidtBudget10

theorem height_envelope_growth10 (alpha C_upper Q0 Q H0 H b0 b r0 r : ℝ)
    (ha : 0 < alpha) (hQ0 : 1 < Q0) (hQ : 1 < Q)
    (hr0 : 0 < r0) (hr : 0 < r) (habsorb : C_upper ≤ Q0)
    (hu0 : H0 ≤ C_upper*Q0^9) (hbu0 : b0 ≤ H0) (hb0 : 0 < b0)
    (hl : Q^alpha ≤ H) (hroot : H^(1/9 : ℝ) ≤ b)
    (hH : 1 ≤ H) (hbalance : r0*Real.log Q0 ≤ r*Real.log Q) :
    Q^(alpha/9) ≤ b ∧
      b0^(r0*min (1/2 : ℝ) (alpha/180)) ≤ b^r := by
  exact ⟨height_denominator_power_lower10 Q alpha H b (zero_lt_one.trans hQ) hl hroot,
    denominator_growth_numeric10 alpha C_upper Q0 Q H0 H b0 b r0 r
      ha hQ0 hQ hr0 hr habsorb hu0 hbu0 hb0 hl hroot hH hbalance⟩

end CompoundFeasibility.SourceFixedBudget10
