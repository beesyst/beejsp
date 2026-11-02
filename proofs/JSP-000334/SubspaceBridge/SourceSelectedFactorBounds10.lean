import SubspaceBridge.SourceSelectedPowers10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSelectedUpper10
open OriginalDual10 SourceSelectedSet10 SchmidtNormal10

theorem three_factor_bound10 (x0 x2 x3 b0 b2 b3 : ℝ)
    (hx0 : 0 ≤ x0) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3)
    (h0 : x0 ≤ b0) (h2 : x2 ≤ b2) (h3 : x3 ≤ b3) :
    x0*x2*x3 ≤ b0*b2*b3 := by
  exact mul_le_mul (mul_le_mul h0 h2 hx2 (hx0.trans h0)) h3 hx3
    (mul_nonneg (hx0.trans h0) (hx2.trans h2))

end CompoundFeasibility.SourceSelectedUpper10
