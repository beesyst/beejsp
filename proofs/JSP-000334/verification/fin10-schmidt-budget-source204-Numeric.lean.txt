import SubspaceBridge.SourceSampleSchmidtGrowth10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSchmidtBudget10

theorem denominator_budget_threshold (m : ℕ) (alpha w C Q b : ℝ)
    (ha : 0 < alpha) (hw : 0 < w) (hC : 0 < C) (hQ : 0 < Q)
    (hb : Q^(alpha/9) ≤ b)
    (hlarge : (2 : ℝ)^(27*(m : ℝ)/(alpha*w*C)) ≤ Q) :
    (2 : ℝ)^(3*m) ≤ b^(w*C) := by
  have he : (27*(m : ℝ)/(alpha*w*C))*(alpha*w*C/9) = 3*(m : ℝ) := by
    field_simp
    <;> ring
  calc
    (2 : ℝ)^(3*m) = (2 : ℝ)^(3*(m : ℝ)) := by
      rw [show (3*(m : ℝ)) = ((3*m : ℕ) : ℝ) by push_cast; ring,Real.rpow_natCast]
    _ = ((2 : ℝ)^(27*(m : ℝ)/(alpha*w*C)))^(alpha*w*C/9) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),he]
    _ ≤ Q^(alpha*w*C/9) :=
      Real.rpow_le_rpow (by positivity) hlarge (by positivity)
    _ = (Q^(alpha/9))^(w*C) := by rw [← Real.rpow_mul hQ.le]; congr 1; ring
    _ ≤ b^(w*C) := Real.rpow_le_rpow (by positivity) hb (by positivity)

theorem polynomial_budget_threshold (alpha w C D R Q b r H : ℝ)
    (ha : 0 < alpha) (hw : 0 < w) (hC : 0 < C) (hD : 0 < D)
    (hQ : 0 < Q) (hr : 0 ≤ r) (hb : Q^(alpha/9) ≤ b)
    (hH : H ≤ D^(R*r)) (hlarge : D^(9*R/(alpha*w*C)) ≤ Q) :
    H ≤ b^(w*r*C) := by
  have he : (9*R/(alpha*w*C))*(alpha*w*C/9) = R := by
    field_simp
  have hbase : D^R ≤ Q^(alpha*w*C/9) := by
    calc
      D^R = (D^(9*R/(alpha*w*C)))^(alpha*w*C/9) := by
        rw [← Real.rpow_mul hD.le,he]
      _ ≤ Q^(alpha*w*C/9) :=
        Real.rpow_le_rpow (by positivity) hlarge (by positivity)
  have hroot : 0 ≤ b := (Real.rpow_nonneg hQ.le _).trans hb
  calc
    H ≤ D^(R*r) := hH
    _ = (D^R)^r := Real.rpow_mul hD.le R r
    _ ≤ (Q^(alpha*w*C/9))^r := Real.rpow_le_rpow (by positivity) hbase hr
    _ = (Q^(alpha/9))^(w*r*C) := by
      rw [← Real.rpow_mul hQ.le,← Real.rpow_mul hQ.le]; congr 1; ring
    _ ≤ b^(w*r*C) := Real.rpow_le_rpow (by positivity) hb (by positivity)

end CompoundFeasibility.SourceSchmidtBudget10
