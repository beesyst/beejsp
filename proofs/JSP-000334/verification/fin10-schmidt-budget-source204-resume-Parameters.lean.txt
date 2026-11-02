import SubspaceBridge.SourceSampleSchmidtParameters10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSchmidtBudget10

theorem explicit_schmidt_parameters10 (m : ℕ) (hm : 0 < m) (eta : ℝ) (he : 0 < eta) :
    let theta := min (1/24 : ℝ) ((m : ℝ)*eta/2)
    let rho := min (1/2 : ℝ) (JSP000334.omega65 m theta)
    0 < theta ∧ theta < 1/12 ∧ theta < (m : ℝ)*eta ∧
      0 < rho ∧ rho ≤ 1/2 ∧ rho ≤ JSP000334.omega65 m theta := by
  let theta := min (1/24 : ℝ) ((m : ℝ)*eta/2)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ht : 0 < theta := lt_min (by norm_num) (by positivity)
  have htu : theta < 1/12 := (min_le_left _ _).trans_lt (by norm_num)
  have hte : theta < (m : ℝ)*eta := by
    have hh := min_le_right (1/24 : ℝ) ((m : ℝ)*eta/2)
    dsimp [theta]
    nlinarith [mul_pos hmR he]
  have ho := JSP000334.omega65_pos m theta ht
  exact ⟨ht,htu,hte,
    lt_min (by norm_num) ho,min_le_left _ _,min_le_right _ _⟩

end CompoundFeasibility.SourceSchmidtBudget10
