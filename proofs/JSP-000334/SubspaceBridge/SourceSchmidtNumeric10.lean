import SubspaceBridge.SchmidtOmega6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSchmidtGrowth10

theorem schmidt_constant_range10 (alpha : ℝ) (ha : 0 < alpha) :
    0 < min (1/2 : ℝ) (alpha/180) ∧ min (1/2 : ℝ) (alpha/180) ≤ 1 ∧
      10*min (1/2 : ℝ) (alpha/180) ≤ alpha/9 := by
  refine ⟨lt_min (by norm_num) (by positivity), (min_le_left _ _).trans (by norm_num), ?_⟩
  have h := min_le_right (1/2 : ℝ) (alpha/180)
  nlinarith

theorem denominator_growth_numeric10 (alpha C_upper Q0 Q H0 H b0 b r0 r : ℝ)
    (ha : 0 < alpha) (hQ0 : 1 < Q0) (hQ : 1 < Q)
    (hr0 : 0 < r0) (hr : 0 < r) (habsorb : C_upper ≤ Q0)
    (hu0 : H0 ≤ C_upper*Q0^9) (hbu0 : b0 ≤ H0) (hb0 : 0 < b0)
    (hl : Q^alpha ≤ H) (hroot : H^(1/9 : ℝ) ≤ b)
    (hH : 1 ≤ H) (hbalance : r0*Real.log Q0 ≤ r*Real.log Q) :
    b0^(r0*min (1/2 : ℝ) (alpha/180)) ≤ b^r := by
  obtain ⟨hC,hC1,hCmp⟩ := schmidt_constant_range10 alpha ha
  have hQ0p : 0 < Q0 := zero_lt_one.trans hQ0
  have hQp : 0 < Q := zero_lt_one.trans hQ
  have hb0upper : b0 ≤ Q0^10 := by
    calc
      b0 ≤ C_upper*Q0^9 := hbu0.trans hu0
      _ ≤ Q0*Q0^9 := mul_le_mul_of_nonneg_right habsorb (by positivity)
      _ = Q0^10 := by ring
  have hlower : Q^(alpha/9) ≤ b := by
    calc
      Q^(alpha/9) = (Q^alpha)^(1/9 : ℝ) := by rw [← Real.rpow_mul hQp.le]; congr 1; ring
      _ ≤ H^(1/9 : ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hQp.le _) hl (by norm_num)
      _ ≤ b := hroot
  have hbp : 0 < b := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hH) _).trans_le hroot
  have huLog : Real.log b0 ≤ 10*Real.log Q0 := by
    have hh := Real.log_le_log hb0 hb0upper
    rw [Real.log_pow] at hh
    exact hh
  have hlLog : (alpha/9)*Real.log Q ≤ Real.log b := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hQp _) hlower
    rw [Real.log_rpow hQp] at hh
    exact hh
  rw [Real.rpow_def_of_pos hb0, Real.rpow_def_of_pos hbp]
  apply Real.exp_le_exp.mpr
  calc
    Real.log b0*(r0*min (1/2 : ℝ) (alpha/180)) ≤
        (10*Real.log Q0)*(r0*min (1/2 : ℝ) (alpha/180)) :=
      mul_le_mul_of_nonneg_right huLog (mul_pos hr0 hC).le
    _ = (10*min (1/2 : ℝ) (alpha/180))*(r0*Real.log Q0) := by ring
    _ ≤ (alpha/9)*(r0*Real.log Q0) :=
      mul_le_mul_of_nonneg_right hCmp (mul_pos hr0 (Real.log_pos hQ0)).le
    _ ≤ (alpha/9)*(r*Real.log Q) := mul_le_mul_of_nonneg_left hbalance (by positivity)
    _ = ((alpha/9)*Real.log Q)*r := by ring
    _ ≤ Real.log b*r := mul_le_mul_of_nonneg_right hlLog hr.le

theorem schmidt_parameters10 (m : ℕ) (hm : 0 < m) (eta : ℝ) (he : 0 < eta) :
    ∃ theta rho : ℝ, 0 < theta ∧ theta < 1/12 ∧ theta < (m : ℝ)*eta ∧
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
  exact ⟨theta,min (1/2 : ℝ) (JSP000334.omega65 m theta),ht,htu,hte,
    lt_min (by norm_num) ho,min_le_left _ _,min_le_right _ _⟩

end CompoundFeasibility.SourceSchmidtGrowth10
