import SubspaceBridge
namespace JSP000334

theorem omega65_le_induction (m : ℕ) (hm : 1 ≤ m) (t : ℝ)
    (ht : 0 < t) (ht' : t < 1/12) : omega65 m t ≤ rothInductionOmega m t := by
  have he : 2 ^ (m - 1) ≤ 2 ^ m - 1 := by
    have hpow : (2 : ℕ) ^ m = 2 ^ (m - 1) * 2 := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
    have hp := Nat.one_le_two_pow (n := m - 1)
    omega
  unfold omega65 rothInductionOmega
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_of_le_one (by positivity : (0 : ℝ) ≤ t/12)
    (by linarith : t/12 ≤ 1) he

theorem omega65_two_lt_induction (t : ℝ) (ht : 0 < t) (ht' : t < 1/12) :
    omega65 2 t < rothInductionOmega 2 t := by
  unfold omega65 rothInductionOmega
  apply mul_lt_mul_of_pos_left _ (by positivity)
  apply pow_lt_pow_right_of_lt_one₀ (by positivity : (0 : ℝ) < t/12)
    (by linarith : t/12 < 1)
  norm_num

theorem omega65_one (t : ℝ) : omega65 1 t = t := by
  norm_num [omega65]
  ring

theorem omega65_le_t (m : ℕ) (hm : 1 ≤ m) (t : ℝ) (ht : 0 < t) (ht' : t < 1/12) :
    omega65 m t ≤ t :=
  (omega65_le_induction m hm t ht ht').trans (rothInductionOmega_le_t m hm t ht ht')

end JSP000334
