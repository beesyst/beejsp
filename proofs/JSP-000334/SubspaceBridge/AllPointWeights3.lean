import SubspaceBridge.CofactorOriginalRankOne3
open scoped BigOperators Matrix
namespace JSP000334
noncomputable section

def allpoint_balanced_values3 (Q : ℝ) (a : Fin 3 → Fin 3 → ℝ) (tau i : Fin 3) : ℝ :=
  if tau = 0 then a tau i*Q^((1 : ℝ)/12) else a tau i

theorem allpoint_balanced_weights3 (H : ℝ) (hH : 3 ≤ H)
    (a : Fin 3 → Fin 3 → ℝ) (ha : ∀ tau i, 0 < a tau i)
    (hreal : ∀ i, a 0 i ≤ 3*H)
    (hfinite : ∀ tau, tau ≠ 0 → ∀ i, a tau i ≤ 1)
    (hinv : ∀ tau i, (a tau i)⁻¹ ≤ 3*H)
    (hprod : (∏ tau, ∏ i, a tau i)*H = 1) :
    let Q := H^4
    let W := allpoint_balanced_values3 Q a
    1 < Q ∧ sourceWeightConditions3 (sourceLogWeights3 Q W) ∧
      (∀ tau i, Q^(sourceLogWeights3 Q W tau i) = W tau i) ∧
      (∀ i, a 0 i = Q^(sourceLogWeights3 Q W 0 i-(1 : ℝ)/12)) ∧
      (∀ tau, tau ≠ 0 → ∀ i, a tau i = Q^(sourceLogWeights3 Q W tau i)) := by
  intro Q W
  have hH0 : 0 < H := by linarith
  have hQ : 1 < Q := by dsimp [Q]; nlinarith [sq_nonneg (H^2-1)]
  have hQ0 := lt_trans zero_lt_one hQ
  let r := Q^((1 : ℝ)/12)
  have hr : 0 < r := Real.rpow_pos_of_pos hQ0 _
  have hr1 : 1 ≤ r := Real.one_le_rpow hQ.le (by norm_num)
  have hrH : r ≤ H := by
    have he : (H^4)^((1 : ℝ)/12) = H^((1 : ℝ)/3) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hH0.le]
      congr 1
      norm_num
    change (H^4)^((1 : ℝ)/12) ≤ H
    rw [he]
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ H by linarith) (by norm_num : (1 : ℝ)/3 ≤ 1)
  have hrpow : r^3 = H := by
    change ((H^4)^((1 : ℝ)/12))^3 = H
    rw [← Real.rpow_mul_natCast (pow_pos hH0 4).le,← Real.rpow_natCast,← Real.rpow_mul hH0.le]
    norm_num
  have hW : ∀ tau i, 0 < W tau i := by
    intro tau i
    dsimp [W,allpoint_balanced_values3]
    split_ifs
    · exact mul_pos (ha tau i) (Real.rpow_pos_of_pos hQ0 _)
    · exact ha tau i
  have h3H : 3*H < Q := by dsimp [Q]; nlinarith [sq_nonneg (H^2-3)]
  have h3H2 : 3*H^2 < Q := by dsimp [Q]; nlinarith [sq_nonneg (H^2-3)]
  have hcut : ∀ tau i, (W tau i)⁻¹ < Q := by
    intro tau i
    by_cases ht : tau = 0
    · subst tau
      change (a 0 i*r)⁻¹ < Q
      rw [mul_inv_rev]
      have hri : r⁻¹ ≤ 1 := (inv_le_one₀ hr).mpr hr1
      have hh := mul_le_mul_of_nonneg_right hri (inv_pos.mpr (ha 0 i)).le
      exact (by nlinarith [hinv 0 i] : r⁻¹*(a 0 i)⁻¹ ≤ 3*H).trans_lt h3H
    · simpa only [W,allpoint_balanced_values3,if_neg ht] using (hinv tau i).trans_lt h3H
  have hcut0 : ∀ i, W 0 i < Q := by
    intro i
    change a 0 i*r < Q
    have hh := mul_le_mul (hreal i) hrH hr.le (by linarith : 0 ≤ 3*H)
    exact (by nlinarith : a 0 i*r ≤ 3*H^2).trans_lt h3H2
  have hWfin : ∀ tau, tau ≠ 0 → ∀ i, W tau i ≤ 1 := by
    intro tau ht i
    simpa only [W,allpoint_balanced_values3,if_neg ht] using hfinite tau ht i
  have hWprod : (∏ tau, ∏ i, W tau i) = 1 := by
    simp only [W,allpoint_balanced_values3,Fin.prod_univ_three,Fin.isValue,Fin.reduceEq,ite_true,ite_false] at ⊢
    have hp := hprod
    simp only [Fin.prod_univ_three] at hp
    change (a 0 0*r*(a 0 1*r)*(a 0 2*r))*(a 1 0*a 1 1*a 1 2)*(a 2 0*a 2 1*a 2 2) = 1
    calc
      _ = (a 0 0*a 0 1*a 0 2)*(a 1 0*a 1 1*a 1 2)*(a 2 0*a 2 1*a 2 2)*r^3 := by ring
      _ = 1 := by rw [hrpow]; exact hp
  have heq := sourceLogWeights3_rpow Q hQ W hW
  refine ⟨hQ,sourceLogWeights3_conditions Q hQ W hW hcut hcut0 hWfin hWprod,heq,?_,?_⟩
  · intro i
    rw [Real.rpow_sub hQ0,heq]
    change a 0 i = (a 0 i*r)/r
    exact (mul_div_cancel_right₀ _ hr.ne').symm
  · intro tau ht i
    rw [heq]
    simp only [W,allpoint_balanced_values3,if_neg ht]

end
end JSP000334
