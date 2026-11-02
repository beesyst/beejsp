import SubspaceBridge.AllPointFixedWeights4
open scoped BigOperators Matrix
namespace JSP000334
noncomputable section

def allpoint_balanced_values4 (Q : ℝ) (a : Fin 3 → Fin 4 → ℝ) (tau : Fin 3) (i : Fin 4) : ℝ :=
  if tau = 0 then a tau i*Q^((1 : ℝ)/32) else a tau i

theorem allpoint_balanced_weights4 (H : ℝ) (hH : 4 ≤ H)
    (a : Fin 3 → Fin 4 → ℝ) (ha : ∀ tau i, 0 < a tau i)
    (hreal : ∀ i, a 0 i ≤ 4*H)
    (hfinite : ∀ tau, tau ≠ 0 → ∀ i, a tau i ≤ 1)
    (hinv : ∀ tau i, (a tau i)⁻¹ ≤ 4*H)
    (hprod : (∏ tau, ∏ i, a tau i)*H = 1) :
    let Q := H^8
    let W := allpoint_balanced_values4 Q a
    1 < Q ∧ sourceWeightConditions4 (sourceLogWeights4 Q W) ∧
      (∀ tau i, Q^(sourceLogWeights4 Q W tau i) = W tau i) ∧
      (∀ i, a 0 i = Q^(sourceLogWeights4 Q W 0 i-(1 : ℝ)/32)) ∧
      (∀ tau, tau ≠ 0 → ∀ i, a tau i = Q^(sourceLogWeights4 Q W tau i)) := by
  intro Q W
  have hH0 : 0 < H := by linarith
  have hQ : 1 < Q := by dsimp [Q]; nlinarith [sq_nonneg (H^2-1)]
  have hQ0 := lt_trans zero_lt_one hQ
  let r := Q^((1 : ℝ)/32)
  have hr : 0 < r := Real.rpow_pos_of_pos hQ0 _
  have hr1 : 1 ≤ r := Real.one_le_rpow hQ.le (by norm_num)
  have hrH : r ≤ H := by
    have he : (H^8)^((1 : ℝ)/32) = H^((1 : ℝ)/4) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hH0.le]
      congr 1
      norm_num
    change (H^8)^((1 : ℝ)/32) ≤ H
    rw [he]
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ H by linarith) (by norm_num : (1 : ℝ)/4 ≤ 1)
  have hrpow : r^4 = H := by
    change ((H^8)^((1 : ℝ)/32))^4 = H
    rw [← Real.rpow_mul_natCast (pow_pos hH0 8).le,← Real.rpow_natCast,← Real.rpow_mul hH0.le]
    norm_num
  have hW : ∀ tau i, 0 < W tau i := by
    intro tau i
    dsimp [W,allpoint_balanced_values4]
    split_ifs
    · exact mul_pos (ha tau i) (Real.rpow_pos_of_pos hQ0 _)
    · exact ha tau i
  have hH2 : 4*H^2 < H^4 := by nlinarith [sq_nonneg (H^2-4)]
  have h48 : H^4≤H^8 := by nlinarith [sq_nonneg (H^4-1)]
  have h3H : 4*H < Q := by change 4*H<H^8; nlinarith
  have h3H2 : 4*H^2 < Q := hH2.trans_le h48
  have hcut : ∀ tau i, (W tau i)⁻¹ < Q := by
    intro tau i
    by_cases ht : tau = 0
    · subst tau
      change (a 0 i*r)⁻¹ < Q
      rw [mul_inv_rev]
      have hri : r⁻¹ ≤ 1 := (inv_le_one₀ hr).mpr hr1
      have hh := mul_le_mul_of_nonneg_right hri (inv_pos.mpr (ha 0 i)).le
      exact (by nlinarith [hinv 0 i] : r⁻¹*(a 0 i)⁻¹ ≤ 4*H).trans_lt h3H
    · simpa only [W,allpoint_balanced_values4,if_neg ht] using (hinv tau i).trans_lt h3H
  have hcut0 : ∀ i, W 0 i < Q := by
    intro i
    change a 0 i*r < Q
    have hh := mul_le_mul (hreal i) hrH hr.le (by linarith : 0 ≤ 4*H)
    exact (by nlinarith : a 0 i*r ≤ 4*H^2).trans_lt h3H2
  have hWfin : ∀ tau, tau ≠ 0 → ∀ i, W tau i ≤ 1 := by
    intro tau ht i
    simpa only [W,allpoint_balanced_values4,if_neg ht] using hfinite tau ht i
  have hWprod : (∏ tau, ∏ i, W tau i) = 1 := by
    have hfactor (tau : Fin 3) : (∏ i : Fin 4,W tau i)=
        if tau=0 then (∏ i : Fin 4,a tau i)*r^4 else ∏ i : Fin 4,a tau i := by
      by_cases ht : tau=0
      · subst tau
        simp only [W,allpoint_balanced_values4,if_pos rfl,ite_true]
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
        rfl
      · simp only [W,allpoint_balanced_values4,if_neg ht]
    simp_rw [hfactor]
    simp only [Fin.prod_univ_three,Fin.isValue,Fin.reduceEq,ite_true,ite_false]
    rw [hrpow]
    have hp := hprod
    simp only [Fin.prod_univ_three] at hp
    nlinarith only [hp]
  have heq := sourceLogWeights4_rpow Q hQ W hW
  refine ⟨hQ,sourceLogWeights4_conditions Q hQ W hW hcut hcut0 hWfin hWprod,heq,?_,?_⟩
  · intro i
    rw [Real.rpow_sub hQ0,heq]
    change a 0 i = (a 0 i*r)/r
    exact (mul_div_cancel_right₀ _ hr.ne').symm
  · intro tau ht i
    rw [heq]
    simp only [W,allpoint_balanced_values4,if_neg ht]

end
end JSP000334
