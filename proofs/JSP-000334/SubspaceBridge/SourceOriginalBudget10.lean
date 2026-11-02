import SubspaceBridge.SourceSelectedCanonical10
open scoped BigOperators Matrix
namespace CompoundFeasibility.SourceOriginalBudget10
open SourceSelectedUpper10 SourceSelectedSet10 OriginalDual10
noncomputable section

theorem complement_product10 (a b d : Fin 10 → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hd : ∀ i, 0 < d i)
    (hbal : (∏ i, a i)*(∏ i, b i)*(∏ i, d i) = 1) (s : MixedIndex10) :
    (∏ k : Fin 9, a ((s 0).succAbove k)) *
      (∏ k : Fin 9, b ((s 1).succAbove k)) *
      (∏ k : Fin 9, d ((s 2).succAbove k)) = (a (s 0)*b (s 1)*d (s 2))⁻¹ := by
  rw [inv_eq_one_div,eq_div_iff (mul_pos (mul_pos (ha _) (hb _)) (hd _)).ne']
  rw [Fin.prod_univ_succAbove a (s 0),Fin.prod_univ_succAbove b (s 1),
    Fin.prod_univ_succAbove d (s 2)] at hbal
  nlinarith only [hbal]

theorem absolute_selected_budget10 (Q delta N : ℝ) (hQ : 1 < Q)
    (hsmall : N ≤ Q^(-9*delta))
    (a b d : Fin 10 → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hd : ∀ i, 0 < d i)
    (hbal : (∏ i, a i)*(∏ i, b i)*(∏ i, d i) = 1)
    (s : MixedIndex10) (hsel : 1 ≤ a (s 0)*b (s 1)*d (s 2)*Q^(delta/2)) :
    (362880*N*(∏ k : Fin 9, a ((s 0).succAbove k)))*
      (∏ k : Fin 9, b ((s 1).succAbove k))*
      (∏ k : Fin 9, d ((s 2).succAbove k)) ≤ 362880*Q^(-17*delta/2) := by
  have hq : 0 < Q := zero_lt_one.trans hQ
  have hpos := mul_pos (mul_pos (ha (s 0)) (hb (s 1))) (hd (s 2))
  have hinv : (a (s 0)*b (s 1)*d (s 2))⁻¹ ≤ Q^(delta/2) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hpos).mpr
    simpa only [mul_comm] using hsel
  calc
    _ = 362880*N*((a (s 0)*b (s 1)*d (s 2))⁻¹) := by
      rw [← complement_product10 a b d ha hb hd hbal s]
      ring
    _ ≤ 362880*Q^(-9*delta)*Q^(delta/2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsmall (by norm_num)) hinv
        (inv_nonneg.mpr hpos.le) (by positivity)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hq]; congr 2; ring

end
end CompoundFeasibility.SourceOriginalBudget10
