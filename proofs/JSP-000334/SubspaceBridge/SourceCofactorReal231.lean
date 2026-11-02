import SubspaceBridge.SourceFramePairing224
import SubspaceBridge.SourceOriginalBounds215
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceLastDual231
open OriginalDual10 SourceSatz51Entry218 SourceOriginalVariable10 SourceFrame224

theorem original_balance231 (q : ℝ) (hq : 1 < q) (A c2 c3 : Fin 10 → ℝ)
    (hA : ∀ i, 0 < A i) (hb : (∏ i, A i*q^(c2 i)*q^(c3 i)) = 1) :
    ∑ i, (normalizedWidth10 q (A i) + c2 i + c3 i) = 0 := by
  apply (Real.rpow_right_inj (zero_lt_one.trans hq) (ne_of_gt hq)).mp
  rw [Real.rpow_sum_of_pos (zero_lt_one.trans hq)]
  simp_rw [Real.rpow_add (zero_lt_one.trans hq), normalized_width_exact10 q _ hq (hA _)]
  simpa only [Real.rpow_zero] using hb

variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {q : ℝ} {hq : 1 < q} {c2 c3 A : Fin 10 → ℝ} {delta : ℝ}

theorem source_width_covolume231 (h2 : A2.det = 1) (h3 : A3.det = 1)
    (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) :
    (∏ i, A i) ≤ ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3)) := by
  have hf : sourceLocalDetFactor10 A2 A3 = 1 := by
    simp only [sourceLocalDetFactor10, h2, h3, padicNorm.one, Rat.cast_one, one_mul]
  have h := sourceLattice10_covolume_width_lower A2 A3 q hq
    (fun i => normalizedWidth10 q (A i)) c2 c3 (original_balance231 q hq A c2 c3 D.positive D.balance)
  simp_rw [hf, one_mul, normalized_width_exact10 q _ hq (D.positive _)] at h
  exact h

theorem source_first_nine_product231 (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) :
    (∏ j : Fin 9, sourceMinima10 A2 A3 L hL q hq
      (fun i => normalizedWidth10 q (A i)) c2 c3 j.castSucc) ≤ q^(-9*delta) := by
  calc
    _ ≤ ∏ _j : Fin 9, q^(-delta) := Finset.prod_le_prod
      (fun j _ => (source_first_nine_minima224 D j).1)
      (fun j _ => (source_first_nine_minima224 D j).2.trans D.small.le)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_lt_one.trans hq).le]
      congr 1
      ring

theorem source_real_cofactor231 (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1)
    (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) (i : Fin 10) :
    |(L⁻¹.transpose *ᵥ integerReal (integerLastDual10 D.u)) i| ≤
      362880 * q^(-9*delta) *
        (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3)) / A i) := by
  have hpoint := fun (j : Fin 9) (k : Fin 10) => source_frame_coordinates224 D j.castSucc k
  have hb := real_cofactor_fin10 L hLd D.u
    (fun j : Fin 9 => sourceMinima10 A2 A3 L hL q hq
      (fun k => normalizedWidth10 q (A k)) c2 c3 j.castSucc) A hpoint i
  rw [Real.norm_eq_abs] at hb
  have ho : (∏ k : Fin 9, A (i.succAbove k)) = (∏ k, A k) / A i := by
    rw [Fin.prod_univ_succAbove A i]
    field_simp [(D.positive i).ne']
  calc
    _ ≤ _ := hb
    _ ≤ 362880 * q^(-9*delta) * (∏ k : Fin 9, A (i.succAbove k)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (source_first_nine_product231 D) (by norm_num))
        (Finset.prod_nonneg (fun k _ => (D.positive _).le))
    _ = 362880 * q^(-9*delta) * ((∏ k, A k) / A i) := by rw [ho]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (source_width_covolume231 h2 h3 D) (D.positive i).le)
      (mul_nonneg (by norm_num) (Real.rpow_pos_of_pos (zero_lt_one.trans hq) _).le)

end CompoundFeasibility.SourceLastDual231
