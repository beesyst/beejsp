import SubspaceBridge.SourceOriginalData10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceOriginalVariable10
open OriginalDual10 SourceSampling10 OriginalDeformation10
noncomputable section

def originalPowerWeights10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset SourceSelectedSet10.MixedIndex10}
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) : Fin 3 → Fin 10 → ℝ :=
  ![fun i => normalizedWidth10 Q (D.A i)/5,
    fun i => normalizedFinite10 2 Q (D.f2 i)/5,fun i => normalizedFinite10 3 Q (D.f3 i)/5]

theorem original_power_weights_bounds10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset SourceSelectedSet10.MixedIndex10}
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    (∀ tau i, |originalPowerWeights10 D tau i| ≤ 1/5) ∧
      (∀ i, originalPowerWeights10 D 1 i ≤ 0) ∧ (∀ i, originalPowerWeights10 D 2 i ≤ 0) ∧
      (∑ tau, ∑ i, originalPowerWeights10 D tau i) = 0 := by
  have h0 (i) := logWeight10_bounds Q (D.A i) hQ (D.positive i) (D.sizes i).1 (D.sizes i).2.1
  have h1 (i) := normalized_finite_bounds10 2 (by decide) Q hQ (D.f2 i) (D.nonpos2 i) (D.sizes i).2.2.1
  have h2 (i) := normalized_finite_bounds10 3 (by decide) Q hQ (D.f3 i) (D.nonpos3 i) (D.sizes i).2.2.2
  refine ⟨?_,fun i => div_nonpos_of_nonpos_of_nonneg (h1 i).2 (by norm_num),
    fun i => div_nonpos_of_nonpos_of_nonneg (h2 i).2 (by norm_num),?_⟩
  · intro tau i
    fin_cases tau
    · change |normalizedWidth10 Q (D.A i)/5| ≤ 1/5
      change ∀ i, -1 < normalizedWidth10 Q (D.A i) ∧ normalizedWidth10 Q (D.A i) < 1 at h0
      exact abs_le.mpr ⟨by linarith [(h0 i).1],by linarith [(h0 i).2]⟩
    · change |normalizedFinite10 2 Q (D.f2 i)/5| ≤ 1/5
      exact abs_le.mpr ⟨by linarith [(h1 i).1],by linarith [(h1 i).2]⟩
    · change |normalizedFinite10 3 Q (D.f3 i)/5| ≤ 1/5
      exact abs_le.mpr ⟨by linarith [(h2 i).1],by linarith [(h2 i).2]⟩
  · have hb := normalized_balance10 Q D.A D.positive D.f2 D.f3 D.balance
    simp only [originalPowerWeights10,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,← Finset.sum_div]
    simp only [Finset.sum_add_distrib] at hb
    linarith

theorem original_power_frame_bounds10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset SourceSelectedSet10.MixedIndex10}
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    (∀ (j : Fin 9) i, ‖(L *ᵥ integerReal (D.u j.castSucc)) i‖ ≤
      (Q^5)^(originalPowerWeights10 D 0 i-delta/5)) ∧
    (∀ (j : Fin 10) i, ‖(SourceForms10.finiteMatrix10 2 A2 *ᵥ
      (fun k => (D.u j k : ℚ_[2]))) i‖ ≤ (Q^5)^(originalPowerWeights10 D 1 i)) ∧
    (∀ (j : Fin 10) i, ‖(SourceForms10.finiteMatrix10 3 A3 *ᵥ
      (fun k => (D.u j k : ℚ_[3]))) i‖ ≤ (Q^5)^(originalPowerWeights10 D 2 i)) := by
  have hq : 0 < Q := zero_lt_one.trans hQ
  have hm := (sourceMinima10_pos_mono A2 A3 L hL Q hQ
    (fun i => normalizedWidth10 Q (D.A i)) (fun i => normalizedFinite10 2 Q (D.f2 i))
    (fun i => normalizedFinite10 3 Q (D.f3 i))).2
  refine ⟨?_,?_,?_⟩
  · intro j i
    have hpoint := (originalCoordinates10_bounds L hL Q hQ
      (fun i => normalizedWidth10 Q (D.A i)) (integerReal (D.u j.castSucc)) _).mp
      (D.attaining j.castSucc).le i
    have hsmall := (hm (show j.castSucc ≤ (8 : Fin 10) by change j.val ≤ 8; omega)).trans D.small.le
    rw [Real.norm_eq_abs]
    apply hpoint.trans
    have hh := mul_le_mul_of_nonneg_right hsmall
      (Real.rpow_pos_of_pos hq (normalizedWidth10 Q (D.A i))).le
    apply hh.trans_eq
    rw [← Real.rpow_add hq]
    change Q^(-delta+normalizedWidth10 Q (D.A i)) =
      (Q^5)^(normalizedWidth10 Q (D.A i)/5-delta/5)
    rw [← Real.rpow_natCast_mul hq.le]
    congr 1
    ring
  · intro j i
    change ‖((A2.map (algebraMap ℚ ℚ_[2])) *ᵥ _) i‖ ≤ (Q^5)^(normalizedFinite10 2 Q (D.f2 i)/5)
    rw [rescaled_power10 Q _ hq,normalized_finite_exact10 2 (by decide) Q hQ,finite_form_norm10]
    have hr := (Rat.cast_le (K := ℝ)
      (p := padicNorm 2 ((A2 *ᵥ (fun k => (D.u j k : ℚ))) i))
      (q := (2 : ℚ)^(D.f2 i))).mpr (D.member2 j i)
    simpa only [Rat.cast_zpow,Rat.cast_ofNat] using hr
  · intro j i
    change ‖((A3.map (algebraMap ℚ ℚ_[3])) *ᵥ _) i‖ ≤ (Q^5)^(normalizedFinite10 3 Q (D.f3 i)/5)
    rw [rescaled_power10 Q _ hq,normalized_finite_exact10 3 (by decide) Q hQ,finite_form_norm10]
    have hr := (Rat.cast_le (K := ℝ)
      (p := padicNorm 3 ((A3 *ᵥ (fun k => (D.u j k : ℚ))) i))
      (q := (3 : ℚ)^(D.f3 i))).mpr (D.member3 j i)
    simpa only [Rat.cast_zpow,Rat.cast_ofNat] using hr

end
end CompoundFeasibility.SourceOriginalVariable10
