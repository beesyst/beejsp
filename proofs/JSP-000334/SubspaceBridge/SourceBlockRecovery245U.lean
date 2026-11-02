import SubspaceBridge.SourceShortSpan241
import SubspaceBridge.SourceBlockUpper245R
import SubspaceBridge.SourceBlockKernel245U
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.BlockRank4_245U
open BlockReduction245P BlockReduction245Q BlockReduction245R SchmidtNormal10
  Exterior53_242 SourceOriginalDual10 OriginalDual10 SourceFlag241

theorem normal_join245U (b : Fin 10 → ℤ) (x y : Fin 5 → ℤ) :
    normalForm10 b (fun j => ((join245Q x y j : ℤ) : ℚ)) =
      (∑ i, ((first245Q b i : ℤ) : ℚ)*(x i : ℚ)) +
      ∑ i, ((second245Q b i : ℤ) : ℚ)*(y i : ℚ) := by
  rw [normalForm10_apply, ← Equiv.sum_comp blockIndex245P]
  simp [Fintype.sum_sum_type, join245Q, first245Q, second245Q]

theorem normal_dummy245U (b : Fin 10 → ℤ) (i : Fin 5) :
    normalForm10 b (fun j => ((join245Q 0 (Pi.single i (1 : ℤ)) j : ℤ) : ℚ)) =
      ((second245Q b i : ℤ) : ℚ) := by
  rw [normal_join245U]
  simp [Pi.single_apply]

theorem normal_original245U (b : Fin 10 → ℤ) (x : Fin 5 → ℤ) :
    normalForm10 b (fun j => ((join245Q x 0 j : ℤ) : ℚ)) =
      originalNormal245U b (fun i => (x i : ℚ)) := by
  rw [normal_join245U]
  simp [originalNormal245U]

theorem sameQ_annihilation245U
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ) (delta : ℝ) (hd : 0 < delta)
    (hsource : sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3 <
      sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 4*Q^(-delta))
    (hsep : (Q^2)⁻¹ ≤ Q^2*sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3)
    (b : Fin 10 → ℤ)
    (w : Fin 10 → originalSourceGroup10 (block245P A2) (block245P A3) (Q^3)
      (weightp245P c2) (weightp245P c3))
    (hw : LinearIndependent ℝ (fun j => integerReal (w j : Fin 10 → ℤ)))
    (hatt : ∀ j, coordinateGauge10 (originalCoordinates10 (block245P L) (block_unit245Q L hL)
      (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0)) (integerReal (w j : Fin 10 → ℤ)) =
        sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
          (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0) (weightp245P c2) (weightp245P c3) j)
    (hpowered : sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
        (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0) (weightp245P c2) (weightp245P c3) 8 <
      sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
        (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0) (weightp245P c2) (weightp245P c3) 9*
          (Q^3)^(-(delta/3)))
    (hline : Submodule.span ℚ {lastDual10 (fun j i => ((w j : Fin 10 → ℤ) i : ℚ))
      (integer_frame_rational_independent10 _ hw)} = Submodule.span ℚ {fun i => (b i : ℚ)}) :
    ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
      (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c0)
        (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ∧
      (∀ i, second245Q b i = 0) ∧
      (∀ j : Fin 4, originalNormal245U b (fun i => ((u j.castSucc : Fin 5 → ℤ) i : ℚ)) = 0) := by
  obtain ⟨u,hu,hpos,hmono,ha,hpoint⟩ := exists_sourceMinima5_attaining A2 A3 L hL Q hQ c0 c2 c3
  let nu := sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
    (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0) (weightp245P c2) (weightp245P c3)
  have hnu : 0 < nu 9 := (sourceMinima10_pos_mono (block245P A2) (block245P A3)
    (block245P L) (block_unit245Q L hL) (Q^3) (powered_gt_one3242 Q hQ)
    (weight0245P c0) (weightp245P c2) (weightp245P c3)).1 9
  have hp1 := Real.rpow_lt_one_of_one_lt_of_neg (powered_gt_one3242 Q hQ)
    (neg_neg_of_pos (show 0 < delta/3 by positivity))
  have hgap : nu 8 < nu 9 := hpowered.trans_le (mul_le_of_le_one_right hnu.le hp1.le)
  have hpow := Real.rpow_lt_one_of_one_lt_of_neg hQ (neg_neg_of_pos hd)
  have h34 := hsource.trans_le (mul_le_of_le_one_right (hpos 4).le hpow.le)
  have hsmall : Q^2*sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3 < nu 9 :=
    (mul_lt_mul_of_pos_left h34 (sq_pos_of_pos (zero_lt_one.trans hQ))).trans_le
      (source_lower245Q A2 A3 L hL Q hQ c0 c2 c3)
  have hann (z : Fin 10 → ℤ)
      (hz : z ∈ originalSourceGroup10 (block245P A2) (block245P A3) (Q^3)
        (weightp245P c2) (weightp245P c3))
      (hzg : coordinateGauge10 (originalCoordinates10 (block245P L) (block_unit245Q L hL)
        (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0)) (integerReal z) < nu 9) :
      normalForm10 b (fun i => (z i : ℚ)) = 0 := by
    apply rational_annihilation_from_real_span241 (fun j => (w j : Fin 10 → ℤ))
      (integer_frame_rational_independent10 _ hw) b hline z
    exact attaining_short_span241 (block245P A2) (block245P A3) (block245P L)
      (block_unit245Q L hL) (Q^3) (powered_gt_one3242 Q hQ)
      (weight0245P c0) (weightp245P c2) (weightp245P c3) w hw hatt hgap z hz hzg
  have hdummy (i : Fin 5) : second245Q b i = 0 := by
    have hm : join245Q 0 (Pi.single i (1 : ℤ)) ∈
        originalSourceGroup10 (block245P A2) (block245P A3) (Q^3)
          (weightp245P c2) (weightp245P c3) := by
      apply (block_source_group245Q A2 A3 Q c2 c3 _).mpr
      rw [first_join245Q]
      exact (originalSourceGroup5 A2 A3 Q c2 c3).zero_mem
    have hs : coordinateGauge10 (originalCoordinates10 (block245P L) (block_unit245Q L hL)
        (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0))
        (integerReal (join245Q 0 (Pi.single i (1 : ℤ)))) < nu 9 := by
      rw [integerReal_join245Q, map_zero, integerReal_single245R, gauge_dummy245Q L hL Q hQ]
      exact hsep.trans_lt hsmall
    have hh := hann _ hm hs
    rw [normal_dummy245U] at hh
    exact_mod_cast hh
  refine ⟨u,hu,ha,hdummy,?_⟩
  intro j
  have hm : join245Q (u j.castSucc : Fin 5 → ℤ) 0 ∈
      originalSourceGroup10 (block245P A2) (block245P A3) (Q^3)
        (weightp245P c2) (weightp245P c3) := by
    apply (block_source_group245Q A2 A3 Q c2 c3 _).mpr
    rw [first_join245Q]
    exact (u j.castSucc).property
  have hs : coordinateGauge10 (originalCoordinates10 (block245P L) (block_unit245Q L hL)
      (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0))
      (integerReal (join245Q (u j.castSucc : Fin 5 → ℤ) 0)) < nu 9 := by
    rw [integerReal_join245Q, map_zero, gauge_original245Q L hL Q hQ, ha]
    exact (mul_le_mul_of_nonneg_left
      (hmono (show j.castSucc ≤ (3 : Fin 5) by change j.val ≤ 3; omega)) (sq_nonneg Q)).trans_lt hsmall
  have hh := hann _ hm hs
  rw [normal_original245U] at hh
  exact hh

end CompoundFeasibility.BlockRank4_245U
