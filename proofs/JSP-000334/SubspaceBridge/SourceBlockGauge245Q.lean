import SubspaceBridge.SourceBlockLattice245Q
import SubspaceBridge.SourceExterior53Normalize242
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.BlockReduction245Q
open BlockReduction245P Exterior53_242

theorem coordinate_left245Q (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin 5 → ℝ) (z : Fin 10 → ℝ) (i : Fin 5) :
    originalCoordinates10 (block245P L) (block_unit245Q L hL) (Q^3)
      (powered_gt_one3242 Q hQ) (weight0245P c) z (blockIndex245P (Sum.inl i)) =
      Q^2*originalCoordinates5 L hL Q hQ c (first245Q z) i := by
  have hq : 0 < Q := zero_lt_one.trans hQ
  have hp : (Q^3)^((c i-2)/3) = Q^(c i)/(Q^2) := by
    have hh := powered_rpow3242 Q (c i-2) 0 0 hQ
    simpa only [add_zero,Real.rpow_sub hq,Real.rpow_two] using hh
  change (block245P L *ᵥ z) (blockIndex245P (Sum.inl i)) /
    (Q^3)^(weight0245P c (blockIndex245P (Sum.inl i))) =
      Q^2*((L *ᵥ first245Q z) i/Q^(c i))
  rw [block_mulVec_left245Q]
  simp only [weight0245P,Equiv.symm_apply_apply,Sum.elim_inl]
  rw [hp]
  field_simp
  ring

theorem coordinate_right245Q (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin 5 → ℝ) (z : Fin 10 → ℝ) (i : Fin 5) :
    originalCoordinates10 (block245P L) (block_unit245Q L hL) (Q^3)
      (powered_gt_one3242 Q hQ) (weight0245P c) z (blockIndex245P (Sum.inr i)) =
      (Q^2)⁻¹*second245Q z i := by
  have hp : (Q^3)^((2 : ℝ)/3) = Q^2 := by
    simpa only [add_zero,Real.rpow_two] using powered_rpow3242 Q 2 0 0 hQ
  change (block245P L *ᵥ z) (blockIndex245P (Sum.inr i)) /
    (Q^3)^(weight0245P c (blockIndex245P (Sum.inr i))) = _
  rw [block_mulVec_right245Q]
  simp only [weight0245P,Equiv.symm_apply_apply,Sum.elim_inr]
  rw [hp]
  ring

theorem norm_join245Q (x y : Fin 5 → ℝ) : ‖join245Q x y‖ = max ‖x‖ ‖y‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonempty _).mpr
    intro j
    obtain ⟨s,rfl⟩ := blockIndex245P.surjective j
    cases s with
    | inl i => simpa only [join245Q,Equiv.symm_apply_apply,Sum.elim_inl] using
        (norm_le_pi_norm x i).trans (le_max_left ‖x‖ ‖y‖)
    | inr i => simpa only [join245Q,Equiv.symm_apply_apply,Sum.elim_inr] using
        (norm_le_pi_norm y i).trans (le_max_right ‖x‖ ‖y‖)
  · apply max_le
    · apply (pi_norm_le_iff_of_nonempty _).mpr
      intro i
      simpa only [join245Q,Equiv.symm_apply_apply,Sum.elim_inl] using
        norm_le_pi_norm (join245Q x y) (blockIndex245P (Sum.inl i))
    · apply (pi_norm_le_iff_of_nonempty _).mpr
      intro i
      simpa only [join245Q,Equiv.symm_apply_apply,Sum.elim_inr] using
        norm_le_pi_norm (join245Q x y) (blockIndex245P (Sum.inr i))

theorem gauge_full245Q (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin 5 → ℝ) (z : Fin 10 → ℝ) :
    coordinateGauge10 (originalCoordinates10 (block245P L) (block_unit245Q L hL)
      (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c)) z =
      max (Q^2*coordinateGauge5 (originalCoordinates5 L hL Q hQ c) (first245Q z))
        ((Q^2)⁻¹*‖second245Q z‖) := by
  have he : originalCoordinates10 (block245P L) (block_unit245Q L hL)
      (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c) z =
      join245Q (Q^2 • originalCoordinates5 L hL Q hQ c (first245Q z))
        ((Q^2)⁻¹ • second245Q z) := by
    ext j
    obtain ⟨s,rfl⟩ := blockIndex245P.surjective j
    cases s with
    | inl i => simpa only [join245Q,Equiv.symm_apply_apply,Sum.elim_inl,
        Pi.smul_apply,smul_eq_mul] using coordinate_left245Q L hL Q hQ c z i
    | inr i => simpa only [join245Q,Equiv.symm_apply_apply,Sum.elim_inr,
        Pi.smul_apply,smul_eq_mul] using coordinate_right245Q L hL Q hQ c z i
  change ‖originalCoordinates10 _ _ _ _ _ z‖ = _
  rw [he,norm_join245Q,norm_smul,norm_smul]
  simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg Q),
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg Q)),coordinateGauge5]

theorem gauge_original245Q (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin 5 → ℝ) (x : Fin 5 → ℝ) :
    coordinateGauge10 (originalCoordinates10 (block245P L) (block_unit245Q L hL)
      (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c)) (join245Q x 0) =
      Q^2*coordinateGauge5 (originalCoordinates5 L hL Q hQ c) x := by
  rw [gauge_full245Q L hL Q hQ,first_join245Q,second_join245Q,norm_zero,mul_zero]
  exact max_eq_left (mul_nonneg (sq_nonneg Q) (norm_nonneg _))

theorem gauge_dummy245Q (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin 5 → ℝ) (i : Fin 5) :
    coordinateGauge10 (originalCoordinates10 (block245P L) (block_unit245Q L hL)
      (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c))
      (join245Q 0 (Pi.single i 1)) = (Q^2)⁻¹ := by
  rw [gauge_full245Q L hL Q hQ,first_join245Q,second_join245Q]
  simp only [coordinateGauge5,map_zero,norm_zero,mul_zero,Pi.norm_single,norm_one,mul_one]
  exact max_eq_right (inv_nonneg.mpr (sq_nonneg Q))

theorem gauge_projection245Q (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin 5 → ℝ) (z : Fin 10 → ℝ) :
    Q^2*coordinateGauge5 (originalCoordinates5 L hL Q hQ c) (first245Q z) ≤
      coordinateGauge10 (originalCoordinates10 (block245P L) (block_unit245Q L hL)
        (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c)) z := by
  rw [gauge_full245Q L hL Q hQ]
  exact le_max_left _ _

end CompoundFeasibility.BlockReduction245Q
