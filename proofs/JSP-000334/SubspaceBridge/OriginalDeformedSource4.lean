import SubspaceBridge.OriginalAuxiliaryGeometry4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalDeformedSource4
open OriginalDeformation4 OriginalLastDual4 OriginalAuxiliaryDual4 OriginalDeformedFrame4 OriginalAuxiliaryGeometry4

structure DeformedAttaining4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ) (delta : ℝ)
    (u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3) where
  deformation_pos : ∀ i, 0 < gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3) i
  sigma : Equiv.Perm (Fin 4)
  w : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3
  real_independent : LinearIndependent ℝ (fun j => integerReal (w j : Fin 4 → ℤ))
  rational_independent : LinearIndependent ℚ (fun j i => ((w j : Fin 4 → ℤ) i : ℚ))
  attaining : ∀ j, coordinateGauge4
    (originalDeformedCoordinates4 L hL Q hQ c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos)
    (integerReal (w j : Fin 4 → ℤ)) = originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3
      (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos j
  minima_pos : ∀ j, 0 < originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3
    (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos j
  minima_mono : Monotone (originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3
    (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos)
  small : originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3
    (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos 2 < (Q^(5 : ℕ))^(-(delta/24))
  widths_pos : ∀ i, 0 < deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma i
  balance : (∏ i, deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma i)*
    (∏ i, Q^(c2 i+c3 i)) = 1
  sizes : ∀ i, deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma i < Q^(5 : ℕ) ∧
    (deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma i)⁻¹ < Q^(5 : ℕ) ∧
    Q^(-c2 i) < Q^(5 : ℕ) ∧ Q^(-c3 i) < Q^(5 : ℕ)
  body : ∀ x, x ∈ parallelepipedBody4 (originalDeformedCoordinates4 L hL Q hQ c0
    (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos) ↔
    ∀ i, |(L *ᵥ x) i| ≤ deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma i
  volume : MeasureTheory.volume.real (parallelepipedBody4 (originalDeformedCoordinates4 L hL Q hQ c0
    (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos)) =
    MeasureTheory.volume.real (originalBody4 L Q c0)
  comparison : ∀ j, gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3) j*
    sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j/16 ≤
      originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3
        (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos j ∧
    originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3
      (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos j ≤
      16*(gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3) j*sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j)
  separation : ∀ j : Fin 4, ∀ z : originalSourceGroup4 A2 A3 Q c2 c3,
    integerReal (z : Fin 4 → ℤ) ∉ minimaFlag4 (fun i => integerReal (u i : Fin 4 → ℤ)) j →
    gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3) j*sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j/16 ≤
      coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c0
        (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos) (integerReal (z : Fin 4 → ℤ))

theorem attaining_of_ready4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ) (delta : ℝ)
    (u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3)
    (hready : deformationReady4 A2 A3 L hL Q hQ c0 c2 c3 delta u) :
    Nonempty (DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u) := by
  rcases hready with ⟨_,_,hd,hprod,hanti,hscaled,sigma,hpos,hbal,hcmp,hvol,hsep,_,_,hsmall,hsizes,hbody,_,_⟩
  obtain ⟨w,hreal,hrat,hp,hm,ha,_⟩ := exists_deformed_attaining4 A2 A3 L hL Q hQ c0 c2 c3 _ sigma hd
  exact ⟨⟨hd,sigma,w,hreal,hrat,ha,hp,hm,hsmall,hpos,hbal,hsizes,hbody,hvol,hcmp,hsep⟩⟩

theorem attaining_first_three4
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
    {u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3}
    (F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u) (j : Fin 3) (i : Fin 4) :
    |(L *ᵥ integerReal (F.w j.castSucc : Fin 4 → ℤ)) i| ≤
      (Q^(5 : ℕ))^(-(delta/24))*deformedWidths4 Q c0
        (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) F.sigma i := by
  have hb := (deformed_gauge_bounds4 L hL Q hQ c0 _ F.sigma F.deformation_pos _ _).mp (F.attaining j.castSucc).le i
  have hsmall := (F.minima_mono (show j.castSucc ≤ (2 : Fin 4) by change j.val ≤ 2; omega)).trans_lt F.small
  exact hb.trans (mul_le_mul_of_nonneg_right hsmall.le (F.widths_pos i).le)

end CompoundFeasibility.OriginalDeformedSource4
