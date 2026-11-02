import SubspaceBridge.SourceNormalization236
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceRatioLine236
open OriginalDeformation10 SourceOriginalVariable10 SourceSatz51Entry218

structure DeformedAttaining236
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ) (delta : ℝ)
    (u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3) where
  deformation_pos : ∀ i, 0 < gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3) i
  deformation_product : (∏ i, gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3) i) = 1
  deformation_antitone : Antitone (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3))
  deformed_scales_mono : Monotone (fun i => gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3) i*sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 i)
  sigma : Equiv.Perm (Fin 10)
  w : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3
  real_independent : LinearIndependent ℝ (fun j => integerReal (w j : Fin 10 → ℤ))
  rational_independent : LinearIndependent ℚ (fun j i => ((w j : Fin 10 → ℤ) i : ℚ))
  attaining : ∀ j, coordinateGauge10
    (originalDeformedCoordinates10 L hL Q hQ c0 (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos)
    (integerReal (w j : Fin 10 → ℤ)) = originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3
      (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos j
  minima_pos : ∀ j, 0 < originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3
    (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos j
  minima_mono : Monotone (originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3
    (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos)
  small : originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3
    (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos 8 < (Q^(5 : ℕ))^(-(delta/60))
  widths_pos : ∀ i, 0 < deformedWidths10 Q c0 (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma i
  balance : (∏ i, deformedWidths10 Q c0 (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma i)*
    (∏ i, Q^(c2 i+c3 i)) = 1
  sizes : ∀ i, deformedWidths10 Q c0 (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma i < Q^(5 : ℕ) ∧
    (deformedWidths10 Q c0 (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma i)⁻¹ < Q^(5 : ℕ) ∧
    Q^(-c2 i) < Q^(5 : ℕ) ∧ Q^(-c3 i) < Q^(5 : ℕ)
  body : ∀ x, x ∈ parallelepipedBody10 (originalDeformedCoordinates10 L hL Q hQ c0
    (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos) ↔
    ∀ i, |(L *ᵥ x) i| ≤ deformedWidths10 Q c0 (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma i
  volume : MeasureTheory.volume.real (parallelepipedBody10 (originalDeformedCoordinates10 L hL Q hQ c0
    (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos)) =
    MeasureTheory.volume.real (originalBody10 L Q c0)
  comparison : ∀ j, gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3) j*
    sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 j/1024 ≤
      originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3
        (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos j ∧
    originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3
      (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos j ≤
      1024*(gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3) j*sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 j)
  separation : ∀ j : Fin 10, ∀ z : originalSourceGroup10 A2 A3 Q c2 c3,
    integerReal (z : Fin 10 → ℤ) ∉ minimaFlag10 (fun i => integerReal (u i : Fin 10 → ℤ)) j →
    gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3) j*sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 j/1024 ≤
      coordinateGauge10 (originalDeformedCoordinates10 L hL Q hQ c0
        (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos) (integerReal (z : Fin 10 → ℤ))

  radius_upper : originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3
    (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos 8 ≤
      1024*gapRadius10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)
  small_unpowered : originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3
    (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos 8 < Q^(-5*delta/60)

theorem attaining_of_ready236
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ) (delta : ℝ)
    (u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3)
    (hr : deformationReady10 A2 A3 L hL Q hQ c0 c2 c3 delta u) :
    Nonempty (DeformedAttaining236 A2 A3 L hL Q hQ c0 c2 c3 delta u) := by
  rcases hr with ⟨_,_,hd,hprod,hanti,hscaled,sigma,hpos,hbal,hcmp,hvol,hsep,hupper,hsmall0,hsmall,hsizes,hbody,_,_⟩
  obtain ⟨w,hw,hp,hm,ha⟩ := exists_deformed_frame236 A2 A3 L hL Q hQ c0 c2 c3 _ sigma hd
  have hrat := SourceOriginalDual10.integer_frame_rational_independent10
    (fun j => (w j : Fin 10 → ℤ)) hw
  exact ⟨⟨hd,hprod,hanti,hscaled,sigma,w,hw,hrat,ha,hp,hm,hsmall,hpos,hbal,hsizes,hbody,hvol,hcmp,hsep,hupper,hsmall0⟩⟩

variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c0 c2 c3 : Fin 10 → ℝ} {delta : ℝ}
  {u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3}

def toSourceData236 (F : DeformedAttaining236 A2 A3 L hL Q hQ c0 c2 c3 delta u) :
    SourceData218 A2 A3 L hL (Q^5) (powered_gt_one236 Q hQ)
      (fun i => c2 i/5) (fun i => c3 i/5)
      (deformedWidths10 Q c0 (gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)) F.sigma)
      (delta/60) where
  positive := F.widths_pos
  sizes := fun i => ⟨(F.sizes i).1,(F.sizes i).2.1⟩
  balance := powered_balance236 Q hQ _ c2 c3 F.balance
  u := fun j => (F.w j : Fin 10 → ℤ)
  member := by
    intro j
    rw [powered_lattice236]
    exact (F.w j).property
  independent := F.real_independent
  attaining := by
    intro j
    rw [normalized_coordinates236 L hL Q hQ c0 _ F.sigma F.deformation_pos,
      normalized_minima236 A2 A3 L hL Q hQ c0 c2 c3 _ F.sigma F.deformation_pos j]
    exact F.attaining j
  small := by
    rw [normalized_minima236 A2 A3 L hL Q hQ c0 c2 c3 _ F.sigma F.deformation_pos 8]
    exact F.small

theorem toSourceData_frame236 (F : DeformedAttaining236 A2 A3 L hL Q hQ c0 c2 c3 delta u) :
    (toSourceData236 F).u = fun j => (F.w j : Fin 10 → ℤ) := rfl

end CompoundFeasibility.SourceRatioLine236
