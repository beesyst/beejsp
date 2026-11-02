import SubspaceBridge.OriginalSelectedSystem4
import SubspaceBridge.OriginalDeformedSource4
import SubspaceBridge.SourceBalance6
import SubspaceBridge.SourceMultiblock4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalSelectedInputs4
open OriginalDeformation4 OriginalDeformedSource4 OriginalLastDual4 OriginalAuxiliaryDual4

theorem inverse_coefficients_algebraic4 (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∀ i j, IsAlgebraic ℚ (L⁻¹.transpose i j) := by
  obtain ⟨K,hK,hmem⟩ := liouville4_common_field L hAlg
  letI : FiniteDimensional ℚ K := hK
  letI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  let B : Matrix (Fin 4) (Fin 4) K := fun i j => ⟨L i j,hmem i j⟩
  have hmap : B.map K.val.toRingHom = L := rfl
  have hdet : B.det ≠ 0 := by
    intro hz
    have he := K.val.toRingHom.map_det B
    change (B.det : ℝ) = (B.map K.val.toRingHom).det at he
    rw [hz,hmap,hL] at he
    exact zero_ne_one he
  have hinv := (Auxiliary6.SourceBalance.mapped_inverse K.val.toRingHom B hdet).1
  change B⁻¹.map K.val.toRingHom * L = 1 at hinv
  have he : L⁻¹ = B⁻¹.map K.val.toRingHom := Matrix.inv_eq_left_inv hinv
  intro i j
  rw [Matrix.transpose_apply,he]
  exact IntermediateField.isAlgebraic_iff.mp (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (B⁻¹ j i))

theorem fixed_dual_liouville4 (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ i (z : Fin 4 → ℤ),
      (L⁻¹.transpose *ᵥ integerReal z) i ≠ 0 →
      C ≤ |(L⁻¹.transpose *ᵥ integerReal z) i| *(max 1 ‖integerReal z‖)^D := by
  simpa only [Matrix.mulVec,dotProduct,integerReal] using
    algebraic_fin4_liouville_lower L⁻¹.transpose (inverse_coefficients_algebraic4 L hL hAlg)

theorem source_frame_real_dual_input4
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
    {u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3}
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u) (i : Fin 4) :
    ‖(L⁻¹.transpose *ᵥ
      (fun k => (integerLastDual4 (fun j => (F.w j : Fin 4 → ℤ)) k : ℝ))) i‖ <
      6*(ZLattice.covolume (integerRealImage (originalSourceGroup4 A2 A3 Q c2 c3))/
        deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) F.sigma i)*
        (Q^(5 : ℕ))^(-3*(delta/24)) := by
  have hreal := OriginalDeformedFrame4.deformed_cofactor_decay4 A2 A3 L hL hLdet Q hQ
    c0 c2 c3 _ F.sigma F.deformation_pos F.w F.attaining (delta/24) F.small i
  have hcov := OriginalAuxiliaryGeometry4.balanced_width_product_covolume4 A2 A3 h2 h3 Q hQ
    _ c2 c3 F.balance
  apply hreal.trans_le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    ((div_le_div_iff_of_pos_right (F.widths_pos i)).mpr hcov) (by norm_num)) (by positivity)


def realCofactorForm4 (w : Fin 4 → Fin 4 → ℤ) : Module.Dual ℝ (Fin 4 → ℝ) :=
  ∑ i, (integerLastDual4 w i : ℝ) • LinearMap.proj i

theorem real_cofactor_kernel4 (w : Fin 4 → Fin 4 → ℤ)
    (hw : LinearIndependent ℝ (fun j => integerReal (w j))) :
    LinearMap.ker (realCofactorForm4 w) =
      Submodule.span ℝ (Set.range (fun j : Fin 3 => integerReal (w j.castSucc))) := by
  let b : Basis (Fin 4) ℝ (Fin 4 → ℝ) := basisOfPiSpaceOfLinearIndependent hw
  have hb (j : Fin 4) : b j = integerReal (w j) := congrFun (coe_basisOfPiSpaceOfLinearIndependent hw) j
  have hpair (j : Fin 4) : realCofactorForm4 w (integerReal (w j)) =
      if j = 3 then ((Matrix.det (w : Matrix (Fin 4) (Fin 4) ℤ) : ℤ) : ℝ) else 0 := by
    have hp := integerLastDual4_pairing w j
    have hr : (∑ i, (w j i : ℝ)*(integerLastDual4 w i : ℝ)) =
        if j = 3 then ((Matrix.det (w : Matrix (Fin 4) (Fin 4) ℤ) : ℤ) : ℝ) else 0 := by exact_mod_cast hp
    simpa [realCofactorForm4,integerReal,mul_comm] using hr
  have hd : ((Matrix.det (w : Matrix (Fin 4) (Fin 4) ℤ) : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast integerFrame4_det_ne_zero w (integral_frame_rational_independent w hw)
  have hvalue (x : Fin 4 → ℝ) : realCofactorForm4 w x = b.repr x 3*((Matrix.det (w : Matrix (Fin 4) (Fin 4) ℤ) : ℤ) : ℝ) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum,LinearMap.map_smul,hb,hpair,smul_eq_mul,mul_ite,mul_zero]
    simp
  apply le_antisymm
  · intro x hx
    have hz : b.repr x 3 = 0 := (mul_eq_zero.mp ((hvalue x).symm.trans hx)).resolve_right hd
    have he := b.sum_repr x
    rw [Fin.sum_univ_castSucc,show Fin.last 3 = (3 : Fin 4) from rfl,hz,zero_smul,add_zero] at he
    rw [← he]
    apply Submodule.sum_mem
    intro j _
    rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change realCofactorForm4 w (integerReal (w j.castSucc)) = 0
    rw [hpair,if_neg]
    intro hj
    have := congrArg Fin.val hj
    change j.val = 3 at this
    omega

theorem source_multiblock_kernel_restriction4 {m : ℕ}
    (P : MvPolynomial (SourceMultiblock4.Vars4 m) ℝ)
    (w : Fin m → Fin 4 → Fin 4 → ℤ)
    (hw : ∀ h, LinearIndependent ℝ (fun j => integerReal (w h j)))
    (S : Fin m → Fin 3 → Finset ℝ) (s t r : Fin m → ℕ)
    (hcard : ∀ h j, (S h j).card = s h)
    (hdeg : ∀ d ∈ P.support, ∀ h, (∑ i : Fin 4, d (h,i)) ≤ r h)
    (hsize : ∀ h, r h < s h*(t h+1))
    (hgrid : ∀ a : Fin m → Fin 3 → ℝ, (∀ h j, a h j ∈ S h j) →
      ∀ J : SourceMultiblock4.Vars4 m →₀ ℕ, (∀ h, (∑ i : Fin 4, J (h,i)) ≤ t h) →
      MvPolynomial.eval (SourceMultiblock4.blockFramePoint4
        (fun h j => integerReal (w h j.castSucc)) a) (SourceMultiblock4.derivative4 J P) = 0) :
    ∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realCofactorForm4 (w h))) →
      MvPolynomial.eval (fun u => y u.1 u.2) P = 0 := by
  intro y hy
  apply SourceMultiblock4.multiblock_span_hermite4 P
    (fun h j => integerReal (w h j.castSucc)) S s t r hcard hdeg hsize hgrid y
  intro h
  rw [← real_cofactor_kernel4 (w h) (hw h)]
  exact hy h

end CompoundFeasibility.OriginalSelectedInputs4
