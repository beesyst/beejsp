import SubspaceBridge.RestrictedFiniteCoordinates5
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedCoordinateCovolume5
open RestrictedGeometry5 RestrictedRelaxed5 RestrictedIntegerCoordinates5
noncomputable section

theorem relaxedLattice5_covolume_index {d : ℕ} (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4) (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) (s₂ s₃ : Fin d → Fin 5) :
    ZLattice.covolume (relaxedLattice5 P A₂ A₃ Q c₂ c₃ s₂ s₃) (restrictedMeasure5 P) =
      ((relaxedIntegerGroup5 P hP A₂ A₃ Q c₂ c₃ s₂ s₃).index : ℝ) *
        ZLattice.covolume (baseLattice5 P) (restrictedMeasure5 P) := by
  let H := relaxedIntegerGroup5 P hP A₂ A₃ Q c₂ c₃ s₂ s₃
  let L := relaxedLattice5 P A₂ A₃ Q c₂ c₃ s₂ s₃
  let e : H ≃ₗ[ℤ] L := relaxedIntegerEquiv5 P hP A₂ A₃ Q c₂ c₃ s₂ s₃
  letI : Module.Free ℤ H := Module.Free.of_equiv e.symm
  letI : Module.Finite ℤ H := Module.Finite.equiv e.symm
  let bH : Basis (Fin (Module.finrank ℚ P)) ℤ H :=
    Module.finBasisOfFinrankEq ℤ H (relaxedIntegerGroup5_rank P hP A₂ A₃ Q c₂ c₃ s₂ s₃)
  let bL : Basis (Fin (Module.finrank ℚ P)) ℤ L := bH.map e
  letI : DiscreteTopology (baseLattice5 P) := by dsimp only [baseLattice5];infer_instance
  letI : IsZLattice ℝ (baseLattice5 P) := by dsimp only [baseLattice5];infer_instance
  let b₀ := baseIntegerBasis5 P hP
  let bR := b₀.ofZLatticeBasis ℝ (baseLattice5 P)
  let U : Matrix (Fin (Module.finrank ℚ P)) (Fin (Module.finrank ℚ P)) ℤ :=
    fun i k => (bH k : Fin (Module.finrank ℚ P) → ℤ) i
  have hcoord : bR.toMatrix (fun k => (bL k : rationalRealSpan5 P)) = U.map (Int.castRingHom ℝ) := by
    ext i k
    change (bR.repr (integerCoordinateMap5 P hP (bH k)) i) = ((bH k : Fin (Module.finrank ℚ P) → ℤ) i : ℝ)
    change ((b₀.ofZLatticeBasis ℝ (baseLattice5 P)).repr
      ((b₀.equivFun.symm (bH k : Fin (Module.finrank ℚ P) → ℤ) : baseLattice5 P) : rationalRealSpan5 P)) i = _
    rw [Basis.ofZLatticeBasis_repr_apply]
    change (((b₀.equivFun (b₀.equivFun.symm (bH k : Fin (Module.finrank ℚ P) → ℤ))) i : ℤ) : ℝ) = _
    rw [LinearEquiv.apply_symm_apply]
  have hindex : |(U.map (Int.castRingHom ℝ)).det| = (H.index : ℝ) := by
    have h := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin (Module.finrank ℚ P))) H bH
    rw [Basis.det_apply] at h
    have he : (Pi.basisFun ℤ (Fin (Module.finrank ℚ P))).toMatrix
        (fun k => (bH k : Fin (Module.finrank ℚ P) → ℤ)) = U := by rfl
    rw [he] at h
    rw [← integer_matrix_det_cast,← Int.cast_abs,← Int.cast_natAbs,← h]
  have hfund : (restrictedMeasure5 P).real (ZSpan.fundamentalDomain bR) =
      ZLattice.covolume (baseLattice5 P) (restrictedMeasure5 P) :=
    (ZLattice.covolume_eq_measure_fundamentalDomain (baseLattice5 P) (restrictedMeasure5 P)
      (ZLattice.isAddFundamentalDomain b₀ (restrictedMeasure5 P))).symm
  change ZLattice.covolume L (restrictedMeasure5 P) = _
  rw [ZLattice.covolume_eq_det_mul_measureReal L (restrictedMeasure5 P) bL bR,Basis.det_apply]
  simp only [Function.comp_def]
  rw [hcoord,hindex,hfund]

end
end CompoundFeasibility.RestrictedCoordinateCovolume5
