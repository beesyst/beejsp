import SubspaceBridge.RestrictedFiniteCoordinates4
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedCoordinateCovolume4
open RestrictedGeometry4 RestrictedRelaxed4 RestrictedIntegerCoordinates4
noncomputable section

theorem relaxedLattice4_covolume_index {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    ZLattice.covolume (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃) (restrictedMeasure4 P) =
      ((relaxedIntegerGroup4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃).index : ℝ) *
        ZLattice.covolume (baseLattice4 P) (restrictedMeasure4 P) := by
  let H := relaxedIntegerGroup4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃
  let L := relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃
  let e : H ≃ₗ[ℤ] L := relaxedIntegerEquiv4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃
  letI : Module.Free ℤ H := Module.Free.of_equiv e.symm
  letI : Module.Finite ℤ H := Module.Finite.equiv e.symm
  let bH : Basis (Fin (Module.finrank ℚ P)) ℤ H :=
    Module.finBasisOfFinrankEq ℤ H (relaxedIntegerGroup4_rank P hP A₂ A₃ Q c₂ c₃ s₂ s₃)
  let bL : Basis (Fin (Module.finrank ℚ P)) ℤ L := bH.map e
  letI : DiscreteTopology (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  letI : IsZLattice ℝ (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  let b₀ := baseIntegerBasis4 P hP
  let bR := b₀.ofZLatticeBasis ℝ (baseLattice4 P)
  let U : Matrix (Fin (Module.finrank ℚ P)) (Fin (Module.finrank ℚ P)) ℤ :=
    fun i k => (bH k : Fin (Module.finrank ℚ P) → ℤ) i
  have hcoord : bR.toMatrix (fun k => (bL k : rationalRealSpan4 P)) = U.map (Int.castRingHom ℝ) := by
    ext i k
    change (bR.repr (integerCoordinateMap4 P hP (bH k)) i) = ((bH k : Fin (Module.finrank ℚ P) → ℤ) i : ℝ)
    change ((b₀.ofZLatticeBasis ℝ (baseLattice4 P)).repr
      ((b₀.equivFun.symm (bH k : Fin (Module.finrank ℚ P) → ℤ) : baseLattice4 P) : rationalRealSpan4 P)) i = _
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
  have hfund : (restrictedMeasure4 P).real (ZSpan.fundamentalDomain bR) =
      ZLattice.covolume (baseLattice4 P) (restrictedMeasure4 P) :=
    (ZLattice.covolume_eq_measure_fundamentalDomain (baseLattice4 P) (restrictedMeasure4 P)
      (ZLattice.isAddFundamentalDomain b₀ (restrictedMeasure4 P))).symm
  change ZLattice.covolume L (restrictedMeasure4 P) = _
  rw [ZLattice.covolume_eq_det_mul_measureReal L (restrictedMeasure4 P) bL bR,Basis.det_apply]
  simp only [Function.comp_def]
  rw [hcoord,hindex,hfund]

end
end CompoundFeasibility.RestrictedCoordinateCovolume4
