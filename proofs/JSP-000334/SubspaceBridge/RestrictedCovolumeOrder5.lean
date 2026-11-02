import SubspaceBridge.RestrictedLower5
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedCovolumeOrder5
open RestrictedGeometry5
noncomputable section

theorem covolume_antitone5 (P : Submodule ℚ (Fin 5 → ℚ))
    (L₁ L₂ : Submodule ℤ (rationalRealSpan5 P))
    [DiscreteTopology L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₁] [IsZLattice ℝ L₂]
    (hle : L₁ ≤ L₂) :
    ZLattice.covolume L₂ (restrictedMeasure5 P) ≤ ZLattice.covolume L₁ (restrictedMeasure5 P) := by
  let n := Module.finrank ℝ (rationalRealSpan5 P)
  let b₁ : Basis (Fin n) ℤ L₁ := (Module.finBasis ℤ L₁).reindex (finCongr (ZLattice.rank ℝ L₁))
  let b₂ : Basis (Fin n) ℤ L₂ := (Module.finBasis ℤ L₂).reindex (finCongr (ZLattice.rank ℝ L₂))
  let u : Fin n → L₂ := fun k => Submodule.inclusion hle (b₁ k)
  let T : Matrix (Fin n) (Fin n) ℤ := b₂.toMatrix u
  have hli : LinearIndependent ℤ u :=
    b₁.linearIndependent.map' (Submodule.inclusion hle) (Submodule.ker_inclusion _ _ hle)
  have hT : T.det ≠ 0 := (SourceRelativeIndex6.integer_span_index_det b₂ u hli).2.2
  let bR := b₂.ofZLatticeBasis ℝ L₂
  have hcoord : bR.toMatrix (fun k => (b₁ k : rationalRealSpan5 P)) = T.map (Int.castRingHom ℝ) := by
    ext i k
    change bR.repr (u k : rationalRealSpan5 P) i = (b₂.repr (u k) i : ℝ)
    exact Basis.ofZLatticeBasis_repr_apply ℝ L₂ b₂ (u k) i
  have hfund : (restrictedMeasure5 P).real (ZSpan.fundamentalDomain bR) =
      ZLattice.covolume L₂ (restrictedMeasure5 P) :=
    (ZLattice.covolume_eq_measure_fundamentalDomain L₂ (restrictedMeasure5 P)
      (ZLattice.isAddFundamentalDomain b₂ (restrictedMeasure5 P))).symm
  have hcov : ZLattice.covolume L₁ (restrictedMeasure5 P) =
      |(T.map (Int.castRingHom ℝ)).det| * ZLattice.covolume L₂ (restrictedMeasure5 P) := by
    rw [ZLattice.covolume_eq_det_mul_measureReal L₁ (restrictedMeasure5 P) b₁ bR,Basis.det_apply]
    simp only [Function.comp_def]
    rw [hcoord,hfund]
  have hone : (1 : ℝ) ≤ |(T.map (Int.castRingHom ℝ)).det| := by
    rw [← integer_matrix_det_cast,← Int.cast_abs,← Int.cast_natAbs]
    exact_mod_cast (Int.natAbs_pos.mpr hT)
  rw [hcov]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hone
    (ZLattice.covolume_pos L₂ (restrictedMeasure5 P)).le

end
end CompoundFeasibility.RestrictedCovolumeOrder5
