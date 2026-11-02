import SubspaceBridge.RestrictedAttainment5
open MeasureTheory
noncomputable section
namespace CompoundFeasibility.RestrictedGeometry5
variable {P : Submodule ℚ (Fin 5 → ℚ)}
variable {A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ} {Q : ℝ} {c₂ c₃ : Fin 5 → ℝ} {d : ℕ}

theorem restrictedBasis5_map_addHaar
    (c : Basis (Fin d) ℤ (restrictedLattice5 P A₂ A₃ Q c₂ c₃)) :
    Measure.map (c.ofZLatticeBasis ℝ _).equivFun
      (c.ofZLatticeBasis ℝ _).addHaar = volume := by
  let b := c.ofZLatticeBasis ℝ (restrictedLattice5 P A₂ A₃ Q c₂ c₃)
  have heq : b.map b.equivFunL.toLinearEquiv = Pi.basisFun ℝ (Fin d) := by
    ext i j
    simp [Basis.map_apply,Basis.equivFun_apply,Pi.basisFun_apply,Finsupp.single_apply,Pi.single_apply,eq_comm]
  change Measure.map b.equivFunL b.addHaar = volume
  rw [Basis.map_addHaar b b.equivFunL,heq,Basis.addHaar_def,
    Basis.parallelepiped_basisFun,MeasureTheory.addHaarMeasure_eq_volume_pi]

theorem restrictedBasis5_measure_eq_covolume_smul
    (c : Basis (Fin d) ℤ (restrictedLattice5 P A₂ A₃ Q c₂ c₃)) :
    restrictedMeasure5 P =
      ENNReal.ofReal (ZLattice.covolume (restrictedLattice5 P A₂ A₃ Q c₂ c₃)
        (restrictedMeasure5 P)) • (c.ofZLatticeBasis ℝ _).addHaar := by
  let b := c.ofZLatticeBasis ℝ (restrictedLattice5 P A₂ A₃ Q c₂ c₃)
  let mu := restrictedMeasure5 P
  have hcv : ENNReal.ofReal (ZLattice.covolume (restrictedLattice5 P A₂ A₃ Q c₂ c₃) mu) =
      mu (_root_.parallelepiped b) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ mu (ZLattice.isAddFundamentalDomain c mu)]
    change ENNReal.ofReal (mu (ZSpan.fundamentalDomain b)).toReal = _
    rw [ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne,
      measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b mu)]
  have h := Measure.addHaarMeasure_unique mu b.parallelepiped
  rw [← Basis.addHaar_def] at h
  change mu = _
  rw [hcv]
  exact h

theorem restrictedBasis5_volume_ratio
    (c : Basis (Fin d) ℤ (restrictedLattice5 P A₂ A₃ Q c₂ c₃))
    (C : Set (rationalRealSpan5 P)) (hC : IsCompact C) :
    volume.real ((c.ofZLatticeBasis ℝ _).equivFun '' C) =
      (restrictedMeasure5 P).real C /
        ZLattice.covolume (restrictedLattice5 P A₂ A₃ Q c₂ c₃) (restrictedMeasure5 P) := by
  let b := c.ofZLatticeBasis ℝ (restrictedLattice5 P A₂ A₃ Q c₂ c₃)
  have himage : volume (b.equivFun '' C) = b.addHaar C := by
    rw [← restrictedBasis5_map_addHaar c]
    change (Measure.map b.equivFunL b.addHaar) (b.equivFunL '' C) = b.addHaar C
    rw [Measure.map_apply b.equivFunL.continuous.measurable (hC.image b.equivFunL.continuous).measurableSet,
      Set.preimage_image_eq _ b.equivFunL.injective]
  have hcv := restrictedLattice5_covolume_pos P A₂ A₃ Q c₂ c₃
  change (volume (b.equivFun '' C)).toReal = _
  rw [himage]
  apply (eq_div_iff hcv.ne').mpr
  have heq := congrArg (fun mu : Measure (rationalRealSpan5 P) => mu.real C)
    (restrictedBasis5_measure_eq_covolume_smul c)
  simpa [measureReal_def,Measure.smul_apply,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hcv.le,mul_comm,b] using heq.symm


end CompoundFeasibility.RestrictedGeometry5
