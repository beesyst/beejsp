import SubspaceBridge.RestrictedLower5
open scoped BigOperators
open MeasureTheory
namespace CompoundFeasibility.SelectedBoxVolume5
noncomputable section

def weightedBox5 {d : ℕ} (r : Fin d → ℝ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (-r i) (r i))

theorem weightedBox5_compact_convex {d : ℕ} (r : Fin d → ℝ)
    (e : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ)) :
    IsCompact (e ⁻¹' weightedBox5 r) ∧ Convex ℝ (e ⁻¹' weightedBox5 r) := by
  have hc : IsCompact (weightedBox5 r) := isCompact_univ_pi (fun _ => isCompact_Icc)
  constructor
  · have hh : IsCompact (e.symm '' weightedBox5 r) :=
      hc.image e.symm.toContinuousLinearEquiv.continuous
    simpa only [LinearEquiv.image_eq_preimage,LinearEquiv.symm_symm] using hh
  · exact (convex_pi (fun _ _ => convex_Icc _ _)).linear_preimage e.toLinearMap

theorem weightedBox5_volume {d : ℕ} (r : Fin d → ℝ) (hr : ∀ i, 0 < r i)
    (e : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ)) :
    volume.real (e ⁻¹' weightedBox5 r) =
      (2 : ℝ)^d * (∏ i, r i) / |LinearMap.det e.toLinearMap| := by
  rw [measureReal_def,weightedBox5,Measure.addHaar_preimage_linearEquiv,volume_pi,Measure.pi_pi]
  simp only [Real.volume_Icc,sub_neg_eq_add,← two_mul,
    ENNReal.toReal_mul,ENNReal.toReal_prod,LinearEquiv.det_coe_symm,abs_inv,
    ENNReal.toReal_ofReal,abs_nonneg,div_eq_mul_inv]
  have hnonneg : ∀ i, 0 ≤ 2*r i := fun i => le_of_lt (mul_pos (by norm_num) (hr i))
  simp only [ENNReal.toReal_ofReal (hnonneg _),Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _))]
  ring

end
end CompoundFeasibility.SelectedBoxVolume5
