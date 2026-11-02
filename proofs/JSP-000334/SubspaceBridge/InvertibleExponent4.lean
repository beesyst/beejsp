import SubspaceBridge.RowScaleSelection4
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.InvertibleExponent4
open DetNormalization4 RowScaleSelection4 SelectedRestriction4 RestrictedRows4 RestrictedWeightOrder4
noncomputable section

theorem matrixUnit4 {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K)
    (hA : A.det ≠ 0) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)

theorem rationalRestriction_span4 (P : Submodule ℚ (Fin 4 → ℚ))
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det ≠ 0) :
    Submodule.span ℚ (Set.range (rationalRowCoordinates4 P A).row) = ⊤ :=
  rowCoordinates4_span P _ A (matrixUnit4 A hA)

theorem realRestriction_span4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det ≠ 0) :
    Submodule.span ℝ (Set.range (realRestrictionCoordinates4 P hP L).row) = ⊤ :=
  rowCoordinates4_span _ _ L (matrixUnit4 L hL)

def invertibleSelectedExponent4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det ≠ 0) (h₃ : A₃.det ≠ 0) (hL : L.det ≠ 0)
    (c₀ c₂ c₃ : Fin 4 → ℝ) : ℝ :=
  (∑ k : Fin (Module.finrank ℚ P), c₀ (weightOrder4 c₀
    (selectedIndex4 (realRestrictionCoordinates4 P hP L) c₀ (realRestriction_span4 P hP L hL) k))) +
  (∑ k : Fin (Module.finrank ℚ P), c₂ (weightOrder4 c₂
    (selectedIndex4 (rationalRowCoordinates4 P A₂) c₂ (rationalRestriction_span4 P A₂ h₂) k))) +
  (∑ k : Fin (Module.finrank ℚ P), c₃ (weightOrder4 c₃
    (selectedIndex4 (rationalRowCoordinates4 P A₃) c₃ (rationalRestriction_span4 P A₃ h₃) k)))

theorem invertibleSelectedExponent4_eq_source (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (c₀ c₂ c₃ : Fin 4 → ℝ) :
    invertibleSelectedExponent4 P hP A₂ A₃ L (by rw [h₂];norm_num)
      (by rw [h₃];norm_num) (by rw [hL];norm_num) c₀ c₂ c₃ =
      sourceSelectedExponent4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ := rfl

theorem invertibleSelectedExponent4_normalized (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det ≠ 0) (h₃ : A₃.det ≠ 0) (hL : L.det ≠ 0)
    (c₀ c₂ c₃ : Fin 4 → ℝ) :
    invertibleSelectedExponent4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ =
      sourceSelectedExponent4 P hP (normalizedDet4 A₂) (normalizedDet4 A₃) (normalizedDet4 L)
        (normalizedDet4_det A₂ h₂) (normalizedDet4_det A₃ h₃) (normalizedDet4_det L hL)
        c₀ c₂ c₃ := by
  have e₀ := selectedIndex4_scale (realRestrictionCoordinates4 P hP L)
    (realRestrictionCoordinates4 P hP (normalizedDet4 L)) (detRowMultiplier4 L)
    (detRowMultiplier4_ne_zero L hL)
    (rowCoordinates4_normalized _ _ L) c₀ (realRestriction_span4 P hP L hL)
    (realRestrictionCoordinates4_span P hP (normalizedDet4 L) (normalizedDet4_det L hL))
  have e₂ := selectedIndex4_scale (rationalRowCoordinates4 P A₂)
    (rationalRowCoordinates4 P (normalizedDet4 A₂)) (detRowMultiplier4 A₂)
    (detRowMultiplier4_ne_zero A₂ h₂)
    (rowCoordinates4_normalized _ _ A₂) c₂ (rationalRestriction_span4 P A₂ h₂)
    (rationalRowCoordinates4_span P (normalizedDet4 A₂) (normalizedDet4_det A₂ h₂))
  have e₃ := selectedIndex4_scale (rationalRowCoordinates4 P A₃)
    (rationalRowCoordinates4 P (normalizedDet4 A₃)) (detRowMultiplier4 A₃)
    (detRowMultiplier4_ne_zero A₃ h₃)
    (rowCoordinates4_normalized _ _ A₃) c₃ (rationalRestriction_span4 P A₃ h₃)
    (rationalRowCoordinates4_span P (normalizedDet4 A₃) (normalizedDet4_det A₃ h₃))
  unfold invertibleSelectedExponent4 sourceSelectedExponent4
  rw [e₀,e₂,e₃]

end
end CompoundFeasibility.InvertibleExponent4
