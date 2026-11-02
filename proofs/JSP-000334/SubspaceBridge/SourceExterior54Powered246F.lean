import SubspaceBridge.SourceExterior54Real246F
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior54_246

theorem powered_gt_one4246 (Q : ℝ) (hQ : 1 < Q) : 1 < Q^4 :=
  one_lt_pow₀ hQ (by decide)

theorem powered_rpow4246 (Q a : ℝ) (hQ : 1 < Q) : (Q^4)^(a/4) = Q^a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_lt_one.trans hQ).le]
  congr 1
  ring

theorem powered_body4246 (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 5 → ℝ) (x : Fin 5 → ℝ) (r : ℝ) :
    coordinateGauge5 (originalCoordinates5 (compound4246 L) (compound_unit4246 L hL)
      (Q^4) (powered_gt_one4246 Q hQ) (normalizedWeights4246 c0)) x ≤ r ↔
      ∀ i, |(compound4246 L *ᵥ x) i| ≤ r * Q^(fourWeights246 c0 i) := by
  change ‖originalCoordinates5 (compound4246 L) (compound_unit4246 L hL)
    (Q^4) (powered_gt_one4246 Q hQ) (normalizedWeights4246 c0) x‖ ≤ r ↔ _
  rw [originalCoordinates5_bounds]
  simp only [normalizedWeights4246, powered_rpow4246 Q _ hQ]

theorem powered_source_wedge4246 (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (x : Fin 4 → Fin 5 → ℤ) (r : Fin 4 → ℝ) (Q : ℝ) (hQ : 1 < Q)
    (c0 : Fin 5 → ℝ)
    (hx : ∀ j k, |(L *ᵥ integerReal (x j)) k| ≤ r j * Q^(c0 k)) :
    coordinateGauge5 (originalCoordinates5 (compound4246 L) (compound_unit4246 L hL)
      (Q^4) (powered_gt_one4246 Q hQ) (normalizedWeights4246 c0))
      (integerReal (wedge4246 x)) ≤ 24 * ∏ j, r j := by
  exact (powered_body4246 L hL Q hQ c0 _ _).mpr
    (real_source_wedge4246 L x r Q hQ c0 hx)

end CompoundFeasibility.Exterior54_246
