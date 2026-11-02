import SubspaceBridge.InvertibleExponent4
import SubspaceBridge.NormalizationTransport4
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.InvertibleCriterion4
open DetNormalization4 InvertibleExponent4 SourceCriterion4 NormalizationTransport4
noncomputable section

def sourceInvertibleNonpositiveCriterion4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det ≠ 0) (h₃ : A₃.det ≠ 0) (hL : L.det ≠ 0)
    (c₀ c₂ c₃ : Fin 4 → ℝ) : Prop :=
  ∀ P : Submodule ℚ (Fin 4 → ℚ), 1 ≤ Module.finrank ℚ P →
    ∀ hP : Module.finrank ℚ P ≤ 3,
      invertibleSelectedExponent4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ ≤ 0

theorem sourceInvertibleNonpositiveCriterion4_iff_normalized
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : A₂.det ≠ 0) (h₃ : A₃.det ≠ 0) (hL : L.det ≠ 0) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    sourceInvertibleNonpositiveCriterion4 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ ↔
      sourceNonpositiveCriterion4 (normalizedDet4 A₂) (normalizedDet4 A₃) (normalizedDet4 L)
        (normalizedDet4_det A₂ h₂) (normalizedDet4_det A₃ h₃) (normalizedDet4_det L hL)
        c₀ c₂ c₃ := by
  unfold sourceInvertibleNonpositiveCriterion4 sourceNonpositiveCriterion4
  simp_rw [invertibleSelectedExponent4_normalized]

theorem source_invertible_fin4_criterion_implies_roth4
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : A₂.det ≠ 0) (h₃ : A₃.det ≠ 0) (hL : L.det ≠ 0)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (hCriterion : sourceInvertibleNonpositiveCriterion4 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃) :
    OriginalVariableGap4.originalRothProperty4 A₂ A₃ L c₀ c₂ c₃ := by
  have hn := source_fin4_criterion_implies_roth4 (normalizedDet4 A₂) (normalizedDet4 A₃)
    (normalizedDet4 L) (normalizedDet4_det A₂ h₂) (normalizedDet4_det A₃ h₃)
    (normalizedDet4_det L hL) (normalizedDet4_algebraic L hAlg) c₀ c₂ c₃ hc₂ hc₃ hb
    ((sourceInvertibleNonpositiveCriterion4_iff_normalized A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃).mp hCriterion)
  exact originalRothProperty4_of_normalized A₂ A₃ L c₀ c₂ c₃ hn

end
end CompoundFeasibility.InvertibleCriterion4
