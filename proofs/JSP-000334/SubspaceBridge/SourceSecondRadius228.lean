import SubspaceBridge.SourceDualRealBasis228
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSecondMinimum228

theorem second_radius_of_dependence228 (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ))
    (hdep : ∀ x y : Fin 10 → ℝ, x ∈ lattice10Span b → y ∈ lattice10Span b →
      coordinateGauge10 e x ≤ 2 → coordinateGauge10 e y ≤ 2 →
      ¬ LinearIndependent ℝ (fun i : Fin 2 => if i = 0 then x else y)) :
    2 ≤ successiveRadius10 b e (1 : Fin 10) := by
  by_contra! hlt
  obtain ⟨v, hv, hvL, _, hmono, hatt, _⟩ := exists_successive_minima10 b e
  have hg0 : coordinateGauge10 e (v 0) ≤ 2 :=
    (hatt 0).le.trans ((hmono (by decide : (0 : Fin 10) ≤ 1)).trans hlt.le)
  have hg1 : coordinateGauge10 e (v 1) ≤ 2 := (hatt 1).le.trans hlt.le
  apply hdep (v 0) (v 1) (hvL 0) (hvL 1) hg0 hg1
  let f : Fin 2 → Fin 10 := Fin.castLE (by decide)
  have he : (fun i : Fin 2 => if i = 0 then v 0 else v 1) = v ∘ f := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact hv.comp f (Fin.castLE_injective _)

end CompoundFeasibility.SourceSecondMinimum228
