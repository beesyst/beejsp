import SubspaceBridge.NonrothOppositeGrowth5
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceCriterion5
open OriginalVariableGap5 SelectedRestriction5

theorem source_nonroth_positive_exponent5
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c0 c2 c3 : Fin 5 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (hn : ¬ originalRothProperty5 A2 A3 L c0 c2 c3) :
    ∃ P : Submodule ℚ (Fin 5 → ℚ), ∃ hP : 1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 4,
      P ≠ ⊤ ∧ 0 < sourceSelectedExponent5 P hP.2 A2 A3 L h2d h3d hLd c0 c2 c3 := by
  obtain ⟨hL,epsilon,deltaGap,c5,C5,B,U,V,j,he,hdEq,hd,hc,hC,hB,hUeq,hU,hsol,hproduct,
    hVU,hV,hjlo,hjhi,hg,hq,P,hP,hPb,hPt,hPbounds,W,hWV,hW,hWU,hEta,hK,K2,hK2,hCompare,hPositive,hframes⟩ :=
    OriginalFlagAssembly5.source_nonroth_selected_opposite_growth5 A2 A3 L h2d h3d hLd hAlg c0 c2 c3 hc0 hc2 hc3 hb hn
  exact ⟨P,hPbounds,hPt,hPositive⟩

def sourceNonpositiveCriterion5
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1) (c0 c2 c3 : Fin 5 → ℝ) : Prop :=
  ∀ P : Submodule ℚ (Fin 5 → ℚ), 1 ≤ Module.finrank ℚ P → ∀ hP : Module.finrank ℚ P ≤ 4,
    sourceSelectedExponent5 P hP A2 A3 L h2d h3d hLd c0 c2 c3 ≤ 0

theorem source_fin5_criterion_implies_roth5
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c0 c2 c3 : Fin 5 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (hCriterion : sourceNonpositiveCriterion5 A2 A3 L h2d h3d hLd c0 c2 c3) :
    originalRothProperty5 A2 A3 L c0 c2 c3 := by
  by_contra hn
  obtain ⟨P,hP,hproper,hpos⟩ := source_nonroth_positive_exponent5 A2 A3 L h2d h3d hLd hAlg c0 c2 c3 hc0 hc2 hc3 hb hn
  exact (not_lt_of_ge (hCriterion P hP.1 hP.2)) hpos

end CompoundFeasibility.SourceCriterion5
