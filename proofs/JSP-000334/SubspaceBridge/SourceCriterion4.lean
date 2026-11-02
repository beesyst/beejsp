import SubspaceBridge.ExponentOrder4
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceCriterion4
open NonrothOppositeGrowth4 SelectedRestriction4 ExponentOrder4
open BoundedWeights4 MinimaPower4 RestrictedGrowth4
noncomputable section

theorem source_nonroth_positive_exponent4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (hn : ¬ OriginalVariableGap4.originalRothProperty4 A₂ A₃ L c₀ c₂ c₃) :
    ∃ P : Submodule ℚ (Fin 4 → ℚ),
      ∃ hP : 1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 3,
        P ≠ ⊤ ∧ 0 < sourceSelectedExponent4 P hP.2 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ := by
  obtain ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints,hselected⟩ :=
    source_restricted_opposite_growth4 A₂ A₃ L h₂ h₃ hL hAlg c₀ c₂ c₃ hc₂ hc₃ hb hn
  obtain ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,
    Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,
    u,hvalues,hflag,hAtt,hEq,hFinalU,hFinalpoints,hFinalsol,hEta,hLowerConst,hQuant,
    cSelected,K,hcSelected,hK,hNew⟩ := hselected
  have hOrder : decayExponent4 j deltaGap ≤ cSelected :=
    exponent_le_of_unbounded_power_bound (originalPreimage4 N V Wfixed) hFinal
      (fun Q hQ => hQV Q hQ.1) (growthConstant4 j C4) K
      (decayExponent4 j deltaGap) cSelected hLowerConst hK (by
        intro Q hQ
        exact (hNew ⟨Q,hQ⟩).2.1.trans (hNew ⟨Q,hQ⟩).2.2)
  refine ⟨P,hPbounds,hproper,?_⟩
  rw [← hcSelected]
  exact hEta.trans_le hOrder

def sourceNonpositiveCriterion4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (c₀ c₂ c₃ : Fin 4 → ℝ) : Prop :=
  ∀ P : Submodule ℚ (Fin 4 → ℚ), 1 ≤ Module.finrank ℚ P →
    ∀ hP : Module.finrank ℚ P ≤ 3,
      sourceSelectedExponent4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ ≤ 0

theorem source_fin4_criterion_implies_roth4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (hCriterion : sourceNonpositiveCriterion4 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃) :
    OriginalVariableGap4.originalRothProperty4 A₂ A₃ L c₀ c₂ c₃ := by
  by_contra hn
  obtain ⟨P,hP,hproper,hpos⟩ := source_nonroth_positive_exponent4 A₂ A₃ L h₂ h₃ hL hAlg
    c₀ c₂ c₃ hc₂ hc₃ hb hn
  exact (not_lt_of_ge (hCriterion P hP.1 hP.2)) hpos

end
end CompoundFeasibility.SourceCriterion4
