import SubspaceBridge.BoundedWeightsTransport4
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.NonrothFixedFlagLiteral189
open Exterior3 OriginalLastDual4 OriginalFlagAssembly4 BoundedWeights4
noncomputable section

def selectedExceptionalFlag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (epsilon delta c4 C4 B : ℝ) (U V : Set ℝ) (j : Fin 3) (hQV : ∀ Q ∈ V, 1 < Q) : Prop :=
    ∃ (N : ℕ) (hN : 1 ≤ N),
      (∀ i, |c₀ i| ≤ (N : ℝ) ∧ (-(N : ℝ) ≤ c₂ i ∧ c₂ i ≤ 0) ∧ (-(N : ℝ) ≤ c₃ i ∧ c₃ i ≤ 0)) ∧
      (∀ i, |scaledWeights4 N c₀ i| ≤ 1) ∧
      (∀ i, -1 ≤ scaledWeights4 N c₂ i ∧ scaledWeights4 N c₂ i ≤ 0) ∧
      (∀ i, -1 ≤ scaledWeights4 N c₃ i ∧ scaledWeights4 N c₃ i ≤ 0) ∧
      (∑ i, (scaledWeights4 N c₀ i+scaledWeights4 N c₂ i+scaledWeights4 N c₃ i) = 0) ∧
      exactNormalization4 N hN A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ ∧
      0 < delta/(N : ℝ) ∧
      (∀ Q ∈ V, Q^(-delta) = (Q^N)^(-(delta/(N : ℝ)))) ∧
      ¬ BddAbove (powerImage4 N V) ∧
      ∃ hWR : ∀ R ∈ powerImage4 N V, 1 < R,
        (∀ (R : ℝ) (hR : R ∈ powerImage4 N V),
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) R (hWR R hR)
            (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.castSucc <
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) R (hWR R hR)
            (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.succ*R^(-(delta/(N : ℝ)))) ∧
        ∃ (Wfixed : Set ℝ) (hWsub : Wfixed ⊆ powerImage4 N V), ¬ BddAbove Wfixed ∧
          ∃ P : Submodule ℚ (Fin 4 → ℚ), Module.finrank ℚ P = j.val+1 ∧
            (1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 3) ∧ P ≠ ⊤ ∧
            ∃ v : (r : Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ r.val (scaledWeights4 N c₂) (scaledWeights4 N c₃),
              (∀ r : Wfixed, P = originalFirstFlag4 j.succ (fun i => (v r i : Fin 4 → ℤ))) ∧
              originalPreimage4 N V Wfixed ⊆ V ∧ ¬ BddAbove (originalPreimage4 N V Wfixed) ∧
              ∃ u : (q : originalPreimage4 N V Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
                (∀ q i, (u q i : Fin 4 → ℤ) = (v ⟨q.val^N,q.property.2⟩ i : Fin 4 → ℤ)) ∧
                (∀ q, P = originalFirstFlag4 j.succ (fun i => (u q i : Fin 4 → ℤ))) ∧
                originalPreimage4 N V Wfixed ⊆ U ∧
                (∀ q : originalPreimage4 N V Wfixed,
                  1 < q.val ∧ B < q.val ∧
                  sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ j.castSucc <
                    sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ j.succ*q.val^(-delta) ∧
                  c4 ≤ (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ i) ∧
                  (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ i) ≤ C4) ∧
                (∀ Q ∈ originalPreimage4 N V Wfixed, ∃ hQ : 1 < Q, ∃ x : Fin 4 → ℤ,
                  OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x ∧
                  x ∈ originalSourceGroup4 A₂ A₃ Q c₂ c₃ ∧
                  coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) Q hQ c₀) (integerReal x) ≤ Q^(-epsilon) ∧
                  sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 0 < Q^(-(epsilon/2)))

theorem source_preimage_evidence4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (epsilon delta c4 C4 B : ℝ) (U V : Set ℝ) (j : Fin 3) (hVU : V ⊆ U)
    (hQV : ∀ Q ∈ V, 1 < Q)
    (hpoints : ∀ (Q : ℝ) (hq : Q ∈ V), B < Q ∧
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.castSucc <
        sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.succ*Q^(-delta))
    (hsol : ∀ Q ∈ U, ∃ hQ : 1 < Q, ∃ x : Fin 4 → ℤ,
      OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x ∧
      x ∈ originalSourceGroup4 A₂ A₃ Q c₂ c₃ ∧
      coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) Q hQ c₀) (integerReal x) ≤ Q^(-epsilon) ∧
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 0 < Q^(-(epsilon/2)))
    (hprod : ∀ (Q : ℝ) (hQ : 1 < Q),
      c4 ≤ (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) ∧
      (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) ≤ C4)
    (N : ℕ) (Wfixed : Set ℝ) :
    originalPreimage4 N V Wfixed ⊆ V ∧ originalPreimage4 N V Wfixed ⊆ U ∧
      (∀ q : originalPreimage4 N V Wfixed,
        1 < q.val ∧ B < q.val ∧
        sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ j.castSucc <
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ j.succ*q.val^(-delta) ∧
        c4 ≤ (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ i) ∧
        (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ i) ≤ C4) ∧
      (∀ Q ∈ originalPreimage4 N V Wfixed, ∃ hQ : 1 < Q, ∃ x : Fin 4 → ℤ,
        OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x ∧
        x ∈ originalSourceGroup4 A₂ A₃ Q c₂ c₃ ∧
        coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) Q hQ c₀) (integerReal x) ≤ Q^(-epsilon) ∧
        sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 0 < Q^(-(epsilon/2))) := by
  refine ⟨fun _ h => h.1,fun _ h => hVU h.1,?_,fun Q h => hsol Q (hVU h.1)⟩
  intro q
  exact ⟨hQV q.val q.property.1,(hpoints q.val q.property.1).1,
    (hpoints q.val q.property.1).2,hprod q.val (hQV q.val q.property.1)⟩

theorem source_selected_exceptional_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (epsilon delta c4 C4 B : ℝ) (hd : 0 < delta) (U V : Set ℝ) (j : Fin 3) (hVU : V ⊆ U) (hV : ¬ BddAbove V)
    (hQV : ∀ Q ∈ V, 1 < Q)
    (hpoints : ∀ (Q : ℝ) (hq : Q ∈ V), B < Q ∧
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.castSucc <
        sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.succ*Q^(-delta))
    (hsol : ∀ Q ∈ U, ∃ hQ : 1 < Q, ∃ x : Fin 4 → ℤ,
      OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x ∧
      x ∈ originalSourceGroup4 A₂ A₃ Q c₂ c₃ ∧
      coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) Q hQ c₀) (integerReal x) ≤ Q^(-epsilon) ∧
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 0 < Q^(-(epsilon/2)))
    (hprod : ∀ (Q : ℝ) (hQ : 1 < Q),
      c4 ≤ (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) ∧
      (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) ≤ C4)
    : selectedExceptionalFlag4 A₂ A₃ L hL c₀ c₂ c₃ epsilon delta c4 C4 B U V j hQV := by
  obtain ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,
    Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hFinalV,hFinal,u,hvalues,hflag⟩ :=
    BoundedWeights4.source_bounded_weights_fixed_flag4 A₂ A₃ L h₂ h₃ hL hAlg c₀ c₂ c₃ hc₂ hc₃ hb
      delta hd V hV hQV j (fun Q hq => (hpoints Q hq).2)
  obtain ⟨_,hFinalU,hFinalpoints,hFinalsol⟩ := source_preimage_evidence4 A₂ A₃ L hL c₀ c₂ c₃
    epsilon delta c4 C4 B U V j hVU hQV hpoints hsol hprod N Wfixed
  refine ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,?_⟩
  refine ⟨Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hFinalV,hFinal,?_⟩
  exact ⟨u,hvalues,hflag,hFinalU,hFinalpoints,hFinalsol⟩

theorem source_nonroth_fixed_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (hn : ¬ OriginalVariableGap4.originalRothProperty4 A₂ A₃ L c₀ c₂ c₃) :
    ∃ epsilon deltaGap c4 C4 B : ℝ, ∃ U V : Set ℝ, ∃ j : Fin 3,
      0 < epsilon ∧ deltaGap = (epsilon/2)/4 ∧ 0 < deltaGap ∧
      0 < c4 ∧ 0 < C4 ∧ 1 < B ∧
      U = {Q : ℝ | ∃ x : Fin 4 → ℤ,
        OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x} ∧
      ¬ BddAbove U ∧
      (∀ Q ∈ U, ∃ hQ : 1 < Q, ∃ x : Fin 4 → ℤ,
        OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x ∧
        x ∈ originalSourceGroup4 A₂ A₃ Q c₂ c₃ ∧
        coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) Q hQ c₀) (integerReal x) ≤ Q^(-epsilon) ∧
        sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 0 < Q^(-(epsilon/2))) ∧
      (∀ (Q : ℝ) (hQ : 1 < Q),
        c4 ≤ (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) ∧
        (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) ≤ C4) ∧
      V ⊆ U ∧ ¬ BddAbove V ∧
      ∃ hQV : ∀ Q ∈ V, 1 < Q,
        (∀ (Q : ℝ) (hq : Q ∈ V), B < Q ∧
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.castSucc <
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.succ*Q^(-deltaGap)) ∧
        selectedExceptionalFlag4 A₂ A₃ L hL c₀ c₂ c₃ epsilon deltaGap c4 C4 B U V j hQV := by
  obtain ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints⟩ :=
    OriginalFlagAssembly4.source_normalized_nonroth_gap4 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ hc₂ hc₃ hb hn
  refine ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints,?_⟩
  exact source_selected_exceptional_flag4 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ hAlg hc₂ hc₃ hb
    epsilon deltaGap c4 C4 B hd U V j hVU hV hQV hpoints hsol hprod

end
end CompoundFeasibility.NonrothFixedFlagLiteral189

set_option pp.all true

#print axioms CompoundFeasibility.NonrothFixedFlagLiteral189.selectedExceptionalFlag4

#print axioms CompoundFeasibility.NonrothFixedFlagLiteral189.source_preimage_evidence4

#print axioms CompoundFeasibility.NonrothFixedFlagLiteral189.source_selected_exceptional_flag4

#print axioms CompoundFeasibility.NonrothFixedFlagLiteral189.source_nonroth_fixed_flag4
