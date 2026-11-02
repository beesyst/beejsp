import SubspaceBridge.OriginalAttainmentTransport4
import SubspaceBridge.OriginalAttainmentPrefix4
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.NonrothAttainmentFlag4
open Exterior3 OriginalLastDual4 OriginalFlagAssembly4 BoundedWeights4 OriginalAttainmentFlag4 OriginalAttainmentTransport4
noncomputable section

def selectedAttainingExceptionalFlag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
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
            ∃ hPbounds : 1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 3, P ≠ ⊤ ∧
            ∃ v : (r : Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ r.val (scaledWeights4 N c₂) (scaledWeights4 N c₃),
              (∀ r : Wfixed, P = originalFirstFlag4 j.succ (fun i => (v r i : Fin 4 → ℤ))) ∧
              (∀ r : Wfixed, ambientFrame4 A₂ A₃ L (sourceUnit42 L hL) r.val (hWR r.val (hWsub r.property))
                (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) (v r)) ∧
              originalPreimage4 N V Wfixed ⊆ V ∧ ¬ BddAbove (originalPreimage4 N V Wfixed) ∧
              ∃ u : (q : originalPreimage4 N V Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
                (∀ q i, (u q i : Fin 4 → ℤ) = (v ⟨q.val^N,q.property.2⟩ i : Fin 4 → ℤ)) ∧
                (∀ q, P = originalFirstFlag4 j.succ (fun i => (u q i : Fin 4 → ℤ))) ∧
                (∀ q : originalPreimage4 N V Wfixed, ambientFrame4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1)
                  c₀ c₂ c₃ (u q)) ∧
                (∀ (q : originalPreimage4 N V Wfixed) (k : Fin (Module.finrank ℚ P)),
                  RestrictedGeometry4.restrictedMinima4 P A₂ A₃ L (sourceUnit42 L hL) q.val
                    (hQV q.val q.property.1) c₀ c₂ c₃ k =
                  sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃
                    (RestrictedGeometry4.ambientPrefixIndex4 P hPbounds.2 k)) ∧
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

theorem source_selected_attaining_exceptional_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
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
    : selectedAttainingExceptionalFlag4 A₂ A₃ L hL c₀ c₂ c₃ epsilon delta c4 C4 B U V j hQV := by
  obtain ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,
    Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,u,hvalues,hflag,hAtt⟩ :=
    source_bounded_weights_attaining_flag4 A₂ A₃ L h₂ h₃ hL hAlg c₀ c₂ c₃ hc₂ hc₃ hb
      delta hd V hV hQV j (fun Q hq => (hpoints Q hq).2)
  obtain ⟨_,hFinalU,hFinalpoints,hFinalsol⟩ := NonrothFixedFlag4.source_preimage_evidence4 A₂ A₃ L hL c₀ c₂ c₃
    epsilon delta c4 C4 B U V j hVU hQV hpoints hsol hprod N Wfixed
  refine ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,?_⟩
  refine ⟨Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,?_⟩
  refine ⟨u,hvalues,hflag,hAtt,?_,hFinalU,hFinalpoints,hFinalsol⟩
  intro q
  exact source_same_frame_restricted_prefix4 P hPbounds.2 j.succ hPdim A₂ A₃ L
    (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ (u q) (hAtt q) (hflag q)

theorem source_nonroth_attaining_fixed_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
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
        selectedAttainingExceptionalFlag4 A₂ A₃ L hL c₀ c₂ c₃ epsilon deltaGap c4 C4 B U V j hQV := by
  obtain ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints⟩ :=
    OriginalFlagAssembly4.source_normalized_nonroth_gap4 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ hc₂ hc₃ hb hn
  refine ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints,?_⟩
  exact source_selected_attaining_exceptional_flag4 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ hAlg hc₂ hc₃ hb
    epsilon deltaGap c4 C4 B hd U V j hVU hV hQV hpoints hsol hprod

theorem selectedAttainingExceptionalFlag4_forget
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (epsilon delta c4 C4 B : ℝ) (U V : Set ℝ) (j : Fin 3)
    (hQV : ∀ Q ∈ V, 1 < Q)
    (h : selectedAttainingExceptionalFlag4 A₂ A₃ L hL c₀ c₂ c₃ epsilon delta c4 C4 B U V j hQV) :
    NonrothFixedFlag4.selectedExceptionalFlag4 A₂ A₃ L hL c₀ c₂ c₃ epsilon delta c4 C4 B U V j hQV := by
  obtain ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,
    Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,
    u,hvalues,hflag,hAtt,hEq,hFinalU,hFinalpoints,hFinalsol⟩ := h
  refine ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,?_⟩
  refine ⟨Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hFinalV,hFinal,?_⟩
  exact ⟨u,hvalues,hflag,hFinalU,hFinalpoints,hFinalsol⟩

theorem source_original_restricted_prefix_eq4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (hn : ¬ OriginalVariableGap4.originalRothProperty4 A₂ A₃ L c₀ c₂ c₃) :
    ∃ (W : Set ℝ) (hQW : ∀ Q ∈ W, 1 < Q), ¬ BddAbove W ∧
      ∃ P : Submodule ℚ (Fin 4 → ℚ),
        ∃ hPbounds : 1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 3,
          P ≠ ⊤ ∧ ∃ d : Fin 4, Module.finrank ℚ P = d.val ∧
            ∃ u : (q : W) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
              (∀ q : W, P = originalFirstFlag4 d (fun i => (u q i : Fin 4 → ℤ))) ∧
              (∀ q : W, ambientFrame4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQW q.val q.property)
                c₀ c₂ c₃ (u q)) ∧
              ∀ (q : W) (k : Fin (Module.finrank ℚ P)),
                RestrictedGeometry4.restrictedMinima4 P A₂ A₃ L (sourceUnit42 L hL) q.val
                  (hQW q.val q.property) c₀ c₂ c₃ k =
                sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQW q.val q.property) c₀ c₂ c₃
                  (RestrictedGeometry4.ambientPrefixIndex4 P hPbounds.2 k) := by
  obtain ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints,hselected⟩ :=
    source_nonroth_attaining_fixed_flag4 A₂ A₃ L h₂ h₃ hL hAlg c₀ c₂ c₃ hc₂ hc₃ hb hn
  obtain ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,
    Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,
    u,hvalues,hflag,hAtt,hEq,hFinalU,hFinalpoints,hFinalsol⟩ := hselected
  exact ⟨originalPreimage4 N V Wfixed,(fun Q hQ => hQV Q hQ.1),hFinal,
    P,hPbounds,hproper,j.succ,hPdim,u,hflag,hAtt,hEq⟩


end
end CompoundFeasibility.NonrothAttainmentFlag4
