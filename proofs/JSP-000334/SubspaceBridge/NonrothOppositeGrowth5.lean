import SubspaceBridge.NonrothVolumeGrowth5
import SubspaceBridge.RestrictedOpposite5
import SubspaceBridge.RestrictedSelectedTies5
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalFlagAssembly5
open OriginalVariableGap5 RestrictedGrowth5 RestrictedOpposite5

theorem source_nonroth_selected_opposite_growth5
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c0 c2 c3 : Fin 5 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (hn : ¬ originalRothProperty5 A2 A3 L c0 c2 c3) :
    ∃ hL : IsUnit L,
    ∃ epsilon deltaGap c5 C5 B : ℝ, ∃ U V : Set ℝ, ∃ j : Fin 4,
      0 < epsilon ∧ deltaGap = (epsilon/2)/5 ∧ 0 < deltaGap ∧
      0 < c5 ∧ 0 < C5 ∧ 1 < B ∧
      U = {Q : ℝ | ∃ x : Fin 5 → ℤ,
        originalSourceSolution5 A2 A3 L c0 c2 c3 Q epsilon x} ∧
      ¬ BddAbove U ∧
      (∀ Q ∈ U, ∃ hQ : 1 < Q, ∃ x : Fin 5 → ℤ,
        originalSourceSolution5 A2 A3 L c0 c2 c3 Q epsilon x ∧
        x ∈ originalSourceGroup5 A2 A3 Q c2 c3 ∧
        coordinateGauge5 (originalCoordinates5 L hL Q hQ c0) (integerReal x) ≤ Q^(-epsilon) ∧
        sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 0 < Q^(-(epsilon/2))) ∧
      (∀ (Q : ℝ) (hQ : 1 < Q),
        c5 ≤ (∏ i : Fin 5, sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ∧
        (∏ i : Fin 5, sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ≤ C5) ∧
      V ⊆ U ∧ ¬ BddAbove V ∧ 1 ≤ j.val+1 ∧ j.val+1 ≤ 4 ∧
      (∀ Q ∈ V, B < Q ∧ ∃ hQ : 1 < Q,
        sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc <
          sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 j.succ * Q^(-deltaGap)) ∧
      ∃ hq : ∀ Q ∈ V, 1 < Q,
      ∃ P : Submodule ℚ (Fin 5 → ℚ), Module.finrank ℚ P = j.val+1 ∧ P ≠ ⊥ ∧ P ≠ ⊤ ∧
      ∃ hPbounds : 1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 4,
      ∃ W : Set ℝ, ∃ hWV : W ⊆ V, ¬ BddAbove W ∧ W ⊆ U ∧
        0 < MinimaPower5.decayExponent5 j deltaGap ∧ 0 < growthConstant5 j C5 ∧
        ∃ K2 : ℝ, 0 < K2 ∧
        MinimaPower5.decayExponent5 j deltaGap ≤ SelectedRestriction5.sourceSelectedExponent5 P hPbounds.2 A2 A3 L h2d h3d hLd c0 c2 c3 ∧
        0 < SelectedRestriction5.sourceSelectedExponent5 P hPbounds.2 A2 A3 L h2d h3d hLd c0 c2 c3 ∧
        ∀ (Q : ℝ) (hQW : Q ∈ W),
          ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
            LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
            (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q (hq Q (hWV hQW)) c0)
              (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q (hq Q (hWV hQW)) c0 c2 c3 i) ∧
            P = originalFirstFlag5 j (fun i => (u i : Fin 5 → ℤ)) ∧
            (∀ i : Fin (Module.finrank ℚ P),
              integerReal (u (RestrictedGeometry5.ambientPrefixIndex5 P hPbounds.2 i) : Fin 5 → ℤ) ∈
                RestrictedGeometry5.rationalRealSpan5 P) ∧
            (∀ k, RestrictedGeometry5.restrictedMinima5 P A2 A3 L hL Q (hq Q (hWV hQW)) c0 c2 c3 k =
              sourceMinima5 A2 A3 L hL Q (hq Q (hWV hQW)) c0 c2 c3 (RestrictedGeometry5.ambientPrefixIndex5 P hPbounds.2 k)) ∧
            quantitativeOriginalPoint5 P hPbounds.2 j A2 A3 L hL Q (hq Q (hWV hQW)) c0 c2 c3 deltaGap C5 ∧
            RestrictedOpposite5.oppositePoint5 P hPbounds.2 A2 A3 L h2d h3d hLd c0 c2 c3 Q K2 := by
  obtain ⟨hL,epsilon,deltaGap,c5,C5,B,U,V,j,he,hdEq,hd,hc,hC,hB,hUeq,hU,hsol,hproduct,
    hVU,hV,hjlo,hjhi,hg,hq,P,hP,hPb,hPt,hPbounds,W,hWV,hW,hWU,hEta,hK,hframes⟩ :=
    source_normalized_nonroth_restricted_growth5 A2 A3 L h2d h3d hLd hAlg c0 c2 c3 hc0 hc2 hc3 hb hn
  obtain ⟨K2,hK2,hUpper⟩ := source_restricted_opposite_uniform5 P hPbounds.2 A2 A3 L h2d h3d hLd c0 c2 c3
    (fun i => (hc2 i).2) (fun i => (hc3 i).2)
  have hBound (Q : ℝ) (hQW : Q ∈ W) : growthConstant5 j C5 * Q^(MinimaPower5.decayExponent5 j deltaGap) ≤
      K2 * Q^(SelectedRestriction5.sourceSelectedExponent5 P hPbounds.2 A2 A3 L h2d h3d hLd c0 c2 c3) := by
    obtain ⟨u,hu,ha,hflag,hm,heq,hquant⟩ := hframes Q hQW
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hLower⟩ := hquant
    have hcopy := hUpper Q (hq Q (hWV hQW))
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hOriginalUpper⟩ := hcopy
    exact hLower.trans hOriginalUpper
  have hCompare := ExponentOrder4.exponent_le_of_unbounded_power_bound W hW
    (fun Q hQW => hq Q (hWV hQW)) (growthConstant5 j C5) K2
    (MinimaPower5.decayExponent5 j deltaGap)
    (SelectedRestriction5.sourceSelectedExponent5 P hPbounds.2 A2 A3 L h2d h3d hLd c0 c2 c3)
    hK hK2 hBound
  refine ⟨hL,epsilon,deltaGap,c5,C5,B,U,V,j,he,hdEq,hd,hc,hC,hB,hUeq,hU,hsol,hproduct,
    hVU,hV,hjlo,hjhi,hg,hq,P,hP,hPb,hPt,hPbounds,W,hWV,hW,hWU,hEta,hK,K2,hK2,hCompare,
    hEta.trans_le hCompare,?_⟩
  intro Q hQW
  obtain ⟨u,hu,ha,hflag,hm,heq,hquant⟩ := hframes Q hQW
  exact ⟨u,hu,ha,hflag,hm,heq,hquant,hUpper Q (hq Q (hWV hQW))⟩

end CompoundFeasibility.OriginalFlagAssembly5
