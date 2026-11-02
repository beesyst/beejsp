import SubspaceBridge.SourceOriginalFrame10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSampling10
open OriginalDeformation10

structure OriginalFrameWitness10 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (Q delta : ℝ) (c2 c3 : Fin 10 → ℝ)
    (u : Fin 10 → Fin 10 → ℤ) where
  w : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3
  W : Fin 10 → ℝ
  independent : LinearIndependent ℝ (fun j => integerReal (w j : Fin 10 → ℤ))
  flag : minimaFlag10 (fun i => integerReal (u i)) 9 =
    minimaFlag10 (fun i => integerReal (w i : Fin 10 → ℤ)) 9
  positive : ∀ i, 0 < W i
  balance : (∏ i, W i)*(∏ i, Q^(c2 i+c3 i)) = 1
  sizes : ∀ i, W i < Q^5 ∧ (W i)⁻¹ < Q^5
  small : ∀ (j : Fin 9) i, |(L *ᵥ integerReal (w j.castSucc : Fin 10 → ℤ)) i| ≤
    (Q^5)^(-(delta/60))*W i

theorem original_frame_witness10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ),
    (∀ i, |c0 i| ≤ 1) → (∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) →
    (∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 → T < Q →
    ∀ u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3,
    LinearIndependent ℝ (fun i => integerReal (u i : Fin 10 → ℤ)) →
    (∀ i, coordinateGauge10 (originalCoordinates10 L hL Q hQ c0)
      (integerReal (u i : Fin 10 → ℤ)) = sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 i) →
    sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 8 <
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9*Q^(-delta) →
    Nonempty (OriginalFrameWitness10 A2 A3 L Q delta c2 c3 (fun i => (u i : Fin 10 → ℤ))) := by
  obtain ⟨T,hT,hsource⟩ := source_original_deformed_frame10 A2 A3 L h2 h3 hL delta hd
  refine ⟨T,hT,?_⟩
  intro Q hQ c0 c2 c3 hc0 hc2 hc3 hb hlarge u hu hatt hgap
  obtain ⟨hdp,sigma,w,hli,hatt',hflag,hpos,hbal,hsizes,hsmall⟩ :=
    hsource Q hQ c0 c2 c3 hc0 hc2 hc3 hb hlarge u hu hatt hgap
  exact ⟨⟨w,_,hli,hflag,hpos,hbal,hsizes,hsmall⟩⟩

end CompoundFeasibility.SourceSampling10
