import SubspaceBridge.OriginalFirstFlag5
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalFlagAssembly5

theorem source_selected_gap_fixed_flag5
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c0 c2 c3 : Fin 5 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (delta : ℝ) (hd : 0 < delta) (Omega : Set ℝ) (hO : ¬ BddAbove Omega)
    (hq : ∀ Q ∈ Omega, 1 < Q) (j : Fin 4)
    (hgap : ∀ (Q : ℝ) (hQO : Q ∈ Omega),
      sourceMinima5 A2 A3 L hL Q (hq Q hQO) c0 c2 c3 j.castSucc <
        sourceMinima5 A2 A3 L hL Q (hq Q hQO) c0 c2 c3 j.succ*Q^(-delta)) :
    ∃ P : Submodule ℚ (Fin 5 → ℚ), Module.finrank ℚ P = j.val+1 ∧
      ∃ V : Set ℝ, ∃ hVO : V ⊆ Omega, ¬ BddAbove V ∧
        ∀ (Q : ℝ) (hQV : Q ∈ V),
          ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
            LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
            (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q (hq Q (hVO hQV)) c0)
              (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q (hq Q (hVO hQV)) c0 c2 c3 i) ∧
            P = originalFirstFlag5 j (fun i => (u i : Fin 5 → ℤ)) := by
  fin_cases j
  · obtain ⟨P,hP,V,hVO,hV,hframes⟩ :=
      SourceFlag247.source_original_fixed_rank1_247 A2 A3 L h2d h3d hLd hL hAlg c0 c2 c3
        hc0 hc2 hc3 hb delta hd Omega hO hq hgap
    refine ⟨P,hP,V,hVO,hV,?_⟩
    intro Q hQV
    obtain ⟨u,hu,ha,hspan⟩ := hframes Q hQV
    refine ⟨u,hu,ha,?_⟩
    change P = originalFirstFlag5 (0 : Fin 4) (fun i => (u i : Fin 5 → ℤ))
    rw [originalFirstFlag5_one]
    exact hspan
  · obtain ⟨P,hP,V,hVO,hV,hframes⟩ :=
      SourceFlag244.source_original_fixed_rank2_244 A2 A3 L h2d h3d hLd hL hAlg c0 c2 c3
        hc0 hc2 hc3 hb delta hd Omega hO hq hgap
    refine ⟨P,hP,V,hVO,hV,?_⟩
    intro Q hQV
    obtain ⟨u,hu,ha,hspan⟩ := hframes Q hQV
    refine ⟨u,hu,ha,?_⟩
    change P = originalFirstFlag5 (1 : Fin 4) (fun i => (u i : Fin 5 → ℤ))
    rw [originalFirstFlag5_two]
    exact hspan
  · obtain ⟨P,hP,V,hVO,hV,hframes⟩ :=
      SourceFlag241.source_original_fixed_rank3_241 A2 A3 L h2d h3d hLd hL hAlg c0 c2 c3
        hc0 hc2 hc3 hb delta hd Omega hO hq hgap
    refine ⟨P,hP,V,hVO,hV,?_⟩
    intro Q hQV
    obtain ⟨u,hu,ha,hspan⟩ := hframes Q hQV
    refine ⟨u,hu,ha,?_⟩
    change P = originalFirstFlag5 (2 : Fin 4) (fun i => (u i : Fin 5 → ℤ))
    rw [originalFirstFlag5_three]
    exact hspan
  · obtain ⟨P,hP,V,hVO,hV,hframes⟩ :=
      BlockRank4_245U.source_original_fixed_rank4_245 A2 A3 L h2d h3d hLd hL hAlg c0 c2 c3
        hc0 hc2 hc3 hb delta hd Omega hO hq hgap
    refine ⟨P,hP,V,hVO,hV,?_⟩
    intro Q hQV
    obtain ⟨u,hu,ha,hspan⟩ := hframes Q hQV
    refine ⟨u,hu,ha,?_⟩
    change P = originalFirstFlag5 (3 : Fin 4) (fun i => (u i : Fin 5 → ℤ))
    rw [originalFirstFlag5_four]
    exact hspan

end CompoundFeasibility.OriginalFlagAssembly5
