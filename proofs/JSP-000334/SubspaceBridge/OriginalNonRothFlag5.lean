import SubspaceBridge.OriginalSelectedFlag5
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalFlagAssembly5
open OriginalVariableGap5

theorem fixed_flag_nonzero_proper5 (j : Fin 4) (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P = j.val+1) : P ≠ ⊥ ∧ P ≠ ⊤ := by
  constructor
  · intro hz
    rw [hz] at hP
    simp at hP
  · intro hz
    rw [hz] at hP
    have ht : Module.finrank ℚ (⊤ : Submodule ℚ (Fin 5 → ℚ)) = 5 := by simp
    rw [ht] at hP
    omega

theorem source_normalized_nonroth_fixed_flag5
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
      ∃ W : Set ℝ, ∃ hWV : W ⊆ V, ¬ BddAbove W ∧ W ⊆ U ∧
        ∀ (Q : ℝ) (hQW : Q ∈ W),
          ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
            LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
            (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q (hq Q (hWV hQW)) c0)
              (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q (hq Q (hWV hQW)) c0 c2 c3 i) ∧
            P = originalFirstFlag5 j (fun i => (u i : Fin 5 → ℤ)) := by
  have h2 : IsUnit A2 := (Matrix.isUnit_iff_isUnit_det A2).mpr (by rw [h2d]; exact isUnit_one)
  have h3 : IsUnit A3 := (Matrix.isUnit_iff_isUnit_det A3).mpr (by rw [h3d]; exact isUnit_one)
  have hL : IsUnit L := (Matrix.isUnit_iff_isUnit_det L).mpr (by rw [hLd]; exact isUnit_one)
  obtain ⟨epsilon,deltaGap,c5,C5,B,U,V,j,he,hdEq,hd,hc,hC,hB,hUeq,hU,hsolutions,hproduct,
    hVU,hV,hjlo,hjhi,hg⟩ :=
    source_fin5_nonroth_gap_units5 A2 A3 L h2 h3 hL c0 c2 c3
      (fun i => (hc2 i).2) (fun i => (hc3 i).2) hb hn
  let hq : ∀ Q ∈ V, 1 < Q := fun Q hQV => (hg Q hQV).2.choose
  have hgap (Q : ℝ) (hQV : Q ∈ V) :
      sourceMinima5 A2 A3 L hL Q (hq Q hQV) c0 c2 c3 j.castSucc <
        sourceMinima5 A2 A3 L hL Q (hq Q hQV) c0 c2 c3 j.succ*Q^(-deltaGap) := by
    obtain ⟨hQ,hgQ⟩ := (hg Q hQV).2
    have heq : hQ = hq Q hQV := Subsingleton.elim _ _
    cases heq
    exact hgQ
  obtain ⟨P,hP,W,hWV,hW,hframes⟩ := source_selected_gap_fixed_flag5
    A2 A3 L h2d h3d hLd hL hAlg c0 c2 c3 hc0 hc2 hc3 hb
    deltaGap hd V hV hq j hgap
  have hproper := fixed_flag_nonzero_proper5 j P hP
  refine ⟨hL,epsilon,deltaGap,c5,C5,B,U,V,j,he,hdEq,hd,hc,hC,hB,hUeq,hU,
    hsolutions,hproduct,hVU,hV,hjlo,hjhi,hg,hq,P,hP,hproper.1,hproper.2,W,hWV,hW,?_,hframes⟩
  exact fun _ h => hVU (hWV h)

end CompoundFeasibility.OriginalFlagAssembly5
