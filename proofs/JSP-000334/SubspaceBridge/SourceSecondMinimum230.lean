import SubspaceBridge.SourceSecondIntegration230
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSecondMinimum230
open OriginalDual10 SourceSatz51Entry218 SourceDualGeometry219 SourceDualAnnihilation222
  SourceSecondMinimum226 SourceSecondMinimum228

theorem source_uniform_second230 (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
      (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (q : ℝ), T < q →
      ∀ (hq : 1 < q) (c2 c3 A : Fin 10 → ℝ)
        (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta),
        2 ≤ originalSecondRadius230 A2 A3 L hL q c2 c3 A D.positive ∧
        1 < originalSecondRadius230 A2 A3 L hL q c2 c3 A D.positive := by
  obtain ⟨T, hT, hline⟩ := source_short_line226 delta hd
  refine ⟨T, hT, ?_⟩
  intro A2 A3 L hL q hqT hq c2 c3 A D
  have h := original_second_of_line230 A2 A3 L hL q c2 c3 A D.positive
    (integerLastDual10 D.u) (hline A2 A3 L hL q hqT hq c2 c3 A D)
  exact ⟨h, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) h⟩

theorem source_uniform_original_second230 (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
      (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (q : ℝ), T < q →
      ∀ (hq : 1 < q) (c2 c3 A : Fin 10 → ℝ)
        (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta),
        2 ≤ successiveRadius10 (originalDualRealBasis228 A2 A3 q c2 c3)
          (dualCoordinates222 L hL
            (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3)))
            (ZLattice.covolume_pos _ MeasureTheory.volume) A D.positive) (1 : Fin 10) ∧
        1 < successiveRadius10 (originalDualRealBasis228 A2 A3 q c2 c3)
          (dualCoordinates222 L hL
            (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3)))
            (ZLattice.covolume_pos _ MeasureTheory.volume) A D.positive) (1 : Fin 10) := by
  obtain ⟨T, hT, h⟩ := source_uniform_second230 delta hd
  refine ⟨T, hT, ?_⟩
  intro A2 A3 L hL q hqT hq c2 c3 A D
  have hn := h A2 A3 L hL q hqT hq c2 c3 A D
  have he := originalSecondRadius_eq230 A2 A3 L hL q c2 c3 A D.positive
  have hr := Eq.mp (congrArg (fun r : ℝ => 2 ≤ r ∧ 1 < r) he) hn
  exact hr

end CompoundFeasibility.SourceSecondMinimum230
