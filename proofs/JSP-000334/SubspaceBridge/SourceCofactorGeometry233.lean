import SubspaceBridge.SourceCofactorBody233
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceCofactorGeometry233
open OriginalDual10 SourceOriginalDual10 SourceSatz51Entry218 SourceLastDual231 SourceDualAnnihilation222
  SourceDualGeometry219
variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {q : ℝ} {hq : 1 < q} {c2 c3 A : Fin 10 → ℝ} {delta : ℝ}

theorem source_cofactor_rat_nonzero233 (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) :
    (fun i => (integerLastDual10 D.u i : ℚ)) ≠ 0 := by
  intro h
  apply source_cofactor_nonzero231 D
  funext i
  have hi : (integerLastDual10 D.u i : ℚ) = 0 := congrFun h i
  change integerLastDual10 D.u i = 0
  exact_mod_cast hi

theorem source_cofactor_line233 (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) :
    Submodule.span ℚ {fun i => (integerLastDual10 D.u i : ℚ)} =
      Submodule.span ℚ {lastDual10 (fun j i => (D.u j i : ℚ))
        (integer_frame_rational_independent10 D.u D.independent)} := by
  exact integerLastDual10_line D.u (integer_frame_rational_independent10 D.u D.independent)

theorem source_uniform_cofactor233 (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
      (h2 : A2.det = 1) (h3 : A3.det = 1) (L : Matrix (Fin 10) (Fin 10) ℝ)
      (hL : IsUnit L) (hLd : L.det = 1) (q : ℝ), T < q →
      ∀ (hq : 1 < q) (c2 c3 A : Fin 10 → ℝ)
        (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta),
        let v : Fin 10 → ℚ := fun i => (integerLastDual10 D.u i : ℚ)
        v ≠ 0 ∧ v ∈ scaledDual219 (originalSourceGroup10 A2 A3 q c2 c3) ∧
          ratReal222 v ∈ dualBody222 L
            (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3))) A ∧
          Submodule.span ℚ {v} = Submodule.span ℚ
            {lastDual10 (fun j i => (D.u j i : ℚ))
              (integer_frame_rational_independent10 D.u D.independent)} := by
  obtain ⟨T, hT, hcut⟩ := cofactor_cutoff233 delta hd
  refine ⟨T, hT, ?_⟩
  intro A2 A3 h2 h3 L hL hLd q hqT hq c2 c3 A D
  exact ⟨source_cofactor_rat_nonzero233 D, source_cofactor_dual231 D,
    source_cofactor_body233 h2 h3 hLd D (hcut q hqT), source_cofactor_line233 D⟩

theorem source_cofactor_real_nonzero233 (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) :
    ratReal222 (fun i => (integerLastDual10 D.u i : ℚ)) ≠ 0 := by
  rw [cofactor_cast233 D.u]
  intro h
  apply source_cofactor_nonzero231 D
  funext i
  have hi : (integerLastDual10 D.u i : ℝ) = 0 := congrFun h i
  change integerLastDual10 D.u i = 0
  exact_mod_cast hi

open SourceSecondMinimum228 SourceSecondMinimum230

theorem source_uniform_geometry233 (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
      (h2 : A2.det = 1) (h3 : A3.det = 1) (L : Matrix (Fin 10) (Fin 10) ℝ)
      (hL : IsUnit L) (hLd : L.det = 1) (q : ℝ), T < q →
      ∀ (hq : 1 < q) (c2 c3 A : Fin 10 → ℝ)
        (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta),
        let v : Fin 10 → ℚ := fun i => (integerLastDual10 D.u i : ℚ)
        1 < successiveRadius10 (originalDualRealBasis228 A2 A3 q c2 c3)
          (dualCoordinates222 L hL
            (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3)))
            (ZLattice.covolume_pos _ MeasureTheory.volume) A D.positive) (1 : Fin 10) ∧
        ratReal222 v ≠ 0 ∧
        ratReal222 v ∈ dualBody222 L
            (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3))) A ∩
          (ratReal222 '' scaledDual219 (originalSourceGroup10 A2 A3 q c2 c3)) ∧
        Submodule.span ℚ {v} = Submodule.span ℚ
          {lastDual10 (fun j i => (D.u j i : ℚ))
            (integer_frame_rational_independent10 D.u D.independent)} := by
  obtain ⟨T1, hT1, hsecond⟩ := source_uniform_original_second230 delta hd
  obtain ⟨T2, _, hpoint⟩ := source_uniform_cofactor233 delta hd
  refine ⟨max T1 T2, lt_of_lt_of_le hT1 (le_max_left _ _), ?_⟩
  intro A2 A3 h2 h3 L hL hLd q hqT hq c2 c3 A D
  have hs := (hsecond A2 A3 L hL q ((le_max_left T1 T2).trans_lt hqT) hq c2 c3 A D).2
  have hp := hpoint A2 A3 h2 h3 L hL hLd q
    ((le_max_right T1 T2).trans_lt hqT) hq c2 c3 A D
  exact ⟨hs, source_cofactor_real_nonzero233 D,
    ⟨hp.2.2.1, ⟨(fun i => (integerLastDual10 D.u i : ℚ)), hp.2.1, rfl⟩⟩, hp.2.2.2⟩

end CompoundFeasibility.SourceCofactorGeometry233
