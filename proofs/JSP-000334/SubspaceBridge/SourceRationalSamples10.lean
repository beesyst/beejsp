import SubspaceBridge.SourceRationalCounterexample10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceOriginalDual10
open SourceSampling10 SourceSelectedSet10 SourceSelectedUpper10 OriginalDual10 SchmidtNormal10 SourceOriginalVariable10
noncomputable section

theorem rational_family_schmidt_inputs10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) (S0 : Finset MixedIndex10) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ D0 E0 alpha C_upper T : ℝ, 1 ≤ D0 ∧ 1 ≤ E0 ∧ 0 < alpha ∧ 0 < C_upper ∧ 1 < T ∧
      ∀ (U : Set ℝ) (hQU : ∀ q ∈ U, 1 < q)
        (D : (q : U) → OriginalData10 A2 A3 L hL q.val (hQU q.val q.property) delta S0),
      (¬ ∃ B : ℝ, ∀ q : U, B < q.val → ∀ s ∈ S0,
        dataRationalDualProduct10 (D q) s = 0) →
      ∀ B1 : ℝ, ∃ V : Set ℝ, ∃ hVU : V ⊆ U, ¬ BddAbove V ∧
        (∀ q : V, max T B1 < q.val) ∧
      ∃ e : ℝ, 0 < e ∧ e < 1 ∧ ∃ c : Fin 3 → Fin 10 → ℝ,
        (∀ tau i, |c tau i| ≤ 1) ∧ (∑ tau, ∑ i, c tau i) = 0 ∧
        (∀ i, c 1 i ≤ 0 ∧ c 2 i ≤ 0) ∧
      ∃ eta : ℝ, 0 < eta ∧ 4000*eta < e ∧ ∃ m : ℕ, ∃ hm : 0 < m,
        4*(eta^2)⁻¹*Real.log (60*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) ∧
        (∀ rho : ℝ, 0 < rho → ∀ B : ℝ,
          Nonempty (OriginalAuxiliarySample10 A2 A3 L (fun i => 5*c 1 i) (fun i => 5*c 2 i)
            V (fun q => (D ⟨q.val,hVU q.property⟩).u) c e eta D0 E0 B rho m hm)) ∧
        ∀ (rho B : ℝ)
          (S : OriginalAuxiliarySample10 A2 A3 L (fun i => 5*c 1 i) (fun i => 5*c 2 i)
            V (fun q => (D ⟨q.val,hVU q.property⟩).u) c e eta D0 E0 B rho m hm) (h : Fin m),
          ((S.data.t h).val^5)^alpha ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
          (normalHeight10 (S.data.M h) : ℝ) ≤ C_upper*((S.data.t h).val^5)^9 ∧
          ∃ s ∈ S0, mixedProduct10 A2 A3 L (S.data.M h) s ≠ 0 ∧
            mixedProduct10 A2 A3 L (S.data.M h) s ≤ 362880*((S.data.t h).val^5)^(-17*delta/10) := by
  obtain ⟨K,hK,D0,E0,alpha,C_upper,T,hD,hE,ha,hC,hT,hinputs⟩ :=
    original_counterexample_schmidt_inputs10 A2 A3 L h2 h3 hLd hL hAlg delta hd S0
  refine ⟨K,hK,D0,E0,alpha,C_upper,T,hD,hE,ha,hC,hT,?_⟩
  intro U hQU D hfail B1
  exact hinputs U hQU D (rational_failure_to_cofactor_failure10 U hQU D hfail) B1

theorem original_rational_counterexample_samples10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) (S0 : Finset MixedIndex10) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ D0 E0 alpha C_upper T : ℝ, 1 ≤ D0 ∧ 1 ≤ E0 ∧ 0 < alpha ∧ 0 < C_upper ∧ 1 < T ∧
      ∀ (_hfail : ∀ B : ℝ, ∃ Q : ℝ, ∃ hQ : 1 < Q, B < Q ∧
        ∃ D : OriginalData10 A2 A3 L hL Q hQ delta S0,
          ∃ s ∈ S0, dataRationalDualProduct10 D s ≠ 0),
      ∀ B1 : ℝ, ∃ U : Set ℝ, ¬ BddAbove U ∧ ∃ hQU : ∀ q ∈ U, 1 < q,
        ∃ D : (q : U) → OriginalData10 A2 A3 L hL q.val (hQU q.val q.property) delta S0,
          (∀ q : U, ∃ s ∈ S0, dataRationalDualProduct10 (D q) s ≠ 0) ∧
      ∃ V : Set ℝ, ∃ hVU : V ⊆ U, ¬ BddAbove V ∧
        (∀ q : V, max T B1 < q.val) ∧
      ∃ e : ℝ, 0 < e ∧ e < 1 ∧ ∃ c : Fin 3 → Fin 10 → ℝ,
        (∀ tau i, |c tau i| ≤ 1) ∧ (∑ tau, ∑ i, c tau i) = 0 ∧
        (∀ i, c 1 i ≤ 0 ∧ c 2 i ≤ 0) ∧
      ∃ eta : ℝ, 0 < eta ∧ 4000*eta < e ∧ ∃ m : ℕ, ∃ hm : 0 < m,
        4*(eta^2)⁻¹*Real.log (60*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) ∧
        (∀ rho : ℝ, 0 < rho → ∀ B : ℝ,
          Nonempty (OriginalAuxiliarySample10 A2 A3 L (fun i => 5*c 1 i) (fun i => 5*c 2 i)
            V (fun q => (D ⟨q.val,hVU q.property⟩).u) c e eta D0 E0 B rho m hm)) ∧
        ∀ (rho B : ℝ)
          (S : OriginalAuxiliarySample10 A2 A3 L (fun i => 5*c 1 i) (fun i => 5*c 2 i)
            V (fun q => (D ⟨q.val,hVU q.property⟩).u) c e eta D0 E0 B rho m hm) (h : Fin m),
          ((S.data.t h).val^5)^alpha ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
          (normalHeight10 (S.data.M h) : ℝ) ≤ C_upper*((S.data.t h).val^5)^9 ∧
          ∃ s ∈ S0, mixedProduct10 A2 A3 L (S.data.M h) s ≠ 0 ∧
            mixedProduct10 A2 A3 L (S.data.M h) s ≤ 362880*((S.data.t h).val^5)^(-17*delta/10) := by
  obtain ⟨K,hK,D0,E0,alpha,C_upper,T,hD,hE,ha,hC,hT,hinputs⟩ :=
    rational_family_schmidt_inputs10 A2 A3 L h2 h3 hLd hL hAlg delta hd S0
  refine ⟨K,hK,D0,E0,alpha,C_upper,T,hD,hE,ha,hC,hT,?_⟩
  intro hfail B1
  obtain ⟨U,hU,hQU,D,hbad,hnotzero⟩ := rational_counterexamples_unbounded10 A2 A3 L hL delta S0 hfail
  exact ⟨U,hU,hQU,D,hbad,hinputs U hQU D hnotzero B1⟩

end
end CompoundFeasibility.SourceOriginalDual10
