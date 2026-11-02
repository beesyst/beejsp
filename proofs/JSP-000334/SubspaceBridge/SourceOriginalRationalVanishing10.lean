import SubspaceBridge.SourceOriginalRationalExclusion10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceOriginalVanishing10
open SourceFixedBudget10 SourceOriginalDual10 SourceOriginalVariable10 SourceSelectedSet10

theorem original_rational_selected_eventually_zero10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) (S0 : Finset MixedIndex10) :
    ∃ Q0 : ℝ, ∀ Q : ℝ, ∀ hQ : 1 < Q, Q0 < Q →
      ∀ D : OriginalData10 A2 A3 L hL Q hQ delta S0,
      ∀ s : MixedIndex10, s ∈ S0 → dataRationalDualProduct10 D s = 0 := by
  classical
  by_contra hnot
  apply original_rational_failure_contradiction10 A2 A3 L h2 h3 hLd hL hAlg delta hd S0
  intro B
  by_contra hnone
  apply hnot
  refine ⟨B,?_⟩
  intro Q hQ hBQ D s hs
  by_contra hn
  exact hnone ⟨Q,hQ,hBQ,D,s,hs,hn⟩

end CompoundFeasibility.SourceOriginalVanishing10
