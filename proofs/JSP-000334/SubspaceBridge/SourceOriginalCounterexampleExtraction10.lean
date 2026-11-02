import SubspaceBridge.SourceOriginalCounterexample10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceOriginalVariable10
open SourceSelectedSet10 SourceSelectedUpper10 OriginalDual10
noncomputable section

theorem original_counterexamples_unbounded10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : IsUnit L) (delta : ℝ) (S0 : Finset MixedIndex10)
    (hfail : ∀ B : ℝ, ∃ Q : ℝ, ∃ hQ : 1 < Q, B < Q ∧
      ∃ D : OriginalData10 A2 A3 L hL Q hQ delta S0,
        ∃ s ∈ S0, mixedProduct10 A2 A3 L (integerLastDual10 D.u) s ≠ 0) :
    ∃ U : Set ℝ, ¬ BddAbove U ∧ ∃ hQU : ∀ q ∈ U, 1 < q,
      ∃ D : (q : U) → OriginalData10 A2 A3 L hL q.val (hQU q.val q.property) delta S0,
        (∀ q : U, ∃ s ∈ S0, mixedProduct10 A2 A3 L (integerLastDual10 (D q).u) s ≠ 0) ∧
        ¬ ∃ B : ℝ, ∀ q : U, B < q.val → ∀ s ∈ S0,
          mixedProduct10 A2 A3 L (integerLastDual10 (D q).u) s = 0 := by
  let U := {Q : ℝ | ∃ hQ : 1 < Q, ∃ D : OriginalData10 A2 A3 L hL Q hQ delta S0,
    ∃ s ∈ S0, mixedProduct10 A2 A3 L (integerLastDual10 D.u) s ≠ 0}
  have hU : ¬ BddAbove U := by
    rintro ⟨B,hB⟩
    obtain ⟨Q,hQ,hBQ,D,s,hs,hn⟩ := hfail B
    exact (not_le_of_gt hBQ) (hB ⟨hQ,D,s,hs,hn⟩)
  let hQU : ∀ q ∈ U, 1 < q := fun q hq => hq.choose
  have hdata (q : U) : ∃ D : OriginalData10 A2 A3 L hL q.val (hQU q.val q.property) delta S0,
      ∃ s ∈ S0, mixedProduct10 A2 A3 L (integerLastDual10 D.u) s ≠ 0 := by
    obtain ⟨hQ,D,s,hs,hn⟩ := q.property
    exact ⟨D,s,hs,hn⟩
  choose D hbad using hdata
  refine ⟨U,hU,hQU,D,hbad,?_⟩
  rintro ⟨B,hzero⟩
  obtain ⟨q,hq,hBq⟩ := not_bddAbove_iff.mp hU B
  obtain ⟨s,hs,hn⟩ := hbad ⟨q,hq⟩
  exact hn (hzero ⟨q,hq⟩ hBq s hs)

end
end CompoundFeasibility.SourceOriginalVariable10
