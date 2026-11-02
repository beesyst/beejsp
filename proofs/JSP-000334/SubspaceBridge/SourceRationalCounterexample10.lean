import SubspaceBridge.SourceOriginalRationalDual10
import SubspaceBridge.SourceOriginalCounterexampleExtraction10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceOriginalDual10
open OriginalDual10 SourceSelectedSet10 SourceSelectedUpper10 SourceOriginalVariable10
noncomputable section

theorem rational_failure_to_cofactor_failure10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {hL : IsUnit L} {delta : ℝ} {S0 : Finset MixedIndex10}
    (U : Set ℝ) (hQU : ∀ q ∈ U, 1 < q)
    (D : (q : U) → OriginalData10 A2 A3 L hL q.val (hQU q.val q.property) delta S0)
    (hfail : ¬ ∃ B : ℝ, ∀ q : U, B < q.val → ∀ s ∈ S0, dataRationalDualProduct10 (D q) s = 0) :
    ¬ ∃ B : ℝ, ∀ q : U, B < q.val → ∀ s ∈ S0,
      mixedProduct10 A2 A3 L (integerLastDual10 (D q).u) s = 0 := by
  rintro ⟨B,hzero⟩
  apply hfail
  refine ⟨B,?_⟩
  intro q hq s hs
  by_contra hn
  exact (data_rational_product_nonzero_iff (D q) s).mp hn (hzero q hq s hs)

theorem rational_counterexamples_unbounded10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : IsUnit L) (delta : ℝ) (S0 : Finset MixedIndex10)
    (hfail : ∀ B : ℝ, ∃ Q : ℝ, ∃ hQ : 1 < Q, B < Q ∧
      ∃ D : OriginalData10 A2 A3 L hL Q hQ delta S0, ∃ s ∈ S0, dataRationalDualProduct10 D s ≠ 0) :
    ∃ U : Set ℝ, ¬ BddAbove U ∧ ∃ hQU : ∀ q ∈ U, 1 < q,
      ∃ D : (q : U) → OriginalData10 A2 A3 L hL q.val (hQU q.val q.property) delta S0,
        (∀ q : U, ∃ s ∈ S0, dataRationalDualProduct10 (D q) s ≠ 0) ∧
        ¬ ∃ B : ℝ, ∀ q : U, B < q.val → ∀ s ∈ S0, dataRationalDualProduct10 (D q) s = 0 := by
  have hcof : ∀ B : ℝ, ∃ Q : ℝ, ∃ hQ : 1 < Q, B < Q ∧
      ∃ D : OriginalData10 A2 A3 L hL Q hQ delta S0, ∃ s ∈ S0,
        mixedProduct10 A2 A3 L (integerLastDual10 D.u) s ≠ 0 := by
    intro B
    obtain ⟨Q,hQ,hBQ,D,s,hs,hn⟩ := hfail B
    exact ⟨Q,hQ,hBQ,D,s,hs,(data_rational_product_nonzero_iff D s).mp hn⟩
  obtain ⟨U,hU,hQU,D,hbad,_hnotzero⟩ := original_counterexamples_unbounded10 A2 A3 L hL delta S0 hcof
  have hrat (q : U) : ∃ s ∈ S0, dataRationalDualProduct10 (D q) s ≠ 0 := by
    obtain ⟨s,hs,hn⟩ := hbad q
    exact ⟨s,hs,(data_rational_product_nonzero_iff (D q) s).mpr hn⟩
  refine ⟨U,hU,hQU,D,hrat,?_⟩
  rintro ⟨B,hzero⟩
  obtain ⟨q,hq,hBq⟩ := not_bddAbove_iff.mp hU B
  obtain ⟨s,hs,hn⟩ := hrat ⟨q,hq⟩
  exact hn (hzero ⟨q,hq⟩ hBq s hs)

end
end CompoundFeasibility.SourceOriginalDual10
