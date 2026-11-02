import SubspaceBridge.SourceOriginalData10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceOriginalVariable10
open SourceSelectedSet10 SourceSelectedUpper10 OriginalDual10 SourceSampling10 SourceGlobalSelected10
noncomputable section

theorem original_fixed_selector_bad_tail10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1)
    (h2u : IsUnit A2) (h3u : IsUnit A3) (hL : IsUnit L)
    (delta : ℝ) (hd : 0 < delta) (S0 : Finset MixedIndex10) :
    ∃ T : ℝ, 1 < T ∧ ∀ (U : Set ℝ) (hQU : ∀ q ∈ U, 1 < q)
      (D : (q : U) → OriginalData10 A2 A3 L hL q.val (hQU q.val q.property) delta S0),
      (¬ ∃ B : ℝ, ∀ q : U, B < q.val → ∀ s ∈ S0,
        mixedProduct10 A2 A3 L (integerLastDual10 (fun j => ((D q).u j : Fin 10 → ℤ))) s = 0) →
      ∀ B : ℝ, ∃ V : Set ℝ, ∃ hVU : V ⊆ U, ¬ BddAbove V ∧
        ∀ q : V, max T B < q.val ∧
          (∃ s ∈ S0, mixedProduct10 A2 A3 L
            (integerLastDual10 (fun j => ((D ⟨q.val,hVU q.property⟩).u j : Fin 10 → ℤ))) s ≠ 0) ∧
          (∀ s ∈ S0, mixedProduct10 A2 A3 L
            (integerLastDual10 (fun j => ((D ⟨q.val,hVU q.property⟩).u j : Fin 10 → ℤ))) s ≤
              362880*q.val^(-17*delta/2)) ∧
          Nonempty (OriginalFrameWitness10 A2 A3 L q.val delta
            (fun i => normalizedFinite10 2 q.val ((D ⟨q.val,hVU q.property⟩).f2 i))
            (fun i => normalizedFinite10 3 q.val ((D ⟨q.val,hVU q.property⟩).f3 i))
            (fun j => ((D ⟨q.val,hVU q.property⟩).u j : Fin 10 → ℤ))) := by
  obtain ⟨T,hT,hframe⟩ := original_absolute_short_frame10 A2 A3 L h2u h3u hL delta hd
  refine ⟨T,hT,?_⟩
  intro U hQU D hfail B
  let P : U → MixedIndex10 → ℝ := fun q s => mixedProduct10 A2 A3 L
    (integerLastDual10 (fun j => ((D q).u j : Fin 10 → ℤ))) s
  let W := {q : ℝ | ∃ hq : q ∈ U, ∃ s ∈ S0, P ⟨q,hq⟩ s ≠ 0}
  have hW : ¬ BddAbove W := unbounded_selected_nonzero_tail10 U (fun _ => S0) P hfail
  let V := {q : ℝ | q ∈ W ∧ max T B < q}
  have hVU : V ⊆ U := fun q hq => hq.1.choose
  have hV : ¬ BddAbove V := by
    rintro ⟨C,hC⟩
    obtain ⟨q,hq,hlarge⟩ := not_bddAbove_iff.mp hW (max C (max T B))
    have hqV : q ∈ V := ⟨hq,(le_max_right _ _).trans_lt hlarge⟩
    exact (not_lt_of_ge (hC hqV)) ((le_max_left _ _).trans_lt hlarge)
  refine ⟨V,hVU,hV,?_⟩
  intro q
  have hq := q.property
  obtain ⟨hU,s,hs,hn⟩ := hq.1
  refine ⟨hq.2,⟨s,hs,hn⟩,?_,?_⟩
  · intro s hs
    exact original_data_cofactor_upper10 h2 h3 hLd (D ⟨q.val,hVU q.property⟩) s hs
  · exact hframe q.val (hQU q.val (hVU q.property)) S0 (D ⟨q.val,hVU q.property⟩)
      ((le_max_left _ _).trans_lt hq.2)

end
end CompoundFeasibility.SourceOriginalVariable10
