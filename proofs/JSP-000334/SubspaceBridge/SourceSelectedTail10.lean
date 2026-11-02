import SubspaceBridge.SourceSampleSchmidtExclusion10
open scoped Classical
noncomputable section
namespace CompoundFeasibility.SourceGlobalSelected10

theorem unbounded_selected_nonzero_tail10 {ι : Type*} [DecidableEq ι]
    (U : Set ℝ) (F : U → Finset ι) (P : U → ι → ℝ)
    (hfail : ¬ ∃ B : ℝ, ∀ q : U, B < q.val → ∀ s ∈ F q, P q s = 0) :
    ¬ BddAbove {q : ℝ | ∃ hq : q ∈ U, ∃ s ∈ F ⟨q,hq⟩, P ⟨q,hq⟩ s ≠ 0} := by
  rintro ⟨B,hB⟩
  apply hfail
  refine ⟨B,?_⟩
  intro q hq s hs
  by_contra hn
  exact (not_le_of_gt hq) (hB ⟨q.property,s,hs,hn⟩)

end CompoundFeasibility.SourceGlobalSelected10
