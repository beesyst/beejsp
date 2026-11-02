import SubspaceBridge.BinaryWeightedSolutionHeight2
import SubspaceBridge.BinaryHeightFinite2
open scoped BigOperators Classical
namespace JSP000334

theorem binary_weighted_allpoint_finite_cover (B C : ℚ) (hB : B ≠ 0) (hC : C ≠ 0) :
    ∃ F : Set (Submodule ℚ (Fin 2 → ℚ)),F.Finite ∧ (∀ P ∈ F,P ≠ ⊤) ∧
    ∀ z : Fin 2 → ℤ,PrimitivePair z →
      (weightedNormalizedProduct2 B C (z 0 : ℚ) (z 1 : ℚ) : ℝ)<
        Real.rpow (archPairHeight z : ℝ) (-(5 : ℝ)/2) →
      ∃ P ∈ F,(fun i => (z i : ℚ)) ∈ P := by
  obtain ⟨M,hM⟩ := binary_weighted_solution_height_bound B C hB hC
  let T : Set (Fin 2 → ℤ) := {z | BinaryWeightedNonexceptional B C z}
  have hT : T.Finite := binary_integer_height_ball_finite T M hM
  let F : Set (Submodule ℚ (Fin 2 → ℚ)) :=
    (binaryZeroLines B C : Set (Submodule ℚ (Fin 2 → ℚ))) ∪ (binaryRationalSpan '' T)
  have hF : F.Finite := (binaryZeroLines B C).finite_toSet.union (hT.image binaryRationalSpan)
  refine ⟨F,hF,?_,?_⟩
  · intro P hP
    rcases hP with hzero | hspan
    · exact binary_zero_lines_proper B C hB P hzero
    · obtain ⟨z,hz,rfl⟩ := hspan
      exact binary_rational_span_proper z hz.2.2.1
  · intro z hz hp
    by_cases he : z 0=0 ∨ z 1=0 ∨ B*(z 0 : ℚ)+C*(z 1 : ℚ)=0
    · obtain ⟨P,hP,hzP⟩ := binary_zero_form_cover B C z he
      exact ⟨P,Or.inl hP,hzP⟩
    · push_neg at he
      have hzT : z ∈ T := ⟨hz,he.1,he.2.1,he.2.2,hp⟩
      exact ⟨binaryRationalSpan z,Or.inr ⟨z,hzT,rfl⟩,binary_rational_span_mem z⟩

end JSP000334
