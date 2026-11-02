import SubspaceBridge.WeightedFiveTermCoefficientFiber4
namespace JSP000334
open scoped BigOperators Matrix

def weightedFiveProperFiber4 (A : ℚ) (B : Fin 4 → ℚ)
    (P : Submodule ℚ (Fin 4 → ℚ)) : Set (Fin 4 → fixedSUnitGroup) :=
  {u∈WeightedFiveTermSolutions A B | (fun i => ((u i : ℚˣ) : ℚ))∈P}

theorem weighted_five_proper_fiber_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (P : Submodule ℚ (Fin 4 → ℚ)) (hP : P≠⊤) :
    (weightedFiveProperFiber4 A B P).Finite := by
  obtain ⟨b0,b1,b2,b3,hb,hann⟩ := five_term_proper_annihilator4 P hP
  let b : Fin 4 → ℚ := ![b0,b1,b2,b3]
  have hbn : ∃ i,b i≠0 := by
    rcases hb with h|h|h|h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · exact ⟨3,h⟩
  apply (weighted_five_coefficient_finite4 A B b hA hB hbn).subset
  intro u hu
  refine ⟨hu.1,?_⟩
  simpa [b,Fin.sum_univ_four] using hann _ hu.2

theorem weighted_five_term_finite (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) :
    (WeightedFiveTermSolutions A B).Finite := by
  obtain ⟨F,hF,hproper,hcover⟩ := weighted_five_term_proper_cover4 A B hA hB
  have hU : (⋃ P∈F,weightedFiveProperFiber4 A B P).Finite :=
    hF.biUnion (fun P hPF => weighted_five_proper_fiber_finite4 A B hA hB P (hproper P hPF))
  apply hU.subset
  intro u hu
  obtain ⟨P,hPF,huP⟩ := hcover u hu
  exact Set.mem_iUnion.mpr ⟨P,Set.mem_iUnion.mpr ⟨hPF,hu,huP⟩⟩

end JSP000334
