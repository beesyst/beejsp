import SubspaceBridge.WeightedFourTermCoefficientFiber3
namespace JSP000334
open scoped BigOperators Matrix

def weightedFourTermProperFiber3 (A B C D : ℚ) (P : Submodule ℚ (Fin 3 → ℚ)) :
    Set (fixedSUnitGroup × fixedSUnitGroup × fixedSUnitGroup) :=
  {p | p∈WeightedFourTermSolutions A B C D ∧ weightedFourTermValues3 p∈P}

theorem weighted_four_term_proper_fiber_finite3 (A B C D : ℚ)
    (hA : A≠0) (hB : B≠0) (hC : C≠0) (hD : D≠0)
    (P : Submodule ℚ (Fin 3 → ℚ)) (hP : P≠⊤) :
    (weightedFourTermProperFiber3 A B C D P).Finite := by
  obtain ⟨b0,b1,b2,hb,hann⟩ := four_term_proper_annihilator P hP
  apply (weighted_four_term_coefficient_fiber_finite3 A B C D b0 b1 b2 hA hB hC hD hb).subset
  intro p hp
  refine ⟨hp.1,?_⟩
  exact hann (weightedFourTermValues3 p) hp.2

theorem weighted_four_term_finite (A B C D : ℚ)
    (hA : A≠0) (hB : B≠0) (hC : C≠0) (hD : D≠0) :
    (WeightedFourTermSolutions A B C D).Finite := by
  obtain ⟨F,hF,hproper,hcover⟩ := weighted_four_term_proper_cover3 A B C D hA hB hC hD
  have hf : (⋃ P∈F,weightedFourTermProperFiber3 A B C D P).Finite :=
    hF.biUnion (fun P hPF => weighted_four_term_proper_fiber_finite3 A B C D hA hB hC hD P (hproper P hPF))
  apply hf.subset
  intro p hp
  obtain ⟨P,hPF,hpP⟩ := hcover p hp
  exact Set.mem_iUnion.mpr ⟨P,Set.mem_iUnion.mpr ⟨hPF,hp,hpP⟩⟩

end JSP000334
