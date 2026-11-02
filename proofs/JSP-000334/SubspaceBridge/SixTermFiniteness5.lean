import SubspaceBridge.SixTermCoefficientFiber5
namespace JSP000334
open scoped BigOperators Matrix

def sixTermProperFiber5 (P : Submodule ℚ (Fin 5 → ℚ)) : Set (Fin 6 → ℚ) :=
  {x∈normalizedRelations fixedSUnitGroup 5 | (fun i : Fin 5 => x i.castSucc)∈P}

theorem six_term_proper_fiber_finite5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : P≠⊤) :
    (sixTermProperFiber5 P).Finite := by
  obtain ⟨b,hb,hann⟩ := six_term_proper_annihilator5 P hP
  apply (six_term_coefficient_fiber_finite5 b hb).subset
  intro x hx
  exact ⟨hx.1,hann _ hx.2⟩

theorem fixed_six_term_finite : (normalizedRelations fixedSUnitGroup 5).Finite := by
  obtain ⟨F,hF,hproper,hcover⟩ := source_six_term_finite_cover5
  have hU : (⋃ P∈F,sixTermProperFiber5 P).Finite :=
    hF.biUnion (fun P hPF => six_term_proper_fiber_finite5 P (hproper P hPF))
  apply hU.subset
  intro x hx
  obtain ⟨P,hPF,hxP⟩ := hcover x hx
  exact Set.mem_iUnion.mpr ⟨P,Set.mem_iUnion.mpr ⟨hPF,hx,hxP⟩⟩

end JSP000334
