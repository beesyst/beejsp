import SubspaceBridge.FiveTermCoefficientFiber4
namespace JSP000334
open scoped BigOperators Matrix

def fiveTermProperFiber4 (P : Submodule ℚ (Fin 4 → ℚ)) : Set (Fin 5 → ℚ) :=
  {x | x∈normalizedRelations fixedSUnitGroup 4 ∧ (fun i : Fin 4 => x i.castSucc)∈P}

theorem five_term_proper_fiber_finite4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : P≠⊤) :
    (fiveTermProperFiber4 P).Finite := by
  obtain ⟨b0,b1,b2,b3,hb,hann⟩ := five_term_proper_annihilator4 P hP
  apply (five_term_coefficient_fiber_finite4 b0 b1 b2 b3 hb).subset
  intro x hx
  exact ⟨hx.1,hann _ hx.2⟩

theorem fixed_five_term_finite : (normalizedRelations fixedSUnitGroup 4).Finite := by
  obtain ⟨F,hF,hproper,hcover⟩ := source_five_term_finite_cover4
  have hU : (⋃ P∈F,fiveTermProperFiber4 P).Finite :=
    hF.biUnion (fun P hPF => five_term_proper_fiber_finite4 P (hproper P hPF))
  apply hU.subset
  intro x hx
  obtain ⟨P,hPF,hxP⟩ := hcover x hx
  exact Set.mem_iUnion.mpr ⟨P,Set.mem_iUnion.mpr ⟨hPF,hx,hxP⟩⟩

end JSP000334
