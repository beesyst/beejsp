import SubspaceBridge.FourTermCoefficientFiber3
namespace JSP000334

def fourTermProperFiber (P : Submodule ℚ (Fin 3 → ℚ)) : Set (Fin 4 → ℚ) :=
  {x | x ∈ normalizedRelations fixedSUnitGroup 3 ∧ ![1,x 1,x 2] ∈ P}

theorem four_term_proper_fiber_finite (P : Submodule ℚ (Fin 3 → ℚ)) (hP : P≠⊤) :
    (fourTermProperFiber P).Finite := by
  obtain ⟨a0,a1,a2,ha,hann⟩ := four_term_proper_annihilator P hP
  apply (four_term_coefficient_fiber_finite a0 a1 a2 ha).subset
  intro x hx
  refine ⟨hx.1,?_⟩
  have he : a0*1+a1*x 1+a2*x 2=0 := hann _ hx.2
  simpa only [hx.1.1] using he

theorem fixed_four_term_finite :
    (normalizedRelations fixedSUnitGroup 3).Finite := by
  obtain ⟨F,hF,hproper,hcover⟩ := source_four_term_finite_cover3
  have hU : (⋃ P∈F,fourTermProperFiber P).Finite :=
    hF.biUnion (fun P hP => four_term_proper_fiber_finite P (hproper P hP))
  apply hU.subset
  intro x hx
  obtain ⟨w,s,_,_,_,_,hscale,_,P,hPF,hwP⟩ := hcover x hx
  have hxP := four_term_original_mem hx P w s hscale hwP
  exact Set.mem_iUnion.mpr ⟨P,Set.mem_iUnion.mpr ⟨hPF,⟨hx,hxP⟩⟩⟩

end JSP000334
