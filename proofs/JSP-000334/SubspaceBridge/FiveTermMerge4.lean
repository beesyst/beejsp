import SubspaceBridge.FiveTermDegeneracy4
namespace JSP000334
open scoped BigOperators Matrix

theorem five_term_merge_first14 (x : Fin 5 → ℚ) (hx : Nondegenerate x) :
    Nondegenerate (![x 0+x 1,x 2,x 3,x 4] : Fin 4 → ℚ) := by
  let f : Fin 5 → Fin 4 := ![0,0,1,2,3]
  have hf : Function.Surjective f := by
    intro j
    fin_cases j
    · exact ⟨0,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
  have hh := five_term_nondegenerate_coarsen4 x hx f hf
  convert hh using 1
  ext j
  fin_cases j <;> simp [f,Fin.sum_univ_succ,add_assoc]

theorem five_term_merge_first24 (x : Fin 5 → ℚ) (hx : Nondegenerate x) :
    Nondegenerate (![x 0+x 2,x 1,x 3,x 4] : Fin 4 → ℚ) := by
  let f : Fin 5 → Fin 4 := ![0,1,0,2,3]
  have hf : Function.Surjective f := by
    intro j
    fin_cases j
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
  have hh := five_term_nondegenerate_coarsen4 x hx f hf
  convert hh using 1
  ext j
  fin_cases j <;> simp [f,Fin.sum_univ_succ,add_assoc]

theorem five_term_merge_first34 (x : Fin 5 → ℚ) (hx : Nondegenerate x) :
    Nondegenerate (![x 0+x 3,x 1,x 2,x 4] : Fin 4 → ℚ) := by
  let f : Fin 5 → Fin 4 := ![0,1,2,0,3]
  have hf : Function.Surjective f := by
    intro j
    fin_cases j
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨4,rfl⟩
  have hh := five_term_nondegenerate_coarsen4 x hx f hf
  convert hh using 1
  ext j
  fin_cases j <;> simp [f,Fin.sum_univ_succ,add_assoc]

theorem five_term_merge_pair124 (x : Fin 5 → ℚ) (hx : Nondegenerate x) :
    Nondegenerate (![x 0,x 1+x 2,x 3,x 4] : Fin 4 → ℚ) := by
  let f : Fin 5 → Fin 4 := ![0,1,1,2,3]
  have hf : Function.Surjective f := by
    intro j
    fin_cases j
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
  have hh := five_term_nondegenerate_coarsen4 x hx f hf
  convert hh using 1
  ext j
  fin_cases j <;> simp [f,Fin.sum_univ_succ,add_assoc]

theorem five_term_merge_pair134 (x : Fin 5 → ℚ) (hx : Nondegenerate x) :
    Nondegenerate (![x 0,x 1+x 3,x 2,x 4] : Fin 4 → ℚ) := by
  let f : Fin 5 → Fin 4 := ![0,1,2,1,3]
  have hf : Function.Surjective f := by
    intro j
    fin_cases j
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨4,rfl⟩
  have hh := five_term_nondegenerate_coarsen4 x hx f hf
  convert hh using 1
  ext j
  fin_cases j <;> simp [f,Fin.sum_univ_succ,add_assoc]

theorem five_term_merge_pair234 (x : Fin 5 → ℚ) (hx : Nondegenerate x) :
    Nondegenerate (![x 0,x 2+x 3,x 1,x 4] : Fin 4 → ℚ) := by
  let f : Fin 5 → Fin 4 := ![0,2,1,1,3]
  have hf : Function.Surjective f := by
    intro j
    fin_cases j
    · exact ⟨0,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨4,rfl⟩
  have hh := five_term_nondegenerate_coarsen4 x hx f hf
  convert hh using 1
  ext j
  fin_cases j <;> simp [f,Fin.sum_univ_succ,add_assoc]

end JSP000334
