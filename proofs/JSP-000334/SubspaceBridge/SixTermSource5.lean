import SubspaceBridge.SixTermProjection5
namespace JSP000334
open scoped BigOperators Matrix
theorem six_term_proper_annihilator5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : P≠⊤) :
    ∃ b : Fin 5 → ℚ,(∃ i,b i≠0) ∧ ∀ y∈P,∑ i,b i*y i=0 := by
  obtain ⟨f,hf,hker⟩ := P.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hP)
  let b (i : Fin 5) := f (Pi.single i 1)
  have heval (y : Fin 5 → ℚ) : f y=∑ i,b i*y i := by
    have hy : y=∑ i,y i • Pi.single i 1 := by
      ext j
      simp [Finset.sum_apply,Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_smul,smul_eq_mul,b,mul_comm]
  refine ⟨b,?_,?_⟩
  · by_contra hnone
    have hz (i : Fin 5) : b i=0 := by
      by_contra hi
      exact hnone ⟨i,hi⟩
    apply hf
    apply LinearMap.ext
    intro y
    change f y=0
    rw [heval]
    simp only [hz,zero_mul,Finset.sum_const_zero]
  · intro y hy
    exact (heval y).symm.trans (hker hy)
end JSP000334
