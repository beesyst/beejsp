import SubspaceBridge.BinaryIntegerBridge2
open scoped BigOperators Classical
namespace JSP000334

def binaryKernelVector (V : Fin 2 → ℤ) : Fin 2 → ℤ := ![V 1,-V 0]

theorem binary_kernel_vector_nonzero (V : Fin 2 → ℤ) (hV : ∃ i,V i ≠ 0) :
    ∃ i,binaryKernelVector V i ≠ 0 := by
  by_contra hh
  push_neg at hh
  obtain ⟨i,hi⟩ := hV
  have h0 := hh 0
  have h1 := hh 1
  simp only [binaryKernelVector,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
    neg_eq_zero] at h0 h1
  fin_cases i <;> simp_all [binaryKernelVector]

theorem binary_kernel_vector_orthogonal (V : Fin 2 → ℤ) :
    (∑ i : Fin 2,V i*binaryKernelVector V i) = 0 := by
  simp [Fin.sum_univ_two,binaryKernelVector]
  ring

theorem binary_kernel_vector_primitive (V : Fin 2 → ℤ)
    (hV : Ideal.span (Set.range V)=⊤) :
    Int.gcd (binaryKernelVector V 0) (binaryKernelVector V 1)=1 := by
  simpa [binaryKernelVector,Int.gcd_comm] using binary_primitive_gcd V hV

theorem binary_kernel_vector_free (V : Fin 2 → ℤ) (k : Fin 2) (hk : V k ≠ 0) :
    binaryKernelVector V k.rev ≠ 0 := by
  fin_cases k <;> simpa [binaryKernelVector] using hk

theorem binary_kernel_vector_normalized (V : Fin 2 → ℤ) (k i : Fin 2) (hk : V k ≠ 0) :
    (binaryKernelVector V i : ℚ) = (binaryKernelVector V k.rev : ℚ)*
      (if i=k then -(V k.rev : ℚ)/(V k : ℚ) else 1) := by
  have hq : (V k : ℚ) ≠ 0 := by exact_mod_cast hk
  fin_cases k <;> fin_cases i <;> simp_all [binaryKernelVector]
  all_goals field_simp <;> ring

theorem binary_kernel_vector_spans (V : Fin 2 → ℤ) (hV : ∃ i,V i ≠ 0)
    (x : Fin 2 → ℚ) (hx : (∑ i : Fin 2,(V i : ℚ)*x i)=0) :
    ∃ t : ℚ, ∀ i,x i=t*(binaryKernelVector V i : ℚ) := by
  rw [Fin.sum_univ_two] at hx
  by_cases h0 : V 0 = 0
  · have h1 : V 1 ≠ 0 := by
      obtain ⟨i,hi⟩ := hV
      fin_cases i <;> simp_all
    have h1q : (V 1 : ℚ) ≠ 0 := by exact_mod_cast h1
    have hx1 : x 1=0 := by
      simp only [h0,Int.cast_zero,zero_mul,zero_add] at hx
      exact (mul_eq_zero.mp hx).resolve_left h1q
    refine ⟨x 0/(V 1 : ℚ),?_⟩
    intro i
    have hi : i=0 ∨ i=1 := by omega
    rcases hi with rfl | rfl <;> simp [binaryKernelVector,h0,hx1]
    field_simp
  · have h0q : (V 0 : ℚ) ≠ 0 := by exact_mod_cast h0
    refine ⟨-x 1/(V 0 : ℚ),?_⟩
    intro i
    have hi : i=0 ∨ i=1 := by omega
    rcases hi with rfl | rfl <;> simp [binaryKernelVector]
    · field_simp
      nlinarith [hx]
    · field_simp

end JSP000334
