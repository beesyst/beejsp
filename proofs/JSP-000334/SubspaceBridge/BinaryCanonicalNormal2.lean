import SubspaceBridge.BinaryAnalyticContradiction2
open scoped BigOperators Classical
namespace JSP000334

def binaryPairNormal (z : Fin 2 → ℤ) : Fin 2 → ℤ := ![-z 1,z 0]

theorem binary_primitive_pair_ideal (z : Fin 2 → ℤ) (hz : PrimitivePair z) :
    Ideal.span (Set.range z)=⊤ := by
  obtain ⟨c,hc⟩ := hz
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← hc]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

theorem binary_pair_normal_primitive (z : Fin 2 → ℤ) (hz : PrimitivePair z) :
    PrimitivePair (binaryPairNormal z) := by
  obtain ⟨c,hc⟩ := hz
  refine ⟨![-c 1,c 0],?_⟩
  simp only [Fin.sum_univ_two] at hc ⊢
  simp only [binaryPairNormal,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
  nlinarith

theorem binary_pair_normal_ideal (z : Fin 2 → ℤ) (hz : PrimitivePair z) :
    Ideal.span (Set.range (binaryPairNormal z))=⊤ :=
  binary_primitive_pair_ideal _ (binary_pair_normal_primitive z hz)

theorem binary_pair_normal_nonzero (z : Fin 2 → ℤ) (hz : PrimitivePair z) :
    ∃ i,binaryPairNormal z i ≠ 0 := by
  by_contra hh
  push_neg at hh
  obtain ⟨c,hc⟩ := binary_pair_normal_primitive z hz
  simp [hh] at hc

theorem binary_pair_normal_vector (z : Fin 2 → ℤ) :
    binaryKernelVector (binaryPairNormal z)=z := by
  ext i
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl | rfl <;> simp [binaryKernelVector,binaryPairNormal]

theorem binary_pair_normal_height (z : Fin 2 → ℤ) :
    (binaryNormalHeight (binaryPairNormal z) : ℝ)=(archPairHeight z : ℝ) := by
  simp [binaryNormalHeight,binaryPairNormal,archPairHeight,max_comm,Int.cast_natAbs,Int.cast_abs]

end JSP000334
