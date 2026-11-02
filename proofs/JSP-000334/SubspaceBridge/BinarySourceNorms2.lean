import SubspaceBridge.BinaryIntegerSourceBounds2
open scoped BigOperators Classical Matrix
namespace JSP000334

theorem binary_vector_value_integer (L : Matrix (Fin 2) (Fin 2) ℤ) (z : Fin 2 → ℤ) (i : Fin 2) :
    binaryLocalVectorValue L z i=((∑ j : Fin 2,L i j*z j : ℤ) : ℚ) := by
  simp [binaryLocalVectorValue]

theorem binary_pattern_value_nonzero (B C : ℚ) (d : ℕ) (hd : 0<d) (b c : ℤ)
    (hb : (b : ℚ)=(d : ℚ)*B) (hc : (c : ℚ)=(d : ℚ)*C) (k i : Fin 2) (z : Fin 2 → ℤ)
    (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hs : B*(z 0 : ℚ)+C*(z 1 : ℚ) ≠ 0) :
    binaryLocalVectorValue (binaryIntegerRetained2 d b c k) z i ≠ 0 := by
  rw [binary_integer_pattern_value B C d b c hb hc]
  apply mul_ne_zero (by exact_mod_cast (ne_of_gt hd))
  have h0q : (z 0 : ℚ) ≠ 0 := by exact_mod_cast h0
  have h1q : (z 1 : ℚ) ≠ 0 := by exact_mod_cast h1
  fin_cases k <;> fin_cases i <;>
    simp_all [weightedRetainedMatrix2,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem binary_pattern_local_bounds (B C : ℚ) (d : ℕ) (hd : 0<d) (b c : ℤ)
    (hb : (b : ℚ)=(d : ℚ)*B) (hc : (c : ℚ)=(d : ℚ)*C) (k : Fin 2) (z : Fin 2 → ℤ)
    (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hs : B*(z 0 : ℚ)+C*(z 1 : ℚ) ≠ 0) (tau : Fin 3) (i : Fin 2) :
    let a := rothLocalAbs tau (binaryLocalVectorValue (binaryIntegerRetained2 d b c k) z i)
    0<a ∧ a⁻¹≤binaryIntegerFormConstant d b c*(archPairHeight z : ℝ) ∧
    (tau ≠ 0 → a≤1) ∧
    (tau=0 → 1≤a ∧ a≤binaryIntegerFormConstant d b c*(archPairHeight z : ℝ)) := by
  let L := binaryIntegerRetained2 d b c k
  let n : ℤ := ∑ j : Fin 2,L i j*z j
  have he : binaryLocalVectorValue L z i=(n : ℚ) := binary_vector_value_integer L z i
  have hn : n ≠ 0 := by
    intro hz
    have hh := binary_pattern_value_nonzero B C d hd b c hb hc k i z h0 h1 hs
    change binaryLocalVectorValue L z i ≠ 0 at hh
    rw [he,hz,Int.cast_zero] at hh
    exact hh rfl
  have hl := binary_integer_norm_bounds n hn tau
  have harch : |(n : ℝ)|=rothLocalAbs 0 (binaryLocalVectorValue L z i) := by
    rw [he]
    simp [rothLocalAbs]
  have hu := binary_integer_pattern_arch_bound d b c k i z
  change rothLocalAbs 0 (binaryLocalVectorValue L z i)≤_ at hu
  change 0<rothLocalAbs tau (binaryLocalVectorValue L z i) ∧ _
  rw [he]
  refine ⟨hl.1,hl.2.1.trans (harch.le.trans hu),hl.2.2,?_⟩
  intro ht
  subst tau
  constructor
  · have hh : (1 : ℝ)≤(n.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hn
    simpa only [Int.cast_natAbs,Int.cast_abs] using hh
  · simpa only [he] using hu

end JSP000334
