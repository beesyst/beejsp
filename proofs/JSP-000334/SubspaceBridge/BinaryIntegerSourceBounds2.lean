import SubspaceBridge.BinaryWeightedSourceProduct2
import SubspaceBridge.BinarySourceWeights2
open scoped BigOperators Classical Matrix
namespace JSP000334

noncomputable def binaryIntegerFormConstant (d : ℕ) (b c : ℤ) : ℝ := 1+(d : ℝ)+(b.natAbs : ℝ)+(c.natAbs : ℝ)

theorem binary_integer_norm_bounds (n : ℤ) (hn : n ≠ 0) (tau : Fin 3) :
    0<rothLocalAbs tau (n : ℚ) ∧
    (rothLocalAbs tau (n : ℚ))⁻¹≤|(n : ℝ)| ∧
    (tau ≠ 0 → rothLocalAbs tau (n : ℚ)≤1) := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hpos (v : Fin 3) : 0<rothLocalAbs v (n : ℚ) := by
    rw [← binary_place_norm_cast]
    exact_mod_cast rationalPlaceNorm_pos v hnq
  have h2 := rothNormalAbs_int_finite 1 (by decide) n
  have h3 := rothNormalAbs_int_finite 2 (by decide) n
  have hp := rothInteger_three_place_lower n hn
  have ha : 1≤rothLocalAbs 0 (n : ℚ) := by
    have hh : rothLocalAbs 1 (n : ℚ)*rothLocalAbs 2 (n : ℚ)≤1 :=
      mul_le_one₀ h2 (hpos 2).le h3
    nlinarith [mul_le_mul_of_nonneg_left hh (hpos 0).le]
  have hb2 : 1≤rothLocalAbs 0 (n : ℚ)*rothLocalAbs 1 (n : ℚ) := by
    nlinarith [mul_le_mul_of_nonneg_left h3 (mul_pos (hpos 0) (hpos 1)).le]
  have hb3 : 1≤rothLocalAbs 0 (n : ℚ)*rothLocalAbs 2 (n : ℚ) := by
    nlinarith [mul_le_mul_of_nonneg_left h2 (mul_pos (hpos 0) (hpos 2)).le]
  have harch : rothLocalAbs 0 (n : ℚ)=|(n : ℝ)| := by simp [rothLocalAbs]
  refine ⟨hpos tau,?_,?_⟩
  · rw [← harch]
    have hi : tau=0 ∨ tau=1 ∨ tau=2 := by omega
    rcases hi with rfl | rfl | rfl
    · apply (inv_le_iff_one_le_mul₀ (hpos 0)).mpr
      nlinarith
    · exact (inv_le_iff_one_le_mul₀ (hpos 1)).mpr hb2
    · exact (inv_le_iff_one_le_mul₀ (hpos 2)).mpr hb3
  · intro ht
    exact rothNormalAbs_int_finite tau ht n

theorem binary_integer_pattern_arch_bound (d : ℕ) (b c : ℤ) (k i : Fin 2) (z : Fin 2 → ℤ) :
    rothLocalAbs 0 (binaryLocalVectorValue (binaryIntegerRetained2 d b c k) z i)≤
      binaryIntegerFormConstant d b c*(archPairHeight z : ℝ) := by
  have hz (j : Fin 2) : |(z j : ℝ)|≤(archPairHeight z : ℝ) := by
    have hh : |(z j : ℚ)|≤archPairHeight z := by
      have hj : j=0 ∨ j=1 := by omega
      rcases hj with rfl | rfl
      · exact le_max_left _ _
      · exact le_max_right _ _
    exact_mod_cast hh
  have hH : 0≤(archPairHeight z : ℝ) := (abs_nonneg _).trans (hz 0)
  have hb : |(b : ℝ)|=(b.natAbs : ℝ)  := by simp only [Int.cast_natAbs,Int.cast_abs]
  have hc : |(c : ℝ)|=(c.natAbs : ℝ)  := by simp only [Int.cast_natAbs,Int.cast_abs]
  have hh := abs_add ((b : ℝ)*(z 0 : ℝ)) ((c : ℝ)*(z 1 : ℝ))
  rw [abs_mul,abs_mul,hb,hc] at hh
  have hbz := mul_le_mul_of_nonneg_left (hz 0) (Nat.cast_nonneg b.natAbs : (0 : ℝ)≤b.natAbs)
  have hcz := mul_le_mul_of_nonneg_left (hz 1) (Nat.cast_nonneg c.natAbs : (0 : ℝ)≤c.natAbs)
  have hd (j : Fin 2) := mul_le_mul_of_nonneg_left (hz j) (Nat.cast_nonneg d : (0 : ℝ)≤d)
  fin_cases k <;> fin_cases i <;>
    simp [rothLocalAbs,binaryLocalVectorValue,binaryIntegerRetained2,Fin.sum_univ_two,binaryIntegerFormConstant] <;>
    (try simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ)≤d)]) <;> nlinarith [hd 0,hd 1]

end JSP000334
