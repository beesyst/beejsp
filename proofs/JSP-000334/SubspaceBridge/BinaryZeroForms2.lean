import SubspaceBridge.BinaryCanonicalNormal2
open scoped BigOperators Classical
namespace JSP000334

noncomputable def binaryCoordinateLine (i : Fin 2) : Submodule ℚ (Fin 2 → ℚ) :=
  LinearMap.ker (LinearMap.proj i)
noncomputable def binaryWeightedForm (B C : ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] ℚ where
  toFun x := B*x 0+C*x 1
  map_add' x y := by simp [mul_add];ring
  map_smul' a x := by simp [mul_add];ring
noncomputable def binaryWeightedLine (B C : ℚ) : Submodule ℚ (Fin 2 → ℚ) :=
  LinearMap.ker (binaryWeightedForm B C)
noncomputable def binaryZeroLines (B C : ℚ) : Finset (Submodule ℚ (Fin 2 → ℚ)) :=
  {binaryCoordinateLine 0,binaryCoordinateLine 1,binaryWeightedLine B C}

theorem binary_coordinate_line_proper (i : Fin 2) : binaryCoordinateLine i ≠ ⊤ := by
  intro he
  have hh : Pi.single i (1 : ℚ) ∈ binaryCoordinateLine i := by rw [he];trivial
  change ((Pi.single i (1 : ℚ)) : Fin 2 → ℚ) i=0 at hh
  simpa using hh

theorem binary_weighted_line_proper (B C : ℚ) (hB : B ≠ 0) : binaryWeightedLine B C ≠ ⊤ := by
  intro he
  have hh : (![1,0] : Fin 2 → ℚ) ∈ binaryWeightedLine B C := by rw [he];trivial
  have hz : B=0 := by simpa [binaryWeightedLine,LinearMap.mem_ker,binaryWeightedForm] using hh
  exact hB hz

theorem binary_zero_lines_proper (B C : ℚ) (hB : B ≠ 0) :
    ∀ P ∈ binaryZeroLines B C,P ≠ ⊤ := by
  intro P hP
  simp only [binaryZeroLines,Finset.mem_insert,Finset.mem_singleton] at hP
  rcases hP with rfl | rfl | rfl
  · exact binary_coordinate_line_proper 0
  · exact binary_coordinate_line_proper 1
  · exact binary_weighted_line_proper B C hB

theorem binary_zero_form_cover (B C : ℚ) (z : Fin 2 → ℤ)
    (hz : z 0=0 ∨ z 1=0 ∨ B*(z 0 : ℚ)+C*(z 1 : ℚ)=0) :
    ∃ P ∈ binaryZeroLines B C,(fun i => (z i : ℚ)) ∈ P := by
  rcases hz with h0 | h1 | hs
  · refine ⟨binaryCoordinateLine 0,by simp [binaryZeroLines],?_⟩
    change (z 0 : ℚ)=0
    simp [h0]
  · refine ⟨binaryCoordinateLine 1,by simp [binaryZeroLines],?_⟩
    change (z 1 : ℚ)=0
    simp [h1]
  · refine ⟨binaryWeightedLine B C,by simp [binaryZeroLines],?_⟩
    exact hs

end JSP000334
