import SubspaceBridge.SourceFiniteDualLower10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceHeightEnvelope10
open SchmidtNormal10

theorem actual_same_normal_mixed_lower10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ (M : Fin 10 → ℤ) (i0 i2 i3 : Fin 10),
      (L⁻¹.transpose *ᵥ integerReal M) i0 ≠ 0 →
      ((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (M k : ℚ_[2]))) i2 ≠ 0 →
      ((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k => (M k : ℚ_[3]))) i3 ≠ 0 →
      C ≤ |(L⁻¹.transpose *ᵥ integerReal M) i0| *
        ‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (M k : ℚ_[2]))) i2‖ *
        ‖((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k => (M k : ℚ_[3]))) i3‖ *
        (max 1 (normalHeight10 M : ℝ))^(D+2) := by
  obtain ⟨C0,hC0,D,h0⟩ := actual_real_dual_liouville10 L hL hAlg
  obtain ⟨C2,hC2,hp2⟩ := actual_p2_dual_lower10 A2 h2
  obtain ⟨C3,hC3,hp3⟩ := actual_p3_dual_lower10 A3 h3
  refine ⟨C0*C2*C3,mul_pos (mul_pos hC0 hC2) hC3,D,?_⟩
  intro M i0 i2 i3 hn0 hn2 hn3
  have hh : 0 ≤ max 1 (normalHeight10 M : ℝ) := zero_le_one.trans (le_max_left _ _)
  have h02 := mul_le_mul (h0 M i0 hn0) (hp2 M i2 hn2)
    hC2.le (mul_nonneg (abs_nonneg _) (pow_nonneg hh D))
  have h023 := mul_le_mul h02 (hp3 M i3 hn3)
    hC3.le (mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hh D))
      (mul_nonneg (norm_nonneg _) hh))
  calc
    C0*C2*C3 ≤ _ := h023
    _ = _ := by rw [pow_add,pow_two]; ring

end CompoundFeasibility.SourceHeightEnvelope10
