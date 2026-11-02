import SubspaceBridge.SourceSelectedCofactor10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSelectedUpper10
open OriginalDual10 SourceSelectedSet10 SchmidtNormal10

theorem integerReal_int_mul10 (g : ℤ) (M : Fin 10 → ℤ) :
    integerReal (fun k => g*M k) = (g : ℝ) • integerReal M := by
  ext k
  change ((g*M k : ℤ) : ℝ) = (g : ℝ)*(M k : ℝ)
  exact Int.cast_mul g (M k)

theorem mixedProduct10_int_mul (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (g : ℤ) (M : Fin 10 → ℤ) (s : MixedIndex10) :
    mixedProduct10 A2 A3 L (fun k => g*M k) s =
      (|(g : ℝ)| * ‖(g : ℚ_[2])‖*‖(g : ℚ_[3])‖)*mixedProduct10 A2 A3 L M s := by
  have hr : (L⁻¹.transpose *ᵥ integerReal (fun k => g*M k)) (s 0) =
      (g : ℝ)*(L⁻¹.transpose *ᵥ integerReal M) (s 0) := by
    rw [integerReal_int_mul10,Matrix.mulVec_smul]
    rfl
  unfold mixedProduct10
  rw [hr,integer_vector_mul10,integer_vector_mul10,abs_mul,norm_mul,norm_mul]
  ring

theorem integer_three_place_scalar10 (g : ℤ) (hg : g ≠ 0) :
    1 ≤ |(g : ℝ)| * ‖(g : ℚ_[2])‖*‖(g : ℚ_[3])‖ := by
  simpa only [Real.norm_eq_abs] using SourceLocalUpper6.integer_g_three_place6 g hg

theorem mixedProduct10_le_int_mul10 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (g : ℤ) (hg : g ≠ 0)
    (M : Fin 10 → ℤ) (s : MixedIndex10) :
    mixedProduct10 A2 A3 L M s ≤ mixedProduct10 A2 A3 L (fun k => g*M k) s := by
  rw [mixedProduct10_int_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (integer_three_place_scalar10 g hg)
    (mixedProduct10_nonneg A2 A3 L M s)

end CompoundFeasibility.SourceSelectedUpper10
