import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
open scoped BigOperators Matrix
namespace CompoundFeasibility.SourceDualBasis220

theorem inverse_columns220 (W : Matrix (Fin 10) (Fin 10) ℚ) (a : Fin 10 → ℚ) :
    W⁻¹ *ᵥ a = ∑ j, a j • (fun i => W⁻¹ i j) := by
  ext i
  change (∑ j, W⁻¹ i j*a j) = _
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem inverse_reconstruction220 (W : Matrix (Fin 10) (Fin 10) ℚ)
    (hW : IsUnit W) (v : Fin 10 → ℚ) : W⁻¹ *ᵥ (W *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul W ((Matrix.isUnit_iff_isUnit_det W).mp hW),Matrix.one_mulVec]

theorem row_sum_pairing220 (W : Matrix (Fin 10) (Fin 10) ℚ)
    (a z : Fin 10 → ℚ) :
    (∑ i, (∑ j, a j*W j i)*z i) = ∑ j, a j*(∑ i, W j i*z i) := by
  simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

end CompoundFeasibility.SourceDualBasis220
