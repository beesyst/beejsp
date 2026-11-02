import SubspaceBridge.SourceDualScalar10
import SubspaceBridge.OriginalDual10
open scoped BigOperators Matrix
namespace CompoundFeasibility.SourceOriginalDual10
open OriginalDual10
noncomputable section

def rowLinear (K : Type*) [Field K] (I : Type*) [Fintype I] (r : I → K) :
    (I → K) →ₗ[K] K where
  toFun x := ∑ i, r i*x i
  map_add' x y := by simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem matrix_row_linear_apply (K : Type*) [Field K] (I : Type*) [Fintype I]
    (B : Matrix I I K) (i : I) (x : I → K) :
    rowLinear K I (fun k => B k i) x = (B.transpose *ᵥ x) i := rfl

theorem original_cofactor_pointwise {n : ℕ} (K : Type*) [Field K] [CharZero K]
    (u : Fin (n+1) → Fin (n+1) → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) :
    ∀ i, (integerLastDual10 u i : K) = ((Matrix.det u : ℤ) : K)*
      (lastDual10 (fun j i => (u j i : ℚ)) hu i : K) :=
  cofactor_dual_cast10 u hu

theorem original_cofactor_linear_nonzero {n : ℕ} (K : Type*) [Field K] [CharZero K]
    (u : Fin (n+1) → Fin (n+1) → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ)))
    (F : (Fin (n+1) → K) →ₗ[K] K) :
    F (fun i => (integerLastDual10 u i : K)) ≠ 0 ↔
      F (fun i => (lastDual10 (fun j i => (u j i : ℚ)) hu i : K)) ≠ 0 := by
  have hd : ((Matrix.det u : ℤ) : K) ≠ 0 := by
    exact_mod_cast integerFrame10_det_ne_zero u hu
  exact linear_row_nonzero_iff K (Fin (n+1)) _ _ _ F hd (original_cofactor_pointwise K u hu)

theorem original_cofactor_matrix_nonzero {n : ℕ} (K : Type*) [Field K] [CharZero K]
    (B : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (u : Fin (n+1) → Fin (n+1) → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) (i : Fin (n+1)) :
    (B.transpose *ᵥ (fun k => (integerLastDual10 u k : K))) i ≠ 0 ↔
      (B.transpose *ᵥ (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : K))) i ≠ 0 := by
  exact original_cofactor_linear_nonzero K u hu (rowLinear K _ (fun k => B k i))

end
end CompoundFeasibility.SourceOriginalDual10
