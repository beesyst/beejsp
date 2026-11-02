import SubspaceBridge.SourceDualRows10
import SubspaceBridge.SchlickeweiEquation4116
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceOriginalNorm214
open OriginalDual10 SourceOriginalDual10

theorem signed_integer_norm214 (K : Type*) [NormedField K] (d : ℤ) :
    ‖(d : K)‖ = ‖(d.natAbs : K)‖ :=
  (SchlickeweiEquation4116.norm_natAbs_cast6 d).symm

theorem cofactor_signed_linear214 {n : ℕ} (K : Type*) [NormedField K] [CharZero K]
    (u : Fin (n+1) → Fin (n+1) → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ)))
    (F : (Fin (n+1) → K) →ₗ[K] K) :
    F (fun k => (integerLastDual10 u k : K)) =
      ((Matrix.det u : ℤ) : K)*F (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : K)) := by
  have hv : (fun k => (integerLastDual10 u k : K)) =
      ((Matrix.det u : ℤ) : K) • (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : K)) :=
    funext (cofactor_dual_cast10 u hu)
  rw [hv,map_smul,smul_eq_mul]

theorem cofactor_signed_matrix214 {n : ℕ} (K : Type*) [NormedField K] [CharZero K]
    (B : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (u : Fin (n+1) → Fin (n+1) → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) (i : Fin (n+1)) :
    (B⁻¹.transpose *ᵥ (fun k => (integerLastDual10 u k : K))) i =
      ((Matrix.det u : ℤ) : K)*
        (B⁻¹.transpose *ᵥ (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : K))) i := by
  exact cofactor_signed_linear214 K u hu (rowLinear K _ (fun k => B⁻¹ k i))

theorem cofactor_norm_linear214 {n : ℕ} (K : Type*) [NormedField K] [CharZero K]
    (u : Fin (n+1) → Fin (n+1) → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ)))
    (N : ℕ) (hN : N = (Matrix.det u).natAbs) (F : (Fin (n+1) → K) →ₗ[K] K) :
    ‖F (fun k => (integerLastDual10 u k : K))‖ =
      ‖F (fun k => (N : K)*(lastDual10 (fun j i => (u j i : ℚ)) hu k : K))‖ := by
  have hs : F (fun k => (N : K)*(lastDual10 (fun j i => (u j i : ℚ)) hu k : K)) =
      (N : K)*F (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : K)) := by
    change F ((N : K) • (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : K))) = _
    rw [map_smul,smul_eq_mul]
  rw [cofactor_signed_linear214 K u hu F,hs,norm_mul,norm_mul,hN,
    ← signed_integer_norm214 K (Matrix.det u)]

theorem cofactor_norm_matrix214 {n : ℕ} (K : Type*) [NormedField K] [CharZero K]
    (B : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (u : Fin (n+1) → Fin (n+1) → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ)))
    (N : ℕ) (hN : N = (Matrix.det u).natAbs) (i : Fin (n+1)) :
    ‖(B⁻¹.transpose *ᵥ (fun k => (integerLastDual10 u k : K))) i‖ =
      ‖(B⁻¹.transpose *ᵥ
        (fun k => (N : K)*(lastDual10 (fun j i => (u j i : ℚ)) hu k : K))) i‖ := by
  exact cofactor_norm_linear214 K u hu N hN (rowLinear K _ (fun k => B⁻¹ k i))

end CompoundFeasibility.SourceOriginalNorm214
