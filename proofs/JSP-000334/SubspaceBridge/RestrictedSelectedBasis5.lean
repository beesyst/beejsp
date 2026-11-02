import SubspaceBridge.RestrictedIntegerCoordinates5
import SubspaceBridge.SelectedRestriction5
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedSelectedBasis5
open RestrictedRows5 RestrictedWeightOrder5 SelectedRestriction5 RestrictedIntegerCoordinates5
noncomputable section

theorem rowCoordinates5_change_basis {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 5 → K)) (b b' : Basis (Fin d) K P)
    (A : Matrix (Fin 5) (Fin 5) K) :
    rowCoordinates5 P b' A = rowCoordinates5 P b A * b.toMatrix b' := by
  ext i k
  let f : P →ₗ[K] K := (LinearMap.proj i).comp ((Matrix.toLin' A).comp P.subtype)
  have h := congrArg f (b.sum_repr (b' k))
  change f (b' k) = ∑ a, f (b a) * b.repr (b' k) a
  simpa only [map_sum,map_smul,smul_eq_mul,mul_comm] using h.symm

theorem selected_basis_matrix_det5 {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 5 → K)) (b b' : Basis (Fin d) K P)
    (A : Matrix (Fin 5) (Fin 5) K) (c : Fin 5 → ℝ)
    (hfull : Submodule.span K (Set.range (rowCoordinates5 P b A).row) = ⊤) :
    (Matrix.of (fun k => rowCoordinates5 P b' A
      (weightOrder5 c (selectedIndex5 (rowCoordinates5 P b A) c hfull k)))).det ≠ 0 := by
  let T := b.toMatrix b'
  have hT : T.det ≠ 0 := by
    have h : T.det * (b'.toMatrix b).det = 1 := by
      rw [← Matrix.det_mul,Basis.toMatrix_mul_toMatrix_flip,Matrix.det_one]
    intro hz
    rw [hz,zero_mul] at h
    exact zero_ne_one h
  have he : Matrix.of (fun k => rowCoordinates5 P b' A
      (weightOrder5 c (selectedIndex5 (rowCoordinates5 P b A) c hfull k))) =
      selectedMatrix5 (rowCoordinates5 P b A) c hfull * T := by
    ext k a
    exact congrFun (congrFun (rowCoordinates5_change_basis P b b' A)
      (weightOrder5 c (selectedIndex5 (rowCoordinates5 P b A) c hfull k))) a
  rw [he,Matrix.det_mul]
  exact mul_ne_zero (selectedMatrix5_det_ne_zero _ c hfull) hT

def finiteSelectedMatrix5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (A : Matrix (Fin 5) (Fin 5) ℚ) (hA : A.det = 1) (c : Fin 5 → ℝ) :
    Matrix (Fin (Module.finrank ℚ P)) (Fin (Module.finrank ℚ P)) ℚ :=
  fun k => rowCoordinates5 P (baseRationalBasis5 P hP) A
    (weightOrder5 c (selectedIndex5 (rationalRowCoordinates5 P A) c (rationalRowCoordinates5_span P A hA) k))

theorem finiteSelectedMatrix5_det_ne_zero (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (A : Matrix (Fin 5) (Fin 5) ℚ) (hA : A.det = 1) (c : Fin 5 → ℝ) :
    (finiteSelectedMatrix5 P hP A hA c).det ≠ 0 :=
  selected_basis_matrix_det5 P (Module.finBasis ℚ P) (baseRationalBasis5 P hP) A c
    (rationalRowCoordinates5_span P A hA)

end
end CompoundFeasibility.RestrictedSelectedBasis5
