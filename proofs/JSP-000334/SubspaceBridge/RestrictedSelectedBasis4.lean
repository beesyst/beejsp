import SubspaceBridge.RestrictedIntegerCoordinates4
import SubspaceBridge.SelectedRestriction4
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedSelectedBasis4
open RestrictedRows4 RestrictedWeightOrder4 SelectedRestriction4 RestrictedIntegerCoordinates4
noncomputable section

theorem rowCoordinates4_change_basis {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 4 → K)) (b b' : Basis (Fin d) K P)
    (A : Matrix (Fin 4) (Fin 4) K) :
    rowCoordinates4 P b' A = rowCoordinates4 P b A * b.toMatrix b' := by
  ext i k
  let f : P →ₗ[K] K := (LinearMap.proj i).comp ((Matrix.toLin' A).comp P.subtype)
  have h := congrArg f (b.sum_repr (b' k))
  change f (b' k) = ∑ a, f (b a) * b.repr (b' k) a
  simpa only [map_sum,map_smul,smul_eq_mul,mul_comm] using h.symm

theorem selected_basis_matrix_det4 {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 4 → K)) (b b' : Basis (Fin d) K P)
    (A : Matrix (Fin 4) (Fin 4) K) (c : Fin 4 → ℝ)
    (hfull : Submodule.span K (Set.range (rowCoordinates4 P b A).row) = ⊤) :
    (Matrix.of (fun k => rowCoordinates4 P b' A
      (weightOrder4 c (selectedIndex4 (rowCoordinates4 P b A) c hfull k)))).det ≠ 0 := by
  let T := b.toMatrix b'
  have hT : T.det ≠ 0 := by
    have h : T.det * (b'.toMatrix b).det = 1 := by
      rw [← Matrix.det_mul,Basis.toMatrix_mul_toMatrix_flip,Matrix.det_one]
    intro hz
    rw [hz,zero_mul] at h
    exact zero_ne_one h
  have he : Matrix.of (fun k => rowCoordinates4 P b' A
      (weightOrder4 c (selectedIndex4 (rowCoordinates4 P b A) c hfull k))) =
      selectedMatrix4 (rowCoordinates4 P b A) c hfull * T := by
    ext k a
    exact congrFun (congrFun (rowCoordinates4_change_basis P b b' A)
      (weightOrder4 c (selectedIndex4 (rowCoordinates4 P b A) c hfull k))) a
  rw [he,Matrix.det_mul]
  exact mul_ne_zero (selectedMatrix4_det_ne_zero _ c hfull) hT

def finiteSelectedMatrix4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) (c : Fin 4 → ℝ) :
    Matrix (Fin (Module.finrank ℚ P)) (Fin (Module.finrank ℚ P)) ℚ :=
  fun k => rowCoordinates4 P (baseRationalBasis4 P hP) A
    (weightOrder4 c (selectedIndex4 (rationalRowCoordinates4 P A) c (rationalRowCoordinates4_span P A hA) k))

theorem finiteSelectedMatrix4_det_ne_zero (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) (c : Fin 4 → ℝ) :
    (finiteSelectedMatrix4 P hP A hA c).det ≠ 0 :=
  selected_basis_matrix_det4 P (Module.finBasis ℚ P) (baseRationalBasis4 P hP) A c
    (rationalRowCoordinates4_span P A hA)

end
end CompoundFeasibility.RestrictedSelectedBasis4
