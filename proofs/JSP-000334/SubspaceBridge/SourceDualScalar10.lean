import Mathlib.LinearAlgebra.Matrix.ToLin
namespace CompoundFeasibility.SourceOriginalDual10

theorem scalar_nonzero_iff (K : Type*) [Field K] (d x y : K)
    (hd : d ≠ 0) (hxy : x = d*y) : x ≠ 0 ↔ y ≠ 0 := by
  subst x
  constructor
  · intro h
    exact (mul_ne_zero_iff.mp h).2
  · intro hy
    exact mul_ne_zero hd hy

theorem linear_row_nonzero_iff (K : Type*) [Field K] (I : Type*)
    (d : K) (x y : I → K) (F : (I → K) →ₗ[K] K)
    (hd : d ≠ 0) (hxy : ∀ i, x i = d*y i) : F x ≠ 0 ↔ F y ≠ 0 := by
  have hv : x = d • y := funext hxy
  have he : F x = d*F y := by rw [hv,map_smul,smul_eq_mul]
  exact scalar_nonzero_iff K d (F x) (F y) hd he

end CompoundFeasibility.SourceOriginalDual10
