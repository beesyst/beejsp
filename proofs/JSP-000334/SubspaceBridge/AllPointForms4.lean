import SubspaceBridge.AllPointSourceExtraction4
open scoped BigOperators Matrix
namespace JSP000334

def retainedIntegerMatrix4 (k : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => if i=k then 1 else if i=j then 1 else 0

theorem retained_integer_matrix_det4 (k : Fin 4) : (retainedIntegerMatrix4 k).det=1 := by
  have he : retainedIntegerMatrix4 k =
      Matrix.updateRow (1 : Matrix (Fin 4) (Fin 4) ℤ) k
        (∑ j : Fin 4,(1 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) j) := by
    ext i j
    by_cases hi : i=k <;> simp [retainedIntegerMatrix4,Matrix.updateRow,hi,Matrix.one_apply]
  rw [he,Matrix.det_updateRow_sum]
  simp

theorem retained_integer_matrix_apply4 (k i : Fin 4) (z : Fin 4 → ℤ) :
    (retainedIntegerMatrix4 k *ᵥ z) i=if i=k then ∑ j,z j else z i := by
  by_cases hi : i=k
  · simp [Matrix.mulVec,dotProduct,retainedIntegerMatrix4,hi]
  · simp [Matrix.mulVec,dotProduct,retainedIntegerMatrix4,hi]

end JSP000334
