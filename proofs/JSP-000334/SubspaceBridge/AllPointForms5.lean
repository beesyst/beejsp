import SubspaceBridge.AllPointFixedSourceFamily5
open scoped BigOperators Matrix
namespace JSP000334

def retainedIntegerMatrix5 (k : Fin 5) : Matrix (Fin 5) (Fin 5) ℤ :=
  fun i j => if i=k then 1 else if i=j then 1 else 0

theorem retained_integer_matrix_det5 (k : Fin 5) : (retainedIntegerMatrix5 k).det=1 := by
  have he : retainedIntegerMatrix5 k =
      Matrix.updateRow (1 : Matrix (Fin 5) (Fin 5) ℤ) k
        (∑ j : Fin 5,(1 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) j) := by
    ext i j
    by_cases hi : i=k <;> simp [retainedIntegerMatrix5,Matrix.updateRow,hi,Matrix.one_apply]
  rw [he,Matrix.det_updateRow_sum]
  simp

theorem retained_integer_matrix_apply5 (k i : Fin 5) (z : Fin 5 → ℤ) :
    (retainedIntegerMatrix5 k *ᵥ z) i=if i=k then ∑ j,z j else z i := by
  by_cases hi : i=k
  · simp [Matrix.mulVec,dotProduct,retainedIntegerMatrix5,hi]
  · simp [Matrix.mulVec,dotProduct,retainedIntegerMatrix5,hi]

end JSP000334
