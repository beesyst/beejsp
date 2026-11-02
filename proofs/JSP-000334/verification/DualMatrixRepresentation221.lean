import SubspaceBridge.SourceDualLattice219
open scoped BigOperators Matrix
namespace M221MatrixRepresentation
open CompoundFeasibility.SourceDualGeometry219

theorem matrix_of221 (f : Fin 10 → Fin 10 → ℚ) :
    (Matrix.of f : Matrix (Fin 10) (Fin 10) ℚ) = (f : Matrix (Fin 10) (Fin 10) ℚ) := by
  rfl

theorem inverse_of221 (f : Fin 10 → Fin 10 → ℚ) :
    let W : Matrix (Fin 10) (Fin 10) ℚ := f
    (Matrix.of f : Matrix (Fin 10) (Fin 10) ℚ)⁻¹ = W⁻¹ := by
  let W : Matrix (Fin 10) (Fin 10) ℚ := f
  have h : (Matrix.of f : Matrix (Fin 10) (Fin 10) ℚ) = W := matrix_of221 f
  exact congrArg (fun M : Matrix (Fin 10) (Fin 10) ℚ => M⁻¹) h

theorem dual_column221 (W : Matrix (Fin 10) (Fin 10) ℚ) (j : Fin 10) :
    dualVector219 W j = (fun i => W⁻¹ i j) := by
  rfl

theorem raw_column221 (f : Fin 10 → Fin 10 → ℚ) (j : Fin 10) :
    (fun i => (Matrix.of f : Matrix (Fin 10) (Fin 10) ℚ)⁻¹ i j) =
      dualVector219 (f : Matrix (Fin 10) (Fin 10) ℚ) j := by
  exact (congrArg (fun M : Matrix (Fin 10) (Fin 10) ℚ => fun i => M i j)
    (inverse_of221 f)).trans (dual_column221 f j).symm

end M221MatrixRepresentation
