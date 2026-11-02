import SubspaceBridge.SourceOriginalIndex212
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceOriginalSatz212
open SourceOriginalVariable10 SourceRelativeIndex6

variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset SourceSelectedSet10.MixedIndex10}

theorem original_frame_matrix_eq212 (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    Matrix.of (fun j => (originalFrame212 D j : Fin 10 → ℤ)) =
      (Matrix.of D.u : Matrix (Fin 10) (Fin 10) ℤ) := by
  ext i j
  rfl

end CompoundFeasibility.SourceOriginalSatz212
