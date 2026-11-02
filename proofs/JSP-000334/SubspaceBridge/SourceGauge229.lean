import SubspaceBridge.SourceDualBody222
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSecondMinimum229
open SourceDualAnnihilation222

theorem dualGauge_coordinates229 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (d : ℝ) (hd : 0 < d) (A : Fin 10 → ℝ) (hA : ∀ i, 0 < A i) (z : Fin 10 → ℝ) :
    dualGauge222 L hL d hd A hA z =
      coordinateGauge10 (dualCoordinates222 L hL d hd A hA) z := by
  rfl

end CompoundFeasibility.SourceSecondMinimum229
