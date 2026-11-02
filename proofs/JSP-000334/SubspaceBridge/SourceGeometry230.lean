import SubspaceBridge.SourceShortPair229
import SubspaceBridge.SourceGauge229
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSecondMinimum230
open SourceDualGeometry219 SourceDualAnnihilation222 SourceSecondMinimum228 SourceSecondMinimum229

def originalDualGroup230 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (q : ℝ) (c2 c3 : Fin 10 → ℝ) : AddSubgroup (Fin 10 → ℤ) :=
  originalSourceGroup10 A2 A3 q c2 c3

theorem originalDualGroup_eq230 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (q : ℝ) (c2 c3 : Fin 10 → ℝ) :
    originalDualGroup230 A2 A3 q c2 c3 = originalSourceGroup10 A2 A3 q c2 c3 := by
  rfl

def originalDualBasis230 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (q : ℝ) (c2 c3 : Fin 10 → ℝ) : Basis (Fin 10) ℝ (Fin 10 → ℝ) :=
  originalDualRealBasis228 A2 A3 q c2 c3

theorem originalDualBasis_eq230 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (q : ℝ) (c2 c3 : Fin 10 → ℝ) :
    originalDualBasis230 A2 A3 q c2 c3 = originalDualRealBasis228 A2 A3 q c2 c3 := by
  rfl

def originalDualCoordinates230 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (q : ℝ)
    (c2 c3 A : Fin 10 → ℝ) (hA : ∀ i, 0 < A i) :
    (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ) :=
  dualCoordinates222 L hL
    (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3)))
    (ZLattice.covolume_pos _ MeasureTheory.volume) A hA

theorem originalDualCoordinates_eq230 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (q : ℝ)
    (c2 c3 A : Fin 10 → ℝ) (hA : ∀ i, 0 < A i) :
    originalDualCoordinates230 A2 A3 L hL q c2 c3 A hA =
      dualCoordinates222 L hL
        (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3)))
        (ZLattice.covolume_pos _ MeasureTheory.volume) A hA := by
  rfl

def originalSecondRadius230 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (q : ℝ)
    (c2 c3 A : Fin 10 → ℝ) (hA : ∀ i, 0 < A i) : ℝ :=
  successiveRadius10 (originalDualBasis230 A2 A3 q c2 c3)
    (originalDualCoordinates230 A2 A3 L hL q c2 c3 A hA) (1 : Fin 10)

theorem originalSecondRadius_eq230 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (q : ℝ)
    (c2 c3 A : Fin 10 → ℝ) (hA : ∀ i, 0 < A i) :
    originalSecondRadius230 A2 A3 L hL q c2 c3 A hA =
      successiveRadius10 (originalDualRealBasis228 A2 A3 q c2 c3)
        (dualCoordinates222 L hL
          (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3)))
          (ZLattice.covolume_pos _ MeasureTheory.volume) A hA) (1 : Fin 10) := by
  rfl

end CompoundFeasibility.SourceSecondMinimum230
