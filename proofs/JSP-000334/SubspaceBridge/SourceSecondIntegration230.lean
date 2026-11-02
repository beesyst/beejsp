import SubspaceBridge.SourceGeometry230
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSecondMinimum230
open SourceDualGeometry219 SourceDualAnnihilation222 SourceSecondMinimum228 SourceSecondMinimum229

theorem originalDualGauge_eq230 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (q : ℝ)
    (c2 c3 A : Fin 10 → ℝ) (hA : ∀ i, 0 < A i) (z : Fin 10 → ℝ) :
    dualGauge222 L hL
      (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3)))
      (ZLattice.covolume_pos _ MeasureTheory.volume) A hA z =
      coordinateGauge10 (originalDualCoordinates230 A2 A3 L hL q c2 c3 A hA) z := by
  exact dualGauge_coordinates229 L hL _ _ A hA z

theorem original_second_of_line230 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (q : ℝ)
    (c2 c3 A : Fin 10 → ℝ) (hA : ∀ i, 0 < A i) (M : Fin 10 → ℤ)
    (hline : ∀ z ∈ scaledDual219 (originalDualGroup230 A2 A3 q c2 c3),
      dualGauge222 L hL
        (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3)))
        (ZLattice.covolume_pos _ MeasureTheory.volume) A hA (ratReal222 z) ≤ 2 →
      z ∈ Submodule.span ℚ {fun i => (M i : ℚ)}) :
    2 ≤ originalSecondRadius230 A2 A3 L hL q c2 c3 A hA := by
  have hlat : (lattice10Span (originalDualBasis230 A2 A3 q c2 c3) : Set (Fin 10 → ℝ)) =
      ratReal222 '' scaledDual219 (originalDualGroup230 A2 A3 q c2 c3) :=
    originalDualRealBasis_lattice228 A2 A3 q c2 c3
  have hline' : ∀ z ∈ scaledDual219 (originalDualGroup230 A2 A3 q c2 c3),
      coordinateGauge10 (originalDualCoordinates230 A2 A3 L hL q c2 c3 A hA)
        (ratReal222 z) ≤ 2 → z ∈ Submodule.span ℚ {fun i => (M i : ℚ)} := by
    intro z hz hg
    have he := originalDualGauge_eq230 A2 A3 L hL q c2 c3 A hA (ratReal222 z)
    exact hline z hz (Eq.mpr (congrArg (fun r : ℝ => r ≤ 2) he) hg)
  have h := second_radius_of_line229 (originalDualBasis230 A2 A3 q c2 c3)
    (originalDualCoordinates230 A2 A3 L hL q c2 c3 A hA)
    (originalDualGroup230 A2 A3 q c2 c3) M hlat hline'
  exact h

end CompoundFeasibility.SourceSecondMinimum230
