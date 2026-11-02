import SubspaceBridge.SchmidtScalar10
open scoped BigOperators Classical
noncomputable section
namespace CompoundFeasibility.SourceSchmidtContradiction10
open SchmidtScalar10 SchmidtRationalNormalization6 SchmidtTaylorCorrespondence6

theorem binary_root_point10 {m : ℕ} (N : Fin m → Fin 10 → ℤ) (h : Fin m) :
    rootPoint6 (binaryLift6 N) h =
      (((rootNumerator6 (N h 0) (N h 1) : ℚ)/
        (rootDenominator6 (N h 0) (N h 1) : ℚ) : ℚ) : ℝ) := by
  simp only [rootPoint6,binaryLift6_zero,binaryLift6_one,Rat.cast_div,Rat.cast_intCast]

end CompoundFeasibility.SourceSchmidtContradiction10
