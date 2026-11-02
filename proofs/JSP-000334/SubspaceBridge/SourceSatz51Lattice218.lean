import SubspaceBridge.SourceSatz51Rounding218
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSatz51Entry218
open SourceOriginalVariable10

theorem rounding_threshold218 (p : ℕ) (q c : ℝ) :
    Nat.ceil (JSP000334.qThreshold p q c) = (-roundedExponent218 p q c).toNat := by
  have he : JSP000334.qThreshold p q c = -(c*Real.log q/Real.log (p : ℝ)) := by
    unfold JSP000334.qThreshold
    ring
  rw [he,← Int.ceil_toNat,Int.ceil_neg]
  rfl

theorem rounding_lattice218 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (q : ℝ) (hq : 1 < q) (c2 c3 : Fin 10 → ℝ) :
    originalSourceGroup10 A2 A3 q c2 c3 =
      sourceLattice10 A2 A3 (fun i => (-roundedExponent218 2 q (c2 i)).toNat)
        (fun i => (-roundedExponent218 3 q (c3 i)).toNat) ∧
    originalSourceGroup10 A2 A3 (q^2)
      (fun i => normalizedFinite10 2 (q^2) (roundedExponent218 2 q (c2 i)))
      (fun i => normalizedFinite10 3 (q^2) (roundedExponent218 3 q (c3 i))) =
      originalSourceGroup10 A2 A3 q c2 c3 := by
  have hq2 : 1 < q^2 := by nlinarith [sq_nonneg (q-1)]
  constructor
  · unfold originalSourceGroup10
    simp_rw [rounding_threshold218]
  · unfold originalSourceGroup10
    simp_rw [normalized_threshold_exact10 2 (by decide) (q^2) hq2,
      normalized_threshold_exact10 3 (by decide) (q^2) hq2,rounding_threshold218]

end CompoundFeasibility.SourceSatz51Entry218
