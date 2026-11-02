import SubspaceBridge.SourceFiniteDualLower10
import SubspaceBridge.SourceSelectedFactorBounds10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSelectedUpper10
open OriginalDual10 SourceSelectedSet10 SchmidtNormal10 SourceHeightEnvelope10

theorem finite_dual_norm_canonical10 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : A.det = 1)
    (M : Fin 10 → ℤ) (i : Fin 10) :
    ‖((A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose *ᵥ
      (fun k => (M k : ℚ_[p]))) i‖ = ‖finiteValue10 p A.adjugate.transpose M i‖ := by
  rw [finite_dual_from_adjugate10 p A hA M i]

theorem original_p2_dual_norm10 (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : A.det = 1)
    (M : Fin 10 → ℤ) (i : Fin 10) :
    ‖((A.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ
      (fun k => (M k : ℚ_[2]))) i‖ = ‖finiteValue10 2 A.adjugate.transpose M i‖ := by
  apply finite_dual_norm_canonical10
  assumption

theorem original_p3_dual_norm10 (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : A.det = 1)
    (M : Fin 10 → ℤ) (i : Fin 10) :
    ‖((A.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ
      (fun k => (M k : ℚ_[3]))) i‖ = ‖finiteValue10 3 A.adjugate.transpose M i‖ := by
  apply finite_dual_norm_canonical10
  assumption

theorem mixedProduct10_canonical
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (M : Fin 10 → ℤ) (s : MixedIndex10) :
    mixedProduct10 A2 A3 L M s =
      |(L⁻¹.transpose *ᵥ integerReal M) (s 0)| *
      ‖finiteValue10 2 A2.adjugate.transpose M (s 1)‖ *
      ‖finiteValue10 3 A3.adjugate.transpose M (s 2)‖ := by
  unfold mixedProduct10
  rw [original_p2_dual_norm10 A2 h2 M (s 1), original_p3_dual_norm10 A3 h3 M (s 2)]

theorem mixedProduct10_le_canonical_bounds
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (M : Fin 10 → ℤ) (s : MixedIndex10)
    (b0 b2 b3 : ℝ)
    (h0 : |(L⁻¹.transpose *ᵥ integerReal M) (s 0)| ≤ b0)
    (hp2 : ‖finiteValue10 2 A2.adjugate.transpose M (s 1)‖ ≤ b2)
    (hp3 : ‖finiteValue10 3 A3.adjugate.transpose M (s 2)‖ ≤ b3) :
    mixedProduct10 A2 A3 L M s ≤ b0*b2*b3 := by
  rw [mixedProduct10_canonical A2 A3 L h2 h3 M s]
  apply three_factor_bound10
  · exact abs_nonneg _
  · exact norm_nonneg _
  · exact norm_nonneg _
  · exact h0
  · exact hp2
  · exact hp3

end CompoundFeasibility.SourceSelectedUpper10
