import SubspaceBridge.SourceInverseTransport10
import SubspaceBridge.SourceRationalFiniteLower10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceHeightEnvelope10
open SchmidtNormal10

theorem finite_adjugate_dimension10 {N : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin N) (Fin N) ℚ) (hA : A.det = 1) :
    (A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose =
      A.adjugate.transpose.map (algebraMap ℚ ℚ_[p]) := by
  exact adjugate_dual_map_generic10 (algebraMap ℚ ℚ_[p]) A hA

theorem finite_adjugate_dual10 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : A.det = 1) :
    (A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose =
      A.adjugate.transpose.map (algebraMap ℚ ℚ_[p]) := by
  exact finite_adjugate_dimension10 p A hA

theorem original_p2_dual_matrix10 (A2 : Matrix (Fin 10) (Fin 10) ℚ) (h2 : A2.det = 1) :
    (A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose =
      A2.adjugate.transpose.map (algebraMap ℚ ℚ_[2]) := by
  exact finite_adjugate_dual10 2 A2 h2

theorem original_p3_dual_matrix10 (A3 : Matrix (Fin 10) (Fin 10) ℚ) (h3 : A3.det = 1) :
    (A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose =
      A3.adjugate.transpose.map (algebraMap ℚ ℚ_[3]) := by
  exact finite_adjugate_dual10 3 A3 h3

theorem finite_dual_from_adjugate10 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : A.det = 1)
    (M : Fin 10 → ℤ) (s : Fin 10) :
    ((A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose *ᵥ (fun k => (M k : ℚ_[p]))) s =
      finiteValue10 p A.adjugate.transpose M s := by
  rw [finite_adjugate_dual10 p A hA]
  rfl

theorem actual_finite_dual_lower10 (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : A.det = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Fin 10 → ℤ) i,
      ((A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose *ᵥ (fun k => (M k : ℚ_[p]))) i ≠ 0 →
      C ≤ ‖((A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose *ᵥ (fun k => (M k : ℚ_[p]))) i‖ *
        max 1 (normalHeight10 M : ℝ) := by
  obtain ⟨C,hC,h⟩ := finite_form_lower10 p hp A.adjugate.transpose
  refine ⟨C,hC,?_⟩
  intro M i hn
  rw [finite_dual_from_adjugate10 p A hA M i] at hn ⊢
  exact (h M i hn).1

theorem actual_p2_dual_lower10 (A2 : Matrix (Fin 10) (Fin 10) ℚ)
    (h2 : A2.det = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Fin 10 → ℤ) i,
      ((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (M k : ℚ_[2]))) i ≠ 0 →
      C ≤ ‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (M k : ℚ_[2]))) i‖ *
        max 1 (normalHeight10 M : ℝ) := by
  exact actual_finite_dual_lower10 2 (Or.inl rfl) A2 h2

theorem actual_p3_dual_lower10 (A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (h3 : A3.det = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Fin 10 → ℤ) i,
      ((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k => (M k : ℚ_[3]))) i ≠ 0 →
      C ≤ ‖((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k => (M k : ℚ_[3]))) i‖ *
        max 1 (normalHeight10 M : ℝ) := by
  exact actual_finite_dual_lower10 3 (Or.inr rfl) A3 h3

end CompoundFeasibility.SourceHeightEnvelope10
