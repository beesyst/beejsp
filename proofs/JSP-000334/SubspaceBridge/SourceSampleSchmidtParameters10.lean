import SubspaceBridge.SourceAuxiliarySample10
import SubspaceBridge.SourceSchmidtNumeric10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSchmidtGrowth10
open SourceSampling10

theorem original_sample_schmidt_parameters10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (c2 c3 : Fin 10 → ℝ) (V : Set ℝ) (v : V → Fin 10 → Fin 10 → ℤ)
    (c : Fin 3 → Fin 10 → ℝ) (epsilon eta D E : ℝ) (he : 0 < eta)
    (m : ℕ) (hm : 0 < m)
    (hfamily : ∀ rho : ℝ, 0 < rho → ∀ B : ℝ,
      Nonempty (OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)) :
    ∃ theta rho : ℝ, 0 < theta ∧ theta < 1/12 ∧ theta < (m : ℝ)*eta ∧
      0 < rho ∧ rho ≤ 1/2 ∧ rho ≤ JSP000334.omega65 m theta ∧
      (∀ B : ℝ, Nonempty
        (OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)) ∧
      ∀ (B : ℝ)
        (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
        (h : Fin m) (hh : h.val+1 < m),
        (S.data.r ⟨h.val+1,hh⟩ : ℝ) ≤ JSP000334.omega65 m theta*(S.data.r h : ℝ) := by
  obtain ⟨theta,rho,ht,htu,hte,hr,hrhalf,hrw⟩ := schmidt_parameters10 m hm eta he
  refine ⟨theta,rho,ht,htu,hte,hr,hrhalf,hrw,hfamily rho hr,?_⟩
  intro B S h hh
  exact (S.conditions.degree_separation h hh).trans
    (mul_le_mul_of_nonneg_right hrw (Nat.cast_nonneg _))

end CompoundFeasibility.SourceSchmidtGrowth10
