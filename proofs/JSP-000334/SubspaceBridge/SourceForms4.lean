import SubspaceBridge.AlgebraicLiouville4
import SubspaceBridge.OriginalAuxiliaryDual4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceForms4

def forms4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (tau : Fin 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  if tau = 0 then L else if tau = 1 then A2.map (algebraMap ℚ ℝ) else A3.map (algebraMap ℚ ℝ)

def finiteMatrix4 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ) :
    Matrix (Fin 4) (Fin 4) ℚ_[p] := A.map (algebraMap ℚ ℚ_[p])

theorem source_det_one4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1) :
    ∀ tau, (forms4 A2 A3 L tau).det = 1 := by
  intro tau
  fin_cases tau
  · exact hL
  · exact OriginalAuxiliaryDual4.mapped_det_one4 A2 h2
  · exact OriginalAuxiliaryDual4.mapped_det_one4 A3 h3

theorem source_unit4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1) :
    ∀ tau, IsUnit (forms4 A2 A3 L tau) := by
  intro tau
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [source_det_one4 A2 A3 L h2 h3 hL tau]
  exact isUnit_one

theorem finite_det_one4 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ)
    (hA : A.det = 1) : (finiteMatrix4 p A).det = 1 :=
  OriginalAuxiliaryDual4.mapped_det_one4 A hA

theorem source_algebraic4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∀ tau i j, IsAlgebraic ℚ (forms4 A2 A3 L tau i j) := by
  intro tau i j
  fin_cases tau
  · exact ha i j
  · exact isAlgebraic_algebraMap _
  · exact isAlgebraic_algebraMap _

theorem common_source_field4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∀ tau i j, forms4 A2 A3 L tau i j ∈ K := by
  obtain ⟨K,hK,hmem⟩ := liouville4_common_field L ha
  refine ⟨K,hK,?_⟩
  intro tau i j
  fin_cases tau
  · exact hmem i j
  · exact K.algebraMap_mem _
  · exact K.algebraMap_mem _

theorem source_rows_nonzero4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1) :
    ∀ tau i, ∃ j, forms4 A2 A3 L tau i j ≠ 0 := by
  intro tau i
  by_contra! hz
  have he := Matrix.det_eq_zero_of_row_eq_zero i hz
  rw [source_det_one4 A2 A3 L h2 h3 hL tau] at he
  exact one_ne_zero he

end CompoundFeasibility.SourceForms4
