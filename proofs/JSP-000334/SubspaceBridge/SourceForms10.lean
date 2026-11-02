import SubspaceBridge.AlgebraicLiouville10
import SubspaceBridge.OriginalDual10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceForms10

def forms10 {n : ℕ} (A2 A3 : Matrix (Fin n) (Fin n) ℚ) (L : Matrix (Fin n) (Fin n) ℝ)
    (tau : Fin 3) : Matrix (Fin n) (Fin n) ℝ :=
  if tau = 0 then L else if tau = 1 then A2.map (algebraMap ℚ ℝ) else A3.map (algebraMap ℚ ℝ)

def finiteMatrix10 {n : ℕ} (p : ℕ) [Fact p.Prime] (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ_[p] := A.map (algebraMap ℚ ℚ_[p])

theorem source_det_one10 {n : ℕ} (A2 A3 : Matrix (Fin n) (Fin n) ℚ)
    (L : Matrix (Fin n) (Fin n) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1) :
    ∀ tau, (forms10 A2 A3 L tau).det = 1 := by
  intro tau
  fin_cases tau
  · simp only [forms10, ↓reduceIte]
    exact hL
  · simp only [forms10, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
    exact OriginalDual10.mapped_det_one10 (K := ℝ) A2 h2
  · simp only [forms10, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
    exact OriginalDual10.mapped_det_one10 (K := ℝ) A3 h3

theorem source_unit10 {n : ℕ} (A2 A3 : Matrix (Fin n) (Fin n) ℚ)
    (L : Matrix (Fin n) (Fin n) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1) :
    ∀ tau, IsUnit (forms10 A2 A3 L tau) := by
  intro tau
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [source_det_one10 A2 A3 L h2 h3 hL tau]
  exact isUnit_one

theorem finite_det_one10 {n : ℕ} (p : ℕ) [Fact p.Prime] (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : A.det = 1) : (finiteMatrix10 p A).det = 1 := by
  unfold finiteMatrix10
  exact OriginalDual10.mapped_det_one10 (K := ℚ_[p]) A hA

theorem source_algebraic10 {n : ℕ} (A2 A3 : Matrix (Fin n) (Fin n) ℚ)
    (L : Matrix (Fin n) (Fin n) ℝ) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∀ tau i j, IsAlgebraic ℚ (forms10 A2 A3 L tau i j) := by
  intro tau i j
  fin_cases tau
  · exact ha i j
  · exact isAlgebraic_algebraMap _
  · exact isAlgebraic_algebraMap _

theorem common_source_field10 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∀ tau i j, forms10 A2 A3 L tau i j ∈ K := by
  obtain ⟨K,hK,hmem⟩ := liouville10_common_field L ha
  refine ⟨K,hK,?_⟩
  intro tau i j
  fin_cases tau
  · exact hmem i j
  · exact K.algebraMap_mem _
  · exact K.algebraMap_mem _

theorem source_rows_nonzero10 {n : ℕ} (A2 A3 : Matrix (Fin n) (Fin n) ℚ)
    (L : Matrix (Fin n) (Fin n) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1) :
    ∀ tau i, ∃ j, forms10 A2 A3 L tau i j ≠ 0 := by
  intro tau i
  by_contra! hz
  have he := Matrix.det_eq_zero_of_row_eq_zero i hz
  rw [source_det_one10 A2 A3 L h2 h3 hL tau] at he
  exact one_ne_zero he

end CompoundFeasibility.SourceForms10
