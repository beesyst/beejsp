import SubspaceBridge.CompoundSourceFamily42
open scoped Matrix
namespace M73DetLiteral
noncomputable section

def first : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
def second : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

def minorMatrix {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K) :
    Matrix (Fin 6) (Fin 6) K := fun s t =>
  (!![A (first s) (first t), A (first s) (second t);
      A (second s) (first t), A (second s) (second t)]).det

theorem coordinate_identity {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K) :
    minorMatrix A = CompoundFeasibility.compound A := by
  ext s t
  unfold minorMatrix
  rw [Matrix.det_fin_two]
  rfl

theorem determinant {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K) :
    (minorMatrix A).det = A.det ^ (3 : ℕ) := by
  rw [coordinate_identity]
  exact CompoundFeasibility.compound42_det A

theorem normalized {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K)
    (hA : A.det = 1) : (minorMatrix A).det = 1 := by
  rw [determinant, hA, one_pow]

theorem source_normalized (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) :
    (minorMatrix A₂).det = 1 ∧ (minorMatrix A₃).det = 1 ∧ (minorMatrix L).det = 1 := by
  constructor
  · rw [determinant, h₂, one_pow]
  constructor
  · rw [determinant, h₃, one_pow]
  · rw [determinant, hL, one_pow]

theorem source_admissible (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    (minorMatrix A₂).det = 1 ∧ (minorMatrix A₃).det = 1 ∧ (minorMatrix L).det = 1 ∧
      (∀ s t, IsAlgebraic ℚ (minorMatrix L s t)) := by
  obtain ⟨h₂c, h₃c, hLc⟩ := source_normalized A₂ A₃ L h₂ h₃ hL
  refine ⟨h₂c, h₃c, hLc, ?_⟩
  intro s t
  unfold minorMatrix
  rw [Matrix.det_fin_two]
  exact ((hAlg _ _).mul (hAlg _ _)).sub ((hAlg _ _).mul (hAlg _ _))

end
end M73DetLiteral
#check M73DetLiteral.determinant
#check M73DetLiteral.source_admissible
#print axioms M73DetLiteral.first
#print axioms M73DetLiteral.second
#print axioms M73DetLiteral.minorMatrix
#print axioms M73DetLiteral.coordinate_identity
#print axioms M73DetLiteral.determinant
#print axioms M73DetLiteral.normalized
#print axioms M73DetLiteral.source_normalized
#print axioms M73DetLiteral.source_admissible
