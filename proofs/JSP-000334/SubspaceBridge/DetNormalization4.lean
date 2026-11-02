import SubspaceBridge.SourceCriterion4
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.DetNormalization4
noncomputable section

def detRowMultiplier4 {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) : K :=
  if i = 0 then A.det⁻¹ else 1

def normalizedDet4 {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 4) (Fin 4) K :=
  A.updateRow 0 (A.det⁻¹ • A 0)

theorem detRowMultiplier4_ne_zero {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.det ≠ 0) (i : Fin 4) :
    detRowMultiplier4 A i ≠ 0 := by
  simp only [detRowMultiplier4]
  split_ifs <;> simp [hA]

theorem normalizedDet4_det {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.det ≠ 0) :
    (normalizedDet4 A).det = 1 := by
  rw [normalizedDet4,Matrix.det_updateRow_smul,Matrix.updateRow_eq_self]
  exact inv_mul_cancel₀ hA

theorem normalizedDet4_apply {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    normalizedDet4 A i j = detRowMultiplier4 A i * A i j := by
  by_cases hi : i = 0
  · subst i
    simp [normalizedDet4,detRowMultiplier4]
  · simp [normalizedDet4,detRowMultiplier4,hi,Ne.symm hi]

theorem normalizedDet4_mulVec {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (x : Fin 4 → K) (i : Fin 4) :
    (normalizedDet4 A *ᵥ x) i = detRowMultiplier4 A i * (A *ᵥ x) i := by
  simp only [Matrix.mulVec, dotProduct,normalizedDet4_apply,mul_assoc,Finset.mul_sum]

theorem algebraic_det4 (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) : IsAlgebraic ℚ L.det := by
  rw [Matrix.det_apply]
  apply isAlgebraic_iff_isIntegral.mpr
  apply IsIntegral.sum
  intro s hs
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℚ]
  exact (IsIntegral.prod _ (fun i _ => (hAlg (s i) i).isIntegral)).smul _

theorem algebraic_inv_det4 (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) : IsAlgebraic ℚ L.det⁻¹ :=
  (algebraic_det4 L hAlg).inv

theorem normalizedDet4_algebraic (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∀ i j, IsAlgebraic ℚ (normalizedDet4 L i j) := by
  intro i j
  rw [normalizedDet4_apply]
  have hs : IsAlgebraic ℚ (detRowMultiplier4 L i) := by
    unfold detRowMultiplier4
    split_ifs
    · exact algebraic_inv_det4 L hAlg
    · exact isAlgebraic_one
  exact hs.mul (hAlg i j)

end
end CompoundFeasibility.DetNormalization4
