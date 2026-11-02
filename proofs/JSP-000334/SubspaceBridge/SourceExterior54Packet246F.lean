import SubspaceBridge.SourceExterior54Group246L
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior54_246

theorem compound_det4246 {R : Type*} [CommRing R]
    (A : Matrix (Fin 5) (Fin 5) R) : (compound4246 A).det = A.det^4 := by
  simp [compound4246, Matrix.det_transpose, Matrix.det_adjugate]

theorem compound_det_one4246 {R : Type*} [CommRing R]
    (A : Matrix (Fin 5) (Fin 5) R) (hA : A.det = 1) : (compound4246 A).det = 1 := by
  rw [compound_det4246, hA, one_pow]

theorem compound_unit4246 {R : Type*} [CommRing R]
    (A : Matrix (Fin 5) (Fin 5) R) (hA : IsUnit A) : IsUnit (compound4246 A) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [compound_det4246]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hA).pow 4

theorem compound_algebraic4246 (L : Matrix (Fin 5) (Fin 5) ℝ)
    (hL : ∀ i j, IsAlgebraic ℚ (L i j)) : ∀ i j, IsAlgebraic ℚ (compound4246 L i j) := by
  intro i j
  rw [compound_minor4246]
  apply IsAlgebraic.mul
  · exact (isAlgebraic_one.neg (R := ℚ)).pow _
  · exact (IsIntegral.det (fun k l => (hL (i.succAbove k) (j.succAbove l)).isIntegral)).isAlgebraic

theorem fourWeights_sum246 (c : Fin 5 → ℝ) :
    (∑ i, fourWeights246 c i) = 4 * ∑ i, c i := by
  simp [fourWeights246, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem normalized_real_bound4246 (c : Fin 5 → ℝ) (hc : ∀ i, |c i| ≤ 1) :
    ∀ i, |normalizedWeights4246 c i| ≤ 1 := by
  intro i
  have hs : |fourWeights246 c i| ≤ 4 := by
    calc
      _ ≤ ∑ k : Fin 4, |c (i.succAbove k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 4, (1 : ℝ) := Finset.sum_le_sum (fun k _ => hc _)
      _ = 4 := by norm_num
  unfold normalizedWeights4246
  rw [abs_div]
  norm_num only [show |(4 : ℝ)| = 4 by norm_num]
  linarith

theorem normalized_finite_bounds4246 (c : Fin 5 → ℝ)
    (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 0) :
    ∀ i, -1 ≤ normalizedWeights4246 c i ∧ normalizedWeights4246 c i ≤ 0 := by
  intro i
  have hlo : (∑ _k : Fin 4, (-1 : ℝ)) ≤ fourWeights246 c i :=
    Finset.sum_le_sum (fun k _ => (hc _).1)
  have hhi : fourWeights246 c i ≤ 0 := Finset.sum_nonpos (fun k _ => (hc _).2)
  norm_num at hlo
  unfold normalizedWeights4246
  constructor <;> linarith

theorem normalized_balance4246 (c0 c2 c3 : Fin 5 → ℝ)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0) :
    (∑ i, (normalizedWeights4246 c0 i+normalizedWeights4246 c2 i+
      normalizedWeights4246 c3 i)) = 0 := by
  simp only [normalizedWeights4246, Finset.sum_add_distrib, ← Finset.sum_div,
    fourWeights_sum246] at *
  linarith

end CompoundFeasibility.Exterior54_246
