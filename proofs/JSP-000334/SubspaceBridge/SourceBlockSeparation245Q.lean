import SubspaceBridge.SourceBlockLattice245Q
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.BlockReduction245Q

theorem integer_norm_lower245Q (x : Fin 5 → ℤ) (hx : x ≠ 0) : 1 ≤ ‖integerReal x‖ := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hx
  have hi' : x i ≠ 0 := by simpa only [Pi.zero_apply] using hi
  have ha : (1 : ℝ) ≤ |(x i : ℝ)| := by exact_mod_cast Int.one_le_abs hi'
  exact ha.trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (integerReal x) i)

theorem uniform_integer_lower245Q (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) :
    ∃ D : ℝ, 0 < D ∧ ∀ (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 5 → ℝ),
      (∀ i, |c0 i| ≤ 1) → ∀ x : Fin 5 → ℤ, x ≠ 0 →
      1/(D*Q) ≤ coordinateGauge5 (originalCoordinates5 L hL Q hQ c0) (integerReal x) := by
  let E := (originalFormEquiv5 L hL).toContinuousLinearEquiv
  let D := max 1 ‖E.symm.toContinuousLinearMap‖
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨D,hD,?_⟩
  intro Q hQ c0 hc x hx
  have hinv : ‖integerReal x‖ ≤ D*‖originalFormEquiv5 L hL (integerReal x)‖ := by
    have hi := E.symm.toContinuousLinearMap.le_opNorm (E (integerReal x))
    simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at hi
    exact hi.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hg : ‖originalFormEquiv5 L hL (integerReal x)‖ ≤
      coordinateGauge5 (originalCoordinates5 L hL Q hQ c0) (integerReal x)*Q := by
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    have hh := (originalCoordinates5_bounds L hL Q hQ c0 (integerReal x) _).mp le_rfl i
    have he : Q^(c0 i) ≤ Q := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hQ.le (abs_le.mp (hc i)).2
    exact hh.trans (mul_le_mul_of_nonneg_left he (norm_nonneg _))
  apply (div_le_iff₀ (mul_pos hD (zero_lt_one.trans hQ))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hg hD.le,(integer_norm_lower245Q x hx).trans hinv]

theorem source_separation245Q (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) :
    ∃ D T : ℝ, 0 < D ∧ 1 < T ∧
      ∀ (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (hQ : 1 < Q)
        (c0 c2 c3 : Fin 5 → ℝ), (∀ i, |c0 i| ≤ 1) →
        1/(D*Q) ≤ sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3 ∧
        (T < Q → (Q^2)⁻¹ ≤ Q^2*sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3) := by
  obtain ⟨D,hD,hlower⟩ := uniform_integer_lower245Q L hL
  refine ⟨D,max 2 D,hD,lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _),?_⟩
  intro A2 A3 Q hQ c0 c2 c3 hc
  obtain ⟨u,hu,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima5_attaining A2 A3 L hL Q hQ c0 c2 c3
  have hx : (u 3 : Fin 5 → ℤ) ≠ 0 := by
    intro hz
    apply hu.ne_zero 3
    rw [hz,map_zero]
  have hlo := hlower Q hQ c0 hc (u 3) hx
  rw [hatt] at hlo
  refine ⟨hlo,?_⟩
  intro hT
  have hq := zero_lt_one.trans hQ
  have hDQ : D ≤ Q^3 := (le_max_right 2 D).trans hT.le |>.trans
    (le_self_pow₀ hQ.le (by decide))
  have hlarge : D*Q ≤ Q^4 := by
    have h := mul_le_mul_of_nonneg_right hDQ hq.le
    nlinarith
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
  have hone := (div_le_iff₀ (mul_pos hD hq)).mp hlo
  have hmul := mul_le_mul_of_nonneg_right hlarge (hpos 3).le
  nlinarith

end CompoundFeasibility.BlockReduction245Q
