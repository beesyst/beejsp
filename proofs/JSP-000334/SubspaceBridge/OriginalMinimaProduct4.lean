import SubspaceBridge.CompoundComparisonReverse42
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalMinimaProduct4

theorem six_product_le64 (mu nu : Fin 6 → ℝ)
    (hn : ∀ j, 0 ≤ nu j) (h : ∀ j, nu j ≤ 2 * mu j) :
    (∏ j : Fin 6, nu j) ≤ 64 * ∏ j : Fin 6, mu j := by
  calc
    _ ≤ ∏ j : Fin 6, 2 * mu j := Finset.prod_le_prod (fun j _ => hn j) (fun j _ => h j)
    _ = 64 * ∏ j : Fin 6, mu j := by
      rw [Finset.prod_mul_distrib]
      norm_num


theorem source_compound_product_le_original_cube4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ) :
    (∏ j : Fin 6, sourceMinima6 A2 A3 L hL Q hQ c0 c2 c3 j) ≤
      64 * (∏ i : Fin 4, sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 i)^3 := by
  have h := six_product_le64 (sourcePairProducts42 A2 A3 L hL Q hQ c0 c2 c3)
    (sourceMinima6 A2 A3 L hL Q hQ c0 c2 c3)
    (fun j => ((sourceMinima6_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1 j).le)
    (source_compound_minima_upper42 A2 A3 L hL Q hQ c0 c2 c3)
  rw [sourcePairProducts42_product] at h
  exact h

theorem source_uniform_original_cube_lower4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ c6 : ℝ, 0 < c6 ∧ ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ),
      (∑ i, (c0 i+c2 i+c3 i) = 0) →
      c6 ≤ 64 * (∏ i : Fin 4, sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 i)^3 := by
  obtain ⟨c6,hc6,_,hlower⟩ := source_compound_uniform_minima_lower6 A2 A3 L h2 h3 hL
  refine ⟨c6,hc6,?_⟩
  intro Q hQ c0 c2 c3 hb
  exact (hlower Q hQ c0 c2 c3 hb).trans
    (source_compound_product_le_original_cube4 A2 A3 L hL Q hQ c0 c2 c3)


theorem positive_lower_of_cube_upper (c6 C4 A : ℝ)
    (hc6 : 0 < c6) (hC4 : 0 < C4) (hA : 0 < A) (hAC : A ≤ C4)
    (hcube : c6 ≤ 64 * A^3) : c6/(64*C4^2) ≤ A := by
  have hsq : A^2 ≤ C4^2 := pow_le_pow_left₀ hA.le hAC 2
  have h3 : A^3 ≤ C4^2*A := by
    calc
      _ = A^2*A := by ring
      _ ≤ C4^2*A := mul_le_mul_of_nonneg_right hsq hA.le
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 64) (sq_pos_of_pos hC4))).mpr
  calc
    _ ≤ 64*A^3 := hcube
    _ ≤ 64*(C4^2*A) := mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ = A*(64*C4^2) := by ring


theorem source_original_uniform_minima_two_sided4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ c4 C4 : ℝ, 0 < c4 ∧ 0 < C4 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ),
        (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) →
        (∑ i, (c0 i+c2 i+c3 i) = 0) →
        c4 ≤ (∏ i : Fin 4, sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 i) ∧
          (∏ i : Fin 4, sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 i) ≤ C4 := by
  obtain ⟨c6,hc6,hlower⟩ := source_uniform_original_cube_lower4 A2 A3 L h2 h3 hL
  obtain ⟨K,C4,_,hC4,_,hupper⟩ := source_original_uniform_minima_upper4 A2 A3 L h2 h3 hL
  let c4 := c6/(64*C4^2)
  have hc4 : 0 < c4 := div_pos hc6 (mul_pos (by norm_num) (sq_pos_of_pos hC4))
  refine ⟨c4,C4,hc4,hC4,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb
  have hA : 0 < ∏ i : Fin 4, sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 i :=
    Finset.prod_pos (fun i _ => (sourceMinima4_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1 i)
  have hu := hupper Q hQ c0 c2 c3 hc2 hc3 hb
  exact ⟨positive_lower_of_cube_upper c6 C4 _ hc6 hC4 hA hu (hlower Q hQ c0 c2 c3 hb),hu⟩

end CompoundFeasibility.OriginalMinimaProduct4