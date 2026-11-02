import SubspaceBridge.CompoundComparisonUpper42
open scoped BigOperators Matrix
namespace CompoundFeasibility

theorem prod_erase_upper42 (mu nu : Fin 6 → ℝ)
    (hnu : ∀ k, 0 < nu k) (hupper : ∀ k, nu k ≤ 2 * mu k) (j : Fin 6) :
    (∏ k ∈ Finset.univ.erase j, nu k) ≤ 32 * ∏ k ∈ Finset.univ.erase j, mu k := by
  have h := Finset.prod_le_prod (fun k _ => (hnu k).le)
    (fun k (_ : k ∈ Finset.univ.erase j) => hupper k)
  have hc : (Finset.univ.erase j).card = 5 := by simp
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, hc, show (2 : ℝ) ^ 5 = 32 by norm_num] using h

theorem product_reverse42 (mu nu : Fin 6 → ℝ) (c C : ℝ)
    (hmu : ∀ k, 0 < mu k) (hnu : ∀ k, 0 < nu k)
    (hupper : ∀ k, nu k ≤ 2 * mu k)
    (hlower : c ≤ ∏ k, nu k) (hprod : (∏ k, mu k) ≤ C ^ 3)
    (hC : 0 < C) (j : Fin 6) :
    (c / (32 * C ^ 3)) * mu j ≤ nu j := by
  have hdecomp (f : Fin 6 → ℝ) :
      f j * (∏ k ∈ Finset.univ.erase j, f k) = ∏ k, f k :=
    Finset.mul_prod_erase _ _ (Finset.mem_univ j)
  have hstep : c * mu j ≤ 32 * nu j * (∏ k, mu k) := by
    calc
      c * mu j ≤ (∏ k, nu k) * mu j := mul_le_mul_of_nonneg_right hlower (hmu j).le
      _ = (nu j * (∏ k ∈ Finset.univ.erase j, nu k)) * mu j := by rw [hdecomp]
      _ ≤ (nu j * (32 * ∏ k ∈ Finset.univ.erase j, mu k)) * mu j :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (prod_erase_upper42 mu nu hnu hupper j) (hnu j).le) (hmu j).le
      _ = 32 * nu j * (∏ k, mu k) := by rw [← hdecomp mu]; ring
  have hfinal : c * mu j ≤ nu j * (32 * C ^ 3) := by
    calc
      _ ≤ 32 * nu j * (∏ k, mu k) := hstep
      _ ≤ 32 * nu j * C ^ 3 := mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) (hnu j).le)
      _ = _ := by ring
  have hd : 0 < 32 * C ^ 3 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  exact hfinal


theorem source_compound_minima_reverse42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (C₄ c₆ : ℝ) (hC : 0 < C₄)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (horiginal : (∏ i : Fin 4, sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ≤ C₄)
    (hcompound : c₆ ≤ ∏ j : Fin 6, sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) :
    ∀ j : Fin 6, (c₆ / (32 * C₄ ^ 3)) *
      sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤
        sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  have hprod : (∏ j : Fin 6, sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ≤ C₄ ^ 3 := by
    rw [sourcePairProducts42_product]
    exact pow_le_pow_left₀
      (Finset.prod_pos (fun i _ => (sourceMinima4_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1 i)).le
      horiginal 3
  exact product_reverse42 _ _ c₆ C₄
    (sourcePairProducts42_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1
    (sourceMinima6_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1
    (source_compound_minima_upper42 A₂ A₃ L hL Q hQ c₀ c₂ c₃)
    hcompound hprod hC

theorem source_compound_uniform_comparison42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ C₄ c₆ κ : ℝ, 0 < C₄ ∧ 0 < c₆ ∧ 0 < κ ∧ κ = c₆ / (32 * C₄ ^ 3) ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) →
        (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        ∀ j : Fin 6,
          κ * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤
            sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ∧
          sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤
            2 * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  obtain ⟨_,C₄,_,hC,_,hfour⟩ := source_original_uniform_minima_upper4 A₂ A₃ L h₂ h₃ hL
  obtain ⟨c₆,hc,_,hsix⟩ := source_compound_uniform_minima_lower6 A₂ A₃ L h₂ h₃ hL
  refine ⟨C₄,c₆,c₆ / (32 * C₄ ^ 3),hC,hc,by positivity,rfl,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb j
  exact ⟨source_compound_minima_reverse42 A₂ A₃ L hL C₄ c₆ hC Q hQ c₀ c₂ c₃
    (hfour Q hQ c₀ c₂ c₃ hc₂ hc₃ hb) (hsix Q hQ c₀ c₂ c₃ hb) j,
    source_compound_minima_upper42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j⟩

end CompoundFeasibility
