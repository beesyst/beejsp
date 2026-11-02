import SubspaceBridge.SourceCompoundMinima53_242
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior53_242

theorem prod_erase_upper3242 (mu nu : Fin 10 → ℝ)
    (hnu : ∀ k, 0 < nu k) (hupper : ∀ k, nu k ≤ 6 * mu k) (j : Fin 10) :
    (∏ k ∈ Finset.univ.erase j, nu k) ≤ 10077696 * ∏ k ∈ Finset.univ.erase j, mu k := by
  have h := Finset.prod_le_prod (fun k _ => (hnu k).le)
    (fun k (_ : k ∈ Finset.univ.erase j) => hupper k)
  have hc : (Finset.univ.erase j).card = 9 := by simp
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, hc, show (6 : ℝ) ^ 9 = 10077696 by norm_num] using h

theorem product_reverse3242 (mu nu : Fin 10 → ℝ) (c C : ℝ)
    (hmu : ∀ k, 0 < mu k) (hnu : ∀ k, 0 < nu k)
    (hupper : ∀ k, nu k ≤ 6 * mu k)
    (hlower : c ≤ ∏ k, nu k) (hprod : (∏ k, mu k) ≤ C ^ 6)
    (hC : 0 < C) (j : Fin 10) :
    (c / (10077696 * C ^ 6)) * mu j ≤ nu j := by
  have hdecomp (f : Fin 10 → ℝ) :
      f j * (∏ k ∈ Finset.univ.erase j, f k) = ∏ k, f k :=
    Finset.mul_prod_erase _ _ (Finset.mem_univ j)
  have hstep : c * mu j ≤ 10077696 * nu j * (∏ k, mu k) := by
    calc
      c * mu j ≤ (∏ k, nu k) * mu j := mul_le_mul_of_nonneg_right hlower (hmu j).le
      _ = (nu j * (∏ k ∈ Finset.univ.erase j, nu k)) * mu j := by rw [hdecomp]
      _ ≤ (nu j * (10077696 * ∏ k ∈ Finset.univ.erase j, mu k)) * mu j :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (prod_erase_upper3242 mu nu hnu hupper j) (hnu j).le) (hmu j).le
      _ = 10077696 * nu j * (∏ k, mu k) := by rw [← hdecomp mu]; ring
  have hfinal : c * mu j ≤ nu j * (10077696 * C ^ 6) := by
    calc
      _ ≤ 10077696 * nu j * (∏ k, mu k) := hstep
      _ ≤ 10077696 * nu j * C ^ 6 := mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) (hnu j).le)
      _ = _ := by ring
  have hd : 0 < 10077696 * C ^ 6 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  exact hfinal


theorem source_uniform_products3242 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ C5 c10 : ℝ, 0 < C5 ∧ 0 < c10 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ),
        (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 →
        c10 ≤ (∏ j, compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 j) ∧
        (∏ i, sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ≤ C5 ∧
        (∏ j, tripleProducts242 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j) ≤ C5^6 := by
  obtain ⟨_,C5,_,hC,hfive⟩ := source_original_uniform_minima_two_sided5 A2 A3 L h2 h3 hL
  obtain ⟨c10,_,hc,_,hten⟩ := source_original_uniform_minima_two_sided10 (compound3242 A2)
    (compound3242 A3) (compound3242 L) (compound_rat_unit3242 A2 h2) (compound_rat_unit3242 A3 h3) (compound_real_unit3242 L hL)
  refine ⟨C5,c10,hC,hc,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb
  have hf := (hfive Q hQ c0 c2 c3 hc2 hc3 hb).2
  have hn (c : Fin 5 → ℝ) (h : ∀ i, c i ≤ 0) : ∀ s, normalizedWeights3242 c s ≤ 0 := by
    intro s
    exact div_nonpos_of_nonpos_of_nonneg (add_nonpos (add_nonpos (h _) (h _)) (h _)) (by norm_num)
  refine ⟨(hten (Q^3) (powered_gt_one3242 Q hQ) (normalizedWeights3242 c0)
    (normalizedWeights3242 c2) (normalizedWeights3242 c3) (hn c2 hc2) (hn c3 hc3)
    (normalized_balance3242 c0 c2 c3 hb)).1,hf,?_⟩
  rw [tripleProducts_product242]
  exact pow_le_pow_left₀
    (Finset.prod_pos (fun i _ => (sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1 i)).le hf 6

theorem source_uniform_comparison3242 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ C5 c10 κ : ℝ, 0 < C5 ∧ 0 < c10 ∧ 0 < κ ∧ κ = c10/(10077696*C5^6) ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ),
        (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 →
        ∀ j, κ*tripleProducts242 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j ≤
          compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 j ∧
          compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 j ≤
            6*tripleProducts242 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j := by
  obtain ⟨C5,c10,hC,hc,hprod⟩ := source_uniform_products3242 A2 A3 L h2 h3 hL
  refine ⟨C5,c10,c10/(10077696*C5^6),hC,hc,by positivity,rfl,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb j
  obtain ⟨hn,_,hm⟩ := hprod Q hQ c0 c2 c3 hc2 hc3 hb
  have hu := compoundMinima_upper3242 A2 A3 L hL Q hQ c0 c2 c3
  exact ⟨product_reverse3242 _ _ c10 C5
    (tripleProducts_pos242 _ (sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1)
    (compoundMinima_pos_mono3242 A2 A3 L hL Q hQ c0 c2 c3).1 hu hn hm hC j,hu j⟩

end CompoundFeasibility.Exterior53_242
