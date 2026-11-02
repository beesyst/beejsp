import SubspaceBridge.SourceCompoundMinima54_246F
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior54_246

theorem prod_erase_upper4246 (mu nu : Fin 5 → ℝ)
    (hnu : ∀ k, 0 < nu k) (hupper : ∀ k, nu k ≤ 24 * mu k) (j : Fin 5) :
    (∏ k ∈ Finset.univ.erase j, nu k) ≤ 331776 * ∏ k ∈ Finset.univ.erase j, mu k := by
  have h := Finset.prod_le_prod (fun k _ => (hnu k).le)
    (fun k (_ : k ∈ Finset.univ.erase j) => hupper k)
  have hc : (Finset.univ.erase j).card = 4 := by simp
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, hc, show (24 : ℝ) ^ 4 = 331776 by norm_num] using h

theorem product_reverse4246 (mu nu : Fin 5 → ℝ) (c C : ℝ)
    (hmu : ∀ k, 0 < mu k) (hnu : ∀ k, 0 < nu k)
    (hupper : ∀ k, nu k ≤ 24 * mu k)
    (hlower : c ≤ ∏ k, nu k) (hprod : (∏ k, mu k) ≤ C ^ 4)
    (hC : 0 < C) (j : Fin 5) :
    (c / (331776 * C ^ 4)) * mu j ≤ nu j := by
  have hdecomp (f : Fin 5 → ℝ) :
      f j * (∏ k ∈ Finset.univ.erase j, f k) = ∏ k, f k :=
    Finset.mul_prod_erase _ _ (Finset.mem_univ j)
  have hstep : c * mu j ≤ 331776 * nu j * (∏ k, mu k) := by
    calc
      c * mu j ≤ (∏ k, nu k) * mu j := mul_le_mul_of_nonneg_right hlower (hmu j).le
      _ = (nu j * (∏ k ∈ Finset.univ.erase j, nu k)) * mu j := by rw [hdecomp]
      _ ≤ (nu j * (331776 * ∏ k ∈ Finset.univ.erase j, mu k)) * mu j :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (prod_erase_upper4246 mu nu hnu hupper j) (hnu j).le) (hmu j).le
      _ = 331776 * nu j * (∏ k, mu k) := by rw [← hdecomp mu]; ring
  have hfinal : c * mu j ≤ nu j * (331776 * C ^ 4) := by
    calc
      _ ≤ 331776 * nu j * (∏ k, mu k) := hstep
      _ ≤ 331776 * nu j * C ^ 4 := mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) (hnu j).le)
      _ = _ := by ring
  have hd : 0 < 331776 * C ^ 4 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  exact hfinal


theorem source_uniform_products4246 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ C5 ccompound : ℝ, 0 < C5 ∧ 0 < ccompound ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ),
        (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 →
        ccompound ≤ (∏ j, compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3 j) ∧
        (∏ i, sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ≤ C5 ∧
        (∏ j, fourProducts246 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j) ≤ C5^4 := by
  obtain ⟨_,C5,_,hC,hfive⟩ := source_original_uniform_minima_two_sided5 A2 A3 L h2 h3 hL
  obtain ⟨ccompound,_,hc,_,hten⟩ := source_original_uniform_minima_two_sided5 (compound4246 A2)
    (compound4246 A3) (compound4246 L) (compound_unit4246 A2 h2) (compound_unit4246 A3 h3) (compound_unit4246 L hL)
  refine ⟨C5,ccompound,hC,hc,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb
  have hf := (hfive Q hQ c0 c2 c3 hc2 hc3 hb).2
  have hn (c : Fin 5 → ℝ) (h : ∀ i, c i ≤ 0) : ∀ s, normalizedWeights4246 c s ≤ 0 := by
    intro s
    exact div_nonpos_of_nonpos_of_nonneg (Finset.sum_nonpos (fun _ _ => h _)) (by norm_num)
  refine ⟨(hten (Q^4) (powered_gt_one4246 Q hQ) (normalizedWeights4246 c0)
    (normalizedWeights4246 c2) (normalizedWeights4246 c3) (hn c2 hc2) (hn c3 hc3)
    (normalized_balance4246 c0 c2 c3 hb)).1,hf,?_⟩
  rw [fourProducts_product246]
  exact pow_le_pow_left₀
    (Finset.prod_pos (fun i _ => (sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1 i)).le hf 4

theorem source_uniform_comparison4246 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ C5 ccompound κ : ℝ, 0 < C5 ∧ 0 < ccompound ∧ 0 < κ ∧ κ = ccompound/(331776*C5^4) ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ),
        (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 →
        ∀ j, κ*fourProducts246 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j ≤
          compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3 j ∧
          compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3 j ≤
            24*fourProducts246 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j := by
  obtain ⟨C5,ccompound,hC,hc,hprod⟩ := source_uniform_products4246 A2 A3 L h2 h3 hL
  refine ⟨C5,ccompound,ccompound/(331776*C5^4),hC,hc,by positivity,rfl,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb j
  obtain ⟨hn,_,hm⟩ := hprod Q hQ c0 c2 c3 hc2 hc3 hb
  have hu := compoundMinima_upper4246 A2 A3 L hL Q hQ c0 c2 c3
  exact ⟨product_reverse4246 _ _ ccompound C5
    (fourProducts_pos246 _ (sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1)
    (compoundMinima_pos_mono4246 A2 A3 L hL Q hQ c0 c2 c3).1 hu hn hm hC j,hu j⟩

end CompoundFeasibility.Exterior54_246
