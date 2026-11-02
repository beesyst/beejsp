import SubspaceBridge.SourceCompoundMinima52_239
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.ExteriorGap52_239
open Exterior52_237 Exterior52_238

theorem prod_erase_upper239 (mu nu : Fin 10 → ℝ)
    (hnu : ∀ k, 0 < nu k) (hupper : ∀ k, nu k ≤ 2 * mu k) (j : Fin 10) :
    (∏ k ∈ Finset.univ.erase j, nu k) ≤ 512 * ∏ k ∈ Finset.univ.erase j, mu k := by
  have h := Finset.prod_le_prod (fun k _ => (hnu k).le)
    (fun k (_ : k ∈ Finset.univ.erase j) => hupper k)
  have hc : (Finset.univ.erase j).card = 9 := by simp
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, hc, show (2 : ℝ) ^ 9 = 512 by norm_num] using h

theorem product_reverse239 (mu nu : Fin 10 → ℝ) (c C : ℝ)
    (hmu : ∀ k, 0 < mu k) (hnu : ∀ k, 0 < nu k)
    (hupper : ∀ k, nu k ≤ 2 * mu k)
    (hlower : c ≤ ∏ k, nu k) (hprod : (∏ k, mu k) ≤ C ^ 4)
    (hC : 0 < C) (j : Fin 10) :
    (c / (512 * C ^ 4)) * mu j ≤ nu j := by
  have hdecomp (f : Fin 10 → ℝ) :
      f j * (∏ k ∈ Finset.univ.erase j, f k) = ∏ k, f k :=
    Finset.mul_prod_erase _ _ (Finset.mem_univ j)
  have hstep : c * mu j ≤ 512 * nu j * (∏ k, mu k) := by
    calc
      c * mu j ≤ (∏ k, nu k) * mu j := mul_le_mul_of_nonneg_right hlower (hmu j).le
      _ = (nu j * (∏ k ∈ Finset.univ.erase j, nu k)) * mu j := by rw [hdecomp]
      _ ≤ (nu j * (512 * ∏ k ∈ Finset.univ.erase j, mu k)) * mu j :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (prod_erase_upper239 mu nu hnu hupper j) (hnu j).le) (hmu j).le
      _ = 512 * nu j * (∏ k, mu k) := by rw [← hdecomp mu]; ring
  have hfinal : c * mu j ≤ nu j * (512 * C ^ 4) := by
    calc
      _ ≤ 512 * nu j * (∏ k, mu k) := hstep
      _ ≤ 512 * nu j * C ^ 4 := mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) (hnu j).le)
      _ = _ := by ring
  have hd : 0 < 512 * C ^ 4 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  exact hfinal


theorem source_uniform_products239 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ C5 c10 : ℝ, 0 < C5 ∧ 0 < c10 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ),
        (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 →
        c10 ≤ (∏ j, compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 j) ∧
        (∏ i, sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ≤ C5 ∧
        (∏ j, pairProducts239 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j) ≤ C5^4 := by
  obtain ⟨_,C5,_,hC,hfive⟩ := source_original_uniform_minima_two_sided5 A2 A3 L h2 h3 hL
  obtain ⟨c10,_,hc,_,hten⟩ := source_original_uniform_minima_two_sided10 (compound237 A2)
    (compound237 A3) (compound237 L) (compound_unit238 A2 h2) (compound_unit238 A3 h3) (compound_unit238 L hL)
  refine ⟨C5,c10,hC,hc,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb
  have hf := (hfive Q hQ c0 c2 c3 hc2 hc3 hb).2
  have hn (c : Fin 5 → ℝ) (h : ∀ i, c i ≤ 0) : ∀ s, normalizedWeights238 c s ≤ 0 := by
    intro s
    exact div_nonpos_of_nonpos_of_nonneg (add_nonpos (h _) (h _)) (by norm_num)
  refine ⟨(hten (Q^2) (powered_gt_one238 Q hQ) (normalizedWeights238 c0)
    (normalizedWeights238 c2) (normalizedWeights238 c3) (hn c2 hc2) (hn c3 hc3)
    (normalized_balance238 c0 c2 c3 hb)).1,hf,?_⟩
  rw [pairProducts_product239]
  exact pow_le_pow_left₀
    (Finset.prod_pos (fun i _ => (sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1 i)).le hf 4

theorem source_uniform_comparison239 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ C5 c10 κ : ℝ, 0 < C5 ∧ 0 < c10 ∧ 0 < κ ∧ κ = c10/(512*C5^4) ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ),
        (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 →
        ∀ j, κ*pairProducts239 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j ≤
          compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 j ∧
          compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 j ≤
            2*pairProducts239 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j := by
  obtain ⟨C5,c10,hC,hc,hprod⟩ := source_uniform_products239 A2 A3 L h2 h3 hL
  refine ⟨C5,c10,c10/(512*C5^4),hC,hc,by positivity,rfl,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb j
  obtain ⟨hn,_,hm⟩ := hprod Q hQ c0 c2 c3 hc2 hc3 hb
  have hu := compoundMinima_upper239 A2 A3 L hL Q hQ c0 c2 c3
  exact ⟨product_reverse239 _ _ c10 C5
    (pairProducts_pos239 _ (sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1)
    (compoundMinima_pos_mono239 A2 A3 L hL Q hQ c0 c2 c3).1 hu hn hm hC j,hu j⟩

end CompoundFeasibility.ExteriorGap52_239
