import SubspaceBridge.SourceMinorIntegration6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceLocalUpper6
open SourceHeightBounds6 SourceMixed6 SourceProper6 Auxiliary6.SourceExpansion

theorem real_det5_le (A : Matrix (Fin 5) (Fin 5) ℝ) (b : Fin 5 → ℝ)
    (hb : ∀ k, 0 ≤ b k) (hA : ∀ j k, ‖A j k‖ ≤ b k) :
    ‖A.det‖ ≤ 120*∏ k, b k := by
  rw [Matrix.det_apply]
  calc
    ‖∑ sigma : Equiv.Perm (Fin 5), sigma.sign • ∏ k, A (sigma k) k‖ ≤
        ∑ sigma : Equiv.Perm (Fin 5), ‖sigma.sign • ∏ k, A (sigma k) k‖ := norm_sum_le _ _
    _ = ∑ sigma : Equiv.Perm (Fin 5), ∏ k, ‖A (sigma k) k‖ := by
      simp only [norm_units_zsmul,norm_prod]
    _ ≤ ∑ _sigma : Equiv.Perm (Fin 5), ∏ k, b k := by
      apply Finset.sum_le_sum
      intro sigma _
      exact Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hA (sigma k) k)
    _ = 120*∏ k, b k := by
      norm_num [Fintype.card_perm, Nat.factorial]

theorem real_transformed_det5_le (B : Matrix (Fin 6) (Fin 6) ℝ)
    (v : Matrix (Fin 6) (Fin 6) ℤ) (Q delta : ℝ) (hQ : 1 < Q) (hd : 0 < delta)
    (c : Fin 6 → ℝ)
    (hv : ∀ (j : Fin 5) k, ‖(B *ᵥ (fun i => (v j.castSucc i : ℝ))) k‖ ≤ Q^(c k-delta))
    (i : Fin 6) :
    ‖((transformedFrame6 B v).submatrix Fin.castSucc i.succAbove).det‖ ≤
      120*∏ k : Fin 5, Q^(c (i.succAbove k)-delta/2) := by
  apply real_det5_le
  · intro k
    exact (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _).le
  · intro j k
    change ‖transformedFrame6 B v j.castSucc (i.succAbove k)‖ ≤ _
    rw [transformedFrame6_apply]
    exact (strict_local_slack6 Q (c (i.succAbove k)) delta _ hQ hd (hv j _)).le


theorem padic_sum_bound6 (p : ℕ) [Fact p.Prime] {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ℚ_[p]) (C : ℝ) (hC : 0 ≤ C) :
    (∀ i ∈ s, ‖f i‖ ≤ C) → ‖∑ i ∈ s, f i‖ ≤ C := by
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using hC
  | @insert a s ha ih =>
    intro hf
    rw [Finset.sum_insert ha]
    apply (padicNormE.nonarchimedean _ _).trans
    apply max_le
    · exact hf a (Finset.mem_insert_self _ _)
    · exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem padic_det5_le (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 5) (Fin 5) ℚ_[p]) (b : Fin 5 → ℝ)
    (hb : ∀ k, 0 ≤ b k) (hA : ∀ j k, ‖A j k‖ ≤ b k) :
    ‖A.det‖ ≤ ∏ k, b k := by
  rw [Matrix.det_apply]
  apply padic_sum_bound6 p Finset.univ _ _ (Finset.prod_nonneg (fun k _ => hb k))
  intro sigma _
  rw [norm_units_zsmul,norm_prod]
  exact Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hA (sigma k) k)

theorem padic_transformed_det5_le (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (v : Matrix (Fin 6) (Fin 6) ℤ)
    (Q : ℝ) (hQ : 0 < Q) (c : Fin 6 → ℝ)
    (hv : ∀ (j : Fin 5) k, ‖(B *ᵥ (fun i => (v j.castSucc i : ℚ_[p]))) k‖ ≤ Q^(c k))
    (i : Fin 6) :
    ‖((transformedFrame6 B v).submatrix Fin.castSucc i.succAbove).det‖ ≤
      ∏ k : Fin 5, Q^(c (i.succAbove k)) := by
  apply padic_det5_le
  · intro k
    exact (Real.rpow_pos_of_pos hQ _).le
  · intro j k
    change ‖transformedFrame6 B v j.castSucc (i.succAbove k)‖ ≤ _
    rw [transformedFrame6_apply]
    exact hv j _


theorem integer_g_three_place6 (g : ℤ) (hg : g ≠ 0) :
    1 ≤ ‖(g : ℝ)‖*‖(g : ℚ_[2])‖*‖(g : ℚ_[3])‖ := by
  have h := JSP000334.rothInteger_three_place_lower g hg
  simpa [JSP000334.rothLocalAbs,Real.norm_eq_abs,← finite_norm 2,← finite_norm 3] using h

theorem normalized_mixed_norm_le_det_product6
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (v : Matrix (Fin 6) (Fin 6) ℤ) (M a : Fin 6 → ℤ)
    (hn : minorNormalization6 v M a) (hi : actualTransformedCofactors6 A2 A3 L v M a)
    (s : MixedIndex6) :
    actualNormProduct6 A2 A3 L M s ≤
      ‖((transformedFrame6 (compound L) v).submatrix Fin.castSucc (s 0).succAbove).det‖*
      ‖((transformedFrame6 (finiteMatrix 2 A2) v).submatrix Fin.castSucc (s 1).succAbove).det‖*
      ‖((transformedFrame6 (finiteMatrix 3 A3) v).submatrix Fin.castSucc (s 2).succAbove).det‖ := by
  let g : ℤ := ∑ k, a k*rawNormal6 v k
  have hg : g ≠ 0 := hn.2.1
  have hr := congrArg (norm : ℝ → ℝ) (hi (s 0)).1
  have h2 := congrArg (norm : ℚ_[2] → ℝ) (hi (s 1)).2.1
  have h3 := congrArg (norm : ℚ_[3] → ℝ) (hi (s 2)).2.2
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul] at hr h2 h3
  have hP : 0 ≤ actualNormProduct6 A2 A3 L M s := by
    unfold actualNormProduct6
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  calc
    actualNormProduct6 A2 A3 L M s = 1*actualNormProduct6 A2 A3 L M s := by ring
    _ ≤ (‖(g : ℝ)‖*‖(g : ℚ_[2])‖*‖(g : ℚ_[3])‖)*actualNormProduct6 A2 A3 L M s :=
      mul_le_mul_of_nonneg_right (integer_g_three_place6 g hg) hP
    _ = _ := by
      rw [hr,h2,h3]
      unfold actualNormProduct6
      dsimp only [g]
      ring

theorem mixed_exponent_cancel6 (c : Fin 3 → Fin 6 → ℝ) (delta : ℝ)
    (hb : (∑ tau, ∑ i, c tau i) = 0) (s : MixedIndex6) :
    (∑ k : Fin 5, (c 0 ((s 0).succAbove k)-delta/2)) +
      (∑ k : Fin 5, c 1 ((s 1).succAbove k)) +
      (∑ k : Fin 5, c 2 ((s 2).succAbove k)) =
      -5*(delta/2)-(∑ tau, c tau (s tau)) := by
  have h0 := Fin.sum_univ_succAbove (c 0) (s 0)
  have h1 := Fin.sum_univ_succAbove (c 1) (s 1)
  have h2 := Fin.sum_univ_succAbove (c 2) (s 2)
  have hb' : (∑ i, c 0 i)+(∑ i, c 1 i)+(∑ i, c 2 i) = 0 := by
    simpa [Fin.sum_univ_three] using hb
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Fin.sum_univ_three]
  linarith


theorem mixed_power_product6 (Q delta : ℝ) (hQ : 0 < Q)
    (c : Fin 3 → Fin 6 → ℝ) (hb : (∑ tau, ∑ i, c tau i) = 0) (s : MixedIndex6) :
    (120*∏ k : Fin 5, Q^(c 0 ((s 0).succAbove k)-delta/2))*
      (∏ k : Fin 5, Q^(c 1 ((s 1).succAbove k)))*
      (∏ k : Fin 5, Q^(c 2 ((s 2).succAbove k))) =
      120*Q^(-5*(delta/2)-(∑ tau, c tau (s tau))) := by
  simp only [← Real.rpow_sum_of_pos hQ]
  rw [← mixed_exponent_cancel6 c delta hb s,Real.rpow_add hQ,Real.rpow_add hQ]
  ring

theorem mixed_det_product_bound6
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (v : Matrix (Fin 6) (Fin 6) ℤ) (Q delta : ℝ) (hQ : 1 < Q) (hd : 0 < delta)
    (c : Fin 3 → Fin 6 → ℝ) (hb : (∑ tau, ∑ i, c tau i) = 0)
    (hR : ∀ (j : Fin 5) k, ‖(compound L *ᵥ (fun i => (v j.castSucc i : ℝ))) k‖ ≤ Q^(c 0 k-delta))
    (h2 : ∀ (j : Fin 5) k, ‖(finiteMatrix 2 A2 *ᵥ (fun i => (v j.castSucc i : ℚ_[2]))) k‖ ≤ Q^(c 1 k))
    (h3 : ∀ (j : Fin 5) k, ‖(finiteMatrix 3 A3 *ᵥ (fun i => (v j.castSucc i : ℚ_[3]))) k‖ ≤ Q^(c 2 k))
    (s : MixedIndex6) :
    ‖((transformedFrame6 (compound L) v).submatrix Fin.castSucc (s 0).succAbove).det‖*
      ‖((transformedFrame6 (finiteMatrix 2 A2) v).submatrix Fin.castSucc (s 1).succAbove).det‖*
      ‖((transformedFrame6 (finiteMatrix 3 A3) v).submatrix Fin.castSucc (s 2).succAbove).det‖ ≤
      120*Q^(-5*(delta/2)-(∑ tau, c tau (s tau))) := by
  have hq : 0 < Q := lt_trans zero_lt_one hQ
  have hr := real_transformed_det5_le (compound L) v Q delta hQ hd (c 0) hR (s 0)
  have hp2 := padic_transformed_det5_le 2 (finiteMatrix 2 A2) v Q hq (c 1) h2 (s 1)
  have hp3 := padic_transformed_det5_le 3 (finiteMatrix 3 A3) v Q hq (c 2) h3 (s 2)
  calc
    _ ≤ (120*∏ k : Fin 5, Q^(c 0 ((s 0).succAbove k)-delta/2))*
        (∏ k : Fin 5, Q^(c 1 ((s 1).succAbove k)))*
        (∏ k : Fin 5, Q^(c 2 ((s 2).succAbove k))) := by
      exact mul_le_mul (mul_le_mul hr hp2 (norm_nonneg _) (by positivity)) hp3
        (norm_nonneg _) (by positivity)
    _ = _ := mixed_power_product6 Q delta hq c hb s

theorem actual_mixed_upper6
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (v : Matrix (Fin 6) (Fin 6) ℤ) (M a : Fin 6 → ℤ)
    (hn : minorNormalization6 v M a) (hi : actualTransformedCofactors6 A2 A3 L v M a)
    (Q delta : ℝ) (hQ : 1 < Q) (hd : 0 < delta)
    (c : Fin 3 → Fin 6 → ℝ) (hb : (∑ tau, ∑ i, c tau i) = 0)
    (hR : ∀ (j : Fin 5) k, ‖(compound L *ᵥ (fun i => (v j.castSucc i : ℝ))) k‖ ≤ Q^(c 0 k-delta))
    (h2 : ∀ (j : Fin 5) k, ‖(finiteMatrix 2 A2 *ᵥ (fun i => (v j.castSucc i : ℚ_[2]))) k‖ ≤ Q^(c 1 k))
    (h3 : ∀ (j : Fin 5) k, ‖(finiteMatrix 3 A3 *ᵥ (fun i => (v j.castSucc i : ℚ_[3]))) k‖ ≤ Q^(c 2 k))
    (s : MixedIndex6) (hs : s ∈ admissibleMixed6 c (delta/2)) :
    actualNormProduct6 A2 A3 L M s ≤ 120*Q^(-17*delta/8) ∧
      actualNormProduct6 A2 A3 L M s < 120*Q^(-delta/8) := by
  have hnD := normalized_mixed_norm_le_det_product6 A2 A3 L v M a hn hi s
  have hD := mixed_det_product_bound6 A2 A3 L v Q delta hQ hd c hb hR h2 h3 s
  have hm := source_half_margin6 c delta s hs
  have he : -5*(delta/2)-(∑ tau, c tau (s tau)) ≤ -17*delta/8 := by linarith
  have hstrong : actualNormProduct6 A2 A3 L M s ≤ 120*Q^(-17*delta/8) :=
    hnD.trans (hD.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ.le he) (by norm_num)))
  refine ⟨hstrong,hstrong.trans_lt ?_⟩
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_exponent_lt hQ (by linarith)) (by norm_num)

end CompoundFeasibility.SourceLocalUpper6
