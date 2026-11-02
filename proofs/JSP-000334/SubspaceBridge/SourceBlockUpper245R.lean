import SubspaceBridge.SourceBlockNine245Q
import SubspaceBridge.SourceBlockSeparation245Q
import SubspaceBridge.SourceBlockLower245Q
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.BlockReduction245R
open BlockReduction245P BlockReduction245Q Exterior53_242

theorem integerReal_single245R (i : Fin 5) :
    integerReal (Pi.single i (1 : ℤ)) = Pi.single i (1 : ℝ) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [integerReal]
  · simp [integerReal, Pi.single_apply, h, Ne.symm h]

theorem integerReal_join245Q (x y : Fin 5 → ℤ) :
    integerReal (join245Q x y) = join245Q (integerReal x) (integerReal y) := by
  ext j
  change ((join245Q x y j : ℤ) : ℝ) = _
  unfold join245Q
  cases BlockReduction245P.blockIndex245P.symm j <;> rfl

theorem nine_membership245R (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c2 c3 : Fin 5 → ℝ)
    (u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3) (j : Fin 9) :
    nineFrame245Q (fun i => integerReal (u i : Fin 5 → ℤ)) j ∈
      integerRealImage (originalSourceGroup10 (block245P A2) (block245P A3)
        (Q^3) (weightp245P c2) (weightp245P c3)) := by
  unfold nineFrame245Q
  cases h : (finSumFinEquiv : Fin 4 ⊕ Fin 5 ≃ Fin 9).symm j with
  | inl i =>
    simp only [Sum.elim_inl]
    refine ⟨join245Q (u i.castSucc : Fin 5 → ℤ) 0,?_,?_⟩
    · apply (block_source_group245Q A2 A3 Q c2 c3 _).mpr
      rw [first_join245Q]
      exact (u i.castSucc).property
    · rw [integerReal_join245Q,map_zero]
  | inr i =>
    simp only [Sum.elim_inr]
    refine ⟨join245Q 0 (Pi.single i (1 : ℤ)),?_,?_⟩
    · apply (block_source_group245Q A2 A3 Q c2 c3 _).mpr
      rw [first_join245Q]
      exact (originalSourceGroup5 A2 A3 Q c2 c3).zero_mem
    · rw [integerReal_join245Q,map_zero]
      rw [integerReal_single245R]

theorem source_upper_of_separation245R (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ)
    (hsep : (Q^2)⁻¹ ≤ Q^2*sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3) :
    sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
      (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0) (weightp245P c2) (weightp245P c3) 8 ≤
      Q^2*sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3 := by
  obtain ⟨u,hu,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima5_attaining A2 A3 L hL Q hQ c0 c2 c3
  let v := nineFrame245Q (fun j => integerReal (u j : Fin 5 → ℤ))
  apply (sourceMinima10_radius_set_properties (block245P A2) (block245P A3) (block245P L)
    (block_unit245Q L hL) (Q^3) (powered_gt_one3242 Q hQ)
    (weight0245P c0) (weightp245P c2) (weightp245P c3) 8).2.2.2
  refine ⟨v,nine_independent245Q _ hu,?_,?_⟩
  · exact nine_membership245R A2 A3 Q c2 c3 u
  · intro j
    change coordinateGauge10 _ (nineFrame245Q _ j) ≤ _
    unfold nineFrame245Q
    cases h : (finSumFinEquiv : Fin 4 ⊕ Fin 5 ≃ Fin 9).symm j with
    | inl i =>
      simp only [Sum.elim_inl]
      rw [gauge_original245Q L hL Q hQ,hatt]
      exact mul_le_mul_of_nonneg_left (hmono (show i.castSucc ≤ (3 : Fin 5) by change i.val ≤ 3; omega))
        (sq_nonneg Q)
    | inr i =>
      simp only [Sum.elim_inr]
      rw [gauge_dummy245Q L hL Q hQ]
      exact hsep

theorem source_comparisons245R (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) :
    ∃ T : ℝ, 1 < T ∧ ∀ (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
      (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ),
      (∀ i, |c0 i| ≤ 1) → T < Q →
      (sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
        (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0) (weightp245P c2) (weightp245P c3) 8 ≤
        Q^2*sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3) ∧
      (Q^2*sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 4 ≤
        sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
        (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0) (weightp245P c2) (weightp245P c3) 9) := by
  obtain ⟨D,T,hD,hT,hsep⟩ := source_separation245Q L hL
  refine ⟨T,hT,?_⟩
  intro A2 A3 Q hQ c0 c2 c3 hc hTQ
  exact ⟨source_upper_of_separation245R A2 A3 L hL Q hQ c0 c2 c3
    ((hsep A2 A3 Q hQ c0 c2 c3 hc).2 hTQ),source_lower245Q A2 A3 L hL Q hQ c0 c2 c3⟩

theorem source_upper245R (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) :
    ∃ T : ℝ, 1 < T ∧ ∀ (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
      (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ),
      (∀ i, |c0 i| ≤ 1) → T < Q →
      sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
        (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0) (weightp245P c2) (weightp245P c3) 8 ≤
        Q^2*sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3 := by
  obtain ⟨T,hT,hcomp⟩ := source_comparisons245R L hL
  exact ⟨T,hT,fun A2 A3 Q hQ c0 c2 c3 hc hTQ =>
    (hcomp A2 A3 Q hQ c0 c2 c3 hc hTQ).1⟩

end CompoundFeasibility.BlockReduction245R
