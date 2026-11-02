import SubspaceBridge.SourceCompoundGap53_242
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag244
open Exterior53_242

theorem short_triple_cutoff244 (kappa delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ Q : ℝ, T < Q → 6/kappa < Q^(delta/2) :=
  compound_gap_cutoff42 (6/kappa) delta hd

theorem short_triple_bound244 (mu nu : Fin 10 → ℝ) (kappa Q delta : ℝ)
    (hk : 0 < kappa) (hQ : 1 < Q) (hm : 0 < mu 8)
    (hcomp : kappa*mu 8 ≤ nu 8)
    (hgap : nu 8 < nu 9*(Q^3)^(-delta/6))
    (hcut : 6/kappa < Q^(delta/2)) : 6*mu 8 < nu 9 := by
  have ht := Real.rpow_pos_of_pos (zero_lt_one.trans hQ) (delta/2)
  have he : Q^(-delta/2)*Q^(delta/2) = 1 := by
    rw [← Real.rpow_add (zero_lt_one.trans hQ)]
    convert Real.rpow_zero Q using 1 <;> congr 1 <;> ring
  rw [← powered_gap_exponent3242 Q delta hQ] at hgap
  have hn := mul_lt_mul_of_pos_right hgap ht
  rw [mul_assoc,he,mul_one] at hn
  have hc : 6 < Q^(delta/2)*kappa := (div_lt_iff₀ hk).mp hcut
  calc
    6*mu 8 < (Q^(delta/2)*kappa)*mu 8 := mul_lt_mul_of_pos_right hc hm
    _ = (kappa*mu 8)*Q^(delta/2) := by ring
    _ ≤ nu 8*Q^(delta/2) := mul_le_mul_of_nonneg_right hcomp ht.le
    _ < nu 9 := hn

theorem actual_short_triples244
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ)
    (hshort : 6*tripleProducts242 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) 8 <
      compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 9) :
    ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
      (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c0)
        (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ∧
      let z := orderedWedge3242 (fun i => (u i : Fin 5 → ℤ)) (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3)
      (∀ j, z j ∈ directGroup3242 A2 A3 Q c2 c3) ∧
      LinearIndependent ℝ (fun j => integerReal (z j)) ∧
      ∀ j : Fin 9, coordinateGauge10 (originalCoordinates10 (compound3242 L) (compound_real_unit3242 L hL)
        (Q^3) (powered_gt_one3242 Q hQ) (normalizedWeights3242 c0)) (integerReal (z j.castSucc)) <
          compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 9 := by
  obtain ⟨u,hu,ha,hm,hi,hb,hg⟩ := actual_wedge_frame3242 A2 A3 L hL Q hQ c0 c2 c3
  refine ⟨u,hu,ha,hm,hi,?_⟩
  intro j
  exact (hg j.castSucc).trans_lt ((mul_le_mul_of_nonneg_left
    (tripleProducts_mono242 _ (show j.castSucc ≤ (8 : Fin 10) by change j.val ≤ 8; omega))
    (by norm_num : (0 : ℝ) ≤ 6)).trans_lt hshort)

end CompoundFeasibility.SourceFlag244
