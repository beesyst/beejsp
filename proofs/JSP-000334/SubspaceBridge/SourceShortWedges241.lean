import SubspaceBridge.SourceCompoundGap52_239
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag241
open Exterior52_237 Exterior52_238 ExteriorGap52_239

theorem short_wedge_cutoff241 (kappa delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ Q : ℝ, T < Q → 2/kappa < Q^(delta/2) :=
  compound_gap_cutoff42 (2/kappa) delta hd

theorem short_pair_bound241 (mu nu : Fin 10 → ℝ) (kappa Q delta : ℝ)
    (hk : 0 < kappa) (hQ : 1 < Q) (hm : 0 < mu 8)
    (hcomp : kappa*mu 8 ≤ nu 8)
    (hgap : nu 8 < nu 9*(Q^2)^(-delta/4))
    (hcut : 2/kappa < Q^(delta/2)) : 2*mu 8 < nu 9 := by
  have ht := Real.rpow_pos_of_pos (zero_lt_one.trans hQ) (delta/2)
  have he : Q^(-delta/2)*Q^(delta/2) = 1 := by
    rw [← Real.rpow_add (zero_lt_one.trans hQ)]
    convert Real.rpow_zero Q using 1 <;> congr 1 <;> ring
  rw [← powered_gap_exponent239 Q delta hQ] at hgap
  have hn := mul_lt_mul_of_pos_right hgap ht
  rw [mul_assoc,he,mul_one] at hn
  have hc : 2 < Q^(delta/2)*kappa := (div_lt_iff₀ hk).mp hcut
  calc
    2*mu 8 < (Q^(delta/2)*kappa)*mu 8 := mul_lt_mul_of_pos_right hc hm
    _ = (kappa*mu 8)*Q^(delta/2) := by ring
    _ ≤ nu 8*Q^(delta/2) := mul_le_mul_of_nonneg_right hcomp ht.le
    _ < nu 9 := hn

theorem actual_short_wedges241
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ)
    (hshort : 2*pairProducts239 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) 8 <
      compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 9) :
    ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
      (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c0)
        (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ∧
      let z := orderedWedge239 (fun i => (u i : Fin 5 → ℤ)) (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3)
      (∀ j, z j ∈ directGroup238 A2 A3 Q c2 c3) ∧
      LinearIndependent ℝ (fun j => integerReal (z j)) ∧
      ∀ j : Fin 9, coordinateGauge10 (originalCoordinates10 (compound237 L) (compound_unit238 L hL)
        (Q^2) (powered_gt_one238 Q hQ) (normalizedWeights238 c0)) (integerReal (z j.castSucc)) <
          compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 9 := by
  obtain ⟨u,hu,ha,hm,hi,hb,hg⟩ := actual_wedge_frame239 A2 A3 L hL Q hQ c0 c2 c3
  refine ⟨u,hu,ha,hm,hi,?_⟩
  intro j
  exact (hg j.castSucc).trans_lt ((mul_le_mul_of_nonneg_left
    (pairProducts_mono239 _ (show j.castSucc ≤ (8 : Fin 10) by change j.val ≤ 8; omega))
    (by norm_num : (0 : ℝ) ≤ 2)).trans_lt hshort)

variable (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
  (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ)

theorem sourceMinima10_short_span241 (v : Fin 9 → Fin 10 → ℝ)
    (hv : LinearIndependent ℝ v)
    (hvL : ∀ j, v j ∈ integerRealImage (originalSourceGroup10 A2 A3 Q c2 c3))
    (hvg : ∀ j, coordinateGauge10 (originalCoordinates10 L hL Q hQ c0) (v j) <
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9)
    (z : Fin 10 → ℝ) (hz : z ∈ integerRealImage (originalSourceGroup10 A2 A3 Q c2 c3))
    (hzg : coordinateGauge10 (originalCoordinates10 L hL Q hQ c0) z <
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9) :
    z ∈ Submodule.span ℝ (Set.range v) := by
  classical
  by_contra hout
  let w : Fin 10 → Fin 10 → ℝ := Fin.snoc v z
  have hi : LinearIndependent ℝ w := linearIndependent_fin_snoc.mpr ⟨hv,hout⟩
  have hwL : ∀ i, w i ∈ integerRealImage (originalSourceGroup10 A2 A3 Q c2 c3) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [w,Fin.snoc_last] using hz
    · simpa only [w,Fin.snoc_castSucc] using hvL j
  have hwg : ∀ i, coordinateGauge10 (originalCoordinates10 L hL Q hQ c0) (w i) <
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9 := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [w,Fin.snoc_last] using hzg
    · simpa only [w,Fin.snoc_castSucc] using hvg j
  obtain ⟨i,_,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => coordinateGauge10 (originalCoordinates10 L hL Q hQ c0) (w i)) Finset.univ_nonempty
  have hle := (sourceMinima10_radius_set_properties A2 A3 L hL Q hQ c0 c2 c3 9).2.2.2
    ⟨w,hi,hwL,fun j => hmax j (Finset.mem_univ j)⟩
  exact (not_lt_of_ge hle) (hwg i)

end CompoundFeasibility.SourceFlag241
