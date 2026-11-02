import SubspaceBridge.SourceOriginalCofactorUpper10
import SubspaceBridge.SourceFrameWitness10
import SubspaceBridge.SourceSelectedTail10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceOriginalVariable10
open SourceSelectedSet10 SourceSelectedUpper10 OriginalDual10 SourceOriginalBudget10 SourceSampling10
noncomputable section

structure OriginalData10 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (delta : ℝ) (S0 : Finset MixedIndex10) where
  A : Fin 10 → ℝ
  positive : ∀ i, 0 < A i
  f2 : Fin 10 → ℤ
  f3 : Fin 10 → ℤ
  nonpos2 : ∀ i, f2 i ≤ 0
  nonpos3 : ∀ i, f3 i ≤ 0
  sizes : ∀ i, A i < Q ∧ (A i)⁻¹ < Q ∧ (2 : ℝ)^(-f2 i) < Q ∧ (3 : ℝ)^(-f3 i) < Q
  balance : (∏ i, A i*(2 : ℝ)^(f2 i)*(3 : ℝ)^(f3 i)) = 1
  selected : ∀ s ∈ S0, 1 ≤ A (s 0)*(2 : ℝ)^(f2 (s 1))*(3 : ℝ)^(f3 (s 2))*Q^(delta/2)
  u : Fin 10 → Fin 10 → ℤ
  member2 : ∀ j i, padicNorm 2 ((A2 *ᵥ (fun k => (u j k : ℚ))) i) ≤ (2 : ℚ)^(f2 i)
  member3 : ∀ j i, padicNorm 3 ((A3 *ᵥ (fun k => (u j k : ℚ))) i) ≤ (3 : ℚ)^(f3 i)
  independent : LinearIndependent ℝ (fun j => integerReal (u j : Fin 10 → ℤ))
  attaining : ∀ j, coordinateGauge10 (originalCoordinates10 L hL Q hQ (fun i => normalizedWidth10 Q (A i)))
    (integerReal (u j : Fin 10 → ℤ)) = sourceMinima10 A2 A3 L hL Q hQ
      (fun i => normalizedWidth10 Q (A i)) (fun i => normalizedFinite10 2 Q (f2 i))
      (fun i => normalizedFinite10 3 Q (f3 i)) j
  small : sourceMinima10 A2 A3 L hL Q hQ
    (fun i => normalizedWidth10 Q (A i)) (fun i => normalizedFinite10 2 Q (f2 i))
    (fun i => normalizedFinite10 3 Q (f3 i)) 8 < Q^(-delta)

theorem original_data_cofactor_upper10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset MixedIndex10}
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1)
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (s : MixedIndex10) (hs : s ∈ S0) :
    mixedProduct10 A2 A3 L (integerLastDual10 (fun j => (D.u j : Fin 10 → ℤ))) s ≤
      362880*Q^(-17*delta/2) := by
  have hp := sourceMinima10_pos_mono A2 A3 L hL Q hQ
    (fun i => normalizedWidth10 Q (D.A i)) (fun i => normalizedFinite10 2 Q (D.f2 i))
    (fun i => normalizedFinite10 3 Q (D.f3 i))
  let u' : Fin 10 → originalSourceGroup10 A2 A3 Q
      (fun i => normalizedFinite10 2 Q (D.f2 i)) (fun i => normalizedFinite10 3 Q (D.f3 i)) :=
    fun j => ⟨D.u j,(normalized_source_group_exact10 A2 A3 Q hQ D.f2 D.f3 D.nonpos2 D.nonpos3
      (D.u j)).mpr ⟨D.member2 j,D.member3 j⟩⟩
  have hpoint := source_original_coordinate_bounds10 A2 A3 L hL Q hQ
    (fun i => normalizedWidth10 Q (D.A i)) (fun i => normalizedFinite10 2 Q (D.f2 i))
    (fun i => normalizedFinite10 3 Q (D.f3 i)) u' D.attaining
  simp_rw [normalized_width_exact10 Q _ hQ (D.positive _)] at hpoint
  exact original_absolute_cofactor_upper10 A2 A3 L h2 h3 hLd Q delta hQ D.A D.positive
    D.f2 D.f3 D.nonpos2 D.nonpos3 D.balance _ hp.1 hp.2 D.small
    (fun j => (D.u j : Fin 10 → ℤ)) hpoint D.member2 D.member3 s (D.selected s hs)

theorem original_absolute_short_frame10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (Q : ℝ) (hQ : 1 < Q) (S0 : Finset MixedIndex10)
      (D : OriginalData10 A2 A3 L hL Q hQ delta S0), T < Q →
      Nonempty (OriginalFrameWitness10 A2 A3 L Q delta
        (fun i => normalizedFinite10 2 Q (D.f2 i)) (fun i => normalizedFinite10 3 Q (D.f3 i))
        (fun j => (D.u j : Fin 10 → ℤ))) := by
  obtain ⟨T1,hT1,hgap⟩ := SourceAbsoluteGap10.source_absolute_gap_uniform10 A2 A3 L h2 h3 hL delta hd
  obtain ⟨T2,hT2,hframe⟩ := original_frame_witness10 A2 A3 L h2 h3 hL delta hd
  refine ⟨max T1 T2,hT1.trans_le (le_max_left _ _),?_⟩
  intro Q hQ S0 D hTQ
  have hc0 (i) : |normalizedWidth10 Q (D.A i)| ≤ 1 :=
    abs_le.mpr ⟨(logWeight10_bounds Q _ hQ (D.positive i) (D.sizes i).1 (D.sizes i).2.1).1.le,
      (logWeight10_bounds Q _ hQ (D.positive i) (D.sizes i).1 (D.sizes i).2.1).2.le⟩
  have hc2 (i) := normalized_finite_bounds10 2 (by decide) Q hQ (D.f2 i) (D.nonpos2 i) (D.sizes i).2.2.1
  have hc3 (i) := normalized_finite_bounds10 3 (by decide) Q hQ (D.f3 i) (D.nonpos3 i) (D.sizes i).2.2.2
  have hb := normalized_balance10 Q D.A D.positive D.f2 D.f3 D.balance
  have hg := hgap Q hQ _ _ _ (fun i => (hc2 i).2) (fun i => (hc3 i).2) hb
    ((le_max_left _ _).trans_lt hTQ) D.small
  let u' : Fin 10 → originalSourceGroup10 A2 A3 Q
      (fun i => normalizedFinite10 2 Q (D.f2 i)) (fun i => normalizedFinite10 3 Q (D.f3 i)) :=
    fun j => ⟨D.u j,(normalized_source_group_exact10 A2 A3 Q hQ D.f2 D.f3 D.nonpos2 D.nonpos3
      (D.u j)).mpr ⟨D.member2 j,D.member3 j⟩⟩
  exact hframe Q hQ _ _ _ hc0 (fun i => ⟨(hc2 i).1.le,(hc2 i).2⟩)
    (fun i => ⟨(hc3 i).1.le,(hc3 i).2⟩) hb ((le_max_right _ _).trans_lt hTQ)
    u' D.independent D.attaining hg

end
end CompoundFeasibility.SourceOriginalVariable10
