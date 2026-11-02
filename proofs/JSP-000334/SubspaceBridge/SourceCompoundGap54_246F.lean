import SubspaceBridge.SourceCompoundComparison54_246F
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior54_246

theorem ratio_gap4246 (mu nu : Fin 5 → ℝ) (κ Q delta : ℝ) (hk : 0 < κ) (hQ : 1 < Q)
    (hcomp : ∀ j, κ*mu j ≤ nu j ∧ nu j ≤ 24*mu j)
    (hg : mu 3 < mu 4*Q^(-delta)) : nu 3 < (24/κ)*nu 4*Q^(-delta) := by
  calc
    nu 3 ≤ 24*mu 3 := (hcomp 3).2
    _ < 24*(mu 4*Q^(-delta)) := mul_lt_mul_of_pos_left hg (by norm_num)
    _ = (24/κ)*(κ*mu 4)*Q^(-delta) := by field_simp; ring
    _ ≤ (24/κ)*nu 4*Q^(-delta) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcomp 4).1 (by positivity))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _).le

theorem powered_gap_exponent4246 (Q delta : ℝ) (hQ : 1 < Q) :
    Q^(-delta/2) = (Q^4)^(-delta/8) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (zero_lt_one.trans hQ).le]
  congr 1
  ring

theorem source_uniform_gap4246 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ C5 ccompound κ : ℝ, 0 < C5 ∧ 0 < ccompound ∧ 0 < κ ∧ κ = ccompound/(331776*C5^4) ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 < T ∧
        ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ),
          (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 → T < Q →
          sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 0 <
            sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 1*Q^(-delta) →
          (∀ j, κ*fourProducts246 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j ≤
            compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3 j ∧
            compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3 j ≤
              24*fourProducts246 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j) ∧
          compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3 3 <
            compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3 4*(Q^4)^(-delta/8) := by
  obtain ⟨C5,ccompound,κ,hC,hc,hk,he,hcompare⟩ := source_uniform_comparison4246 A2 A3 L h2 h3 hL
  refine ⟨C5,ccompound,κ,hC,hc,hk,he,?_⟩
  intro delta hd
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 (24/κ) delta hd
  refine ⟨T,hT,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb hTQ hg
  have hcq := hcompare Q hQ c0 c2 c3 hc2 hc3 hb
  have hp := sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  have hpair := fourProducts_gap246 _ hp.1 Q delta hg
  have hr := ratio_gap4246 _ _ κ Q delta hk hQ hcq hpair
  have hgenuine := absorb_compound_gap42 _ _ (24/κ) Q delta
    ((compoundMinima_pos_mono4246 A2 A3 L hL Q hQ c0 c2 c3).1 4) hQ (hcut Q hTQ) hr
  exact ⟨hcq,by rw [powered_gap_exponent4246 Q delta hQ] at hgenuine; exact hgenuine⟩

theorem source_rank1_compound4_gap246 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1)
    (hL : IsUnit L) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ C5 ccompound κ : ℝ, 0 < C5 ∧ 0 < ccompound ∧ 0 < κ ∧ κ = ccompound/(331776*C5^4) ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 < T ∧ 0 < delta/8 ∧
        ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ),
          (∀ i, |c0 i| ≤ 1) → (∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) →
          (∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 → T < Q →
          sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 0 <
            sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 1*Q^(-delta) →
          let B2 := compound4246 A2
          let B3 := compound4246 A3
          let B0 := compound4246 L
          let Qprime := Q^4
          let cp0 := normalizedWeights4246 c0
          let cp2 := normalizedWeights4246 c2
          let cp3 := normalizedWeights4246 c3
          let nu := sourceMinima5 B2 B3 B0 (compound_unit4246 L hL)
            Qprime (powered_gt_one4246 Q hQ) cp0 cp2 cp3
          let mu := fourProducts246 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3)
          B2.det=1 ∧ B3.det=1 ∧ B0.det=1 ∧
          (∀ s t, IsAlgebraic ℚ (B0 s t)) ∧
          (∀ s, |cp0 s|≤1) ∧ (∀ s, -1≤cp2 s ∧ cp2 s≤0) ∧
          (∀ s, -1≤cp3 s ∧ cp3 s≤0) ∧ (∑ s, (cp0 s+cp2 s+cp3 s))=0 ∧
          originalSourceGroup5 B2 B3 Qprime cp2 cp3 = originalSourceGroup5 (compound4246 A2) (compound4246 A3) Q (fourWeights246 c2) (fourWeights246 c3) ∧
          (∀ j, κ*mu j ≤ nu j ∧ nu j ≤ 24*mu j) ∧
          nu 3 < nu 4*Qprime^(-delta/8) := by
  have h2 : IsUnit A2 := (Matrix.isUnit_iff_isUnit_det A2).mpr (by rw [h2d]; exact isUnit_one)
  have h3 : IsUnit A3 := (Matrix.isUnit_iff_isUnit_det A3).mpr (by rw [h3d]; exact isUnit_one)
  obtain ⟨C5,ccompound,κ,hC,hc,hk,he,hgap⟩ := source_uniform_gap4246 A2 A3 L h2 h3 hL
  refine ⟨C5,ccompound,κ,hC,hc,hk,he,?_⟩
  intro delta hd
  obtain ⟨T,hT,hs⟩ := hgap delta hd
  refine ⟨T,hT,by positivity,?_⟩
  intro Q hQ c0 c2 c3 hc0 hc2 hc3 hb hTQ hg
  exact ⟨compound_det_one4246 A2 h2d,compound_det_one4246 A3 h3d,
    compound_det_one4246 L hLd,compound_algebraic4246 L hAlg,
    normalized_real_bound4246 c0 hc0,normalized_finite_bounds4246 c2 hc2,
    normalized_finite_bounds4246 c3 hc3,normalized_balance4246 c0 c2 c3 hb,
    powered_group4246 A2 A3 Q c2 c3,
    hs Q hQ c0 c2 c3 (fun i => (hc2 i).2) (fun i => (hc3 i).2) hb hTQ hg⟩

end CompoundFeasibility.Exterior54_246
