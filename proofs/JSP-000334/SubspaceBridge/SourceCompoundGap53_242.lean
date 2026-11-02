import SubspaceBridge.SourceCompoundComparison53_242
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior53_242

theorem triple_gap242 (a : Fin 5 → ℝ) (ha : ∀ i, 0 < a i) (hm : Monotone a)
    (Q delta : ℝ) (hg : a 1 < a 2*Q^(-delta)) :
    tripleProducts242 a 8 < tripleProducts242 a 9*Q^(-delta) := by
  obtain ⟨h8,h9⟩ := tripleProducts_top242 a ha hm
  rw [h8,h9]
  convert mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hg (ha 3)) (ha 4) using 1 <;> ring

theorem ratio_gap3242 (mu nu : Fin 10 → ℝ) (κ Q delta : ℝ) (hk : 0 < κ) (hQ : 1 < Q)
    (hcomp : ∀ j, κ*mu j ≤ nu j ∧ nu j ≤ 6*mu j)
    (hg : mu 8 < mu 9*Q^(-delta)) : nu 8 < (6/κ)*nu 9*Q^(-delta) := by
  calc
    nu 8 ≤ 6*mu 8 := (hcomp 8).2
    _ < 6*(mu 9*Q^(-delta)) := mul_lt_mul_of_pos_left hg (by norm_num)
    _ = (6/κ)*(κ*mu 9)*Q^(-delta) := by field_simp; ring
    _ ≤ (6/κ)*nu 9*Q^(-delta) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcomp 9).1 (by positivity))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _).le

theorem powered_gap_exponent3242 (Q delta : ℝ) (hQ : 1 < Q) :
    Q^(-delta/2) = (Q^3)^(-delta/6) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (zero_lt_one.trans hQ).le]
  congr 1
  ring

theorem source_uniform_gap3242 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ C5 c10 κ : ℝ, 0 < C5 ∧ 0 < c10 ∧ 0 < κ ∧ κ = c10/(10077696*C5^6) ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 < T ∧
        ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ),
          (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 → T < Q →
          sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 1 <
            sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 2*Q^(-delta) →
          (∀ j, κ*tripleProducts242 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j ≤
            compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 j ∧
            compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 j ≤
              6*tripleProducts242 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j) ∧
          compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 8 <
            compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 9*(Q^3)^(-delta/6) := by
  obtain ⟨C5,c10,κ,hC,hc,hk,he,hcompare⟩ := source_uniform_comparison3242 A2 A3 L h2 h3 hL
  refine ⟨C5,c10,κ,hC,hc,hk,he,?_⟩
  intro delta hd
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 (6/κ) delta hd
  refine ⟨T,hT,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb hTQ hg
  have hcq := hcompare Q hQ c0 c2 c3 hc2 hc3 hb
  have hp := sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  have hpair := triple_gap242 _ hp.1 hp.2 Q delta hg
  have hr := ratio_gap3242 _ _ κ Q delta hk hQ hcq hpair
  have hgenuine := absorb_compound_gap42 _ _ (6/κ) Q delta
    ((compoundMinima_pos_mono3242 A2 A3 L hL Q hQ c0 c2 c3).1 9) hQ (hcut Q hTQ) hr
  exact ⟨hcq,by rw [powered_gap_exponent3242 Q delta hQ] at hgenuine; exact hgenuine⟩

theorem source_rank2_compound_gap3242 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1)
    (hL : IsUnit L) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ C5 c10 κ : ℝ, 0 < C5 ∧ 0 < c10 ∧ 0 < κ ∧ κ = c10/(10077696*C5^6) ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 < T ∧ 0 < delta/6 ∧
        ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ),
          (∀ i, |c0 i| ≤ 1) → (∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) →
          (∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 → T < Q →
          sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 1 <
            sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 2*Q^(-delta) →
          let B2 := compound3242 A2
          let B3 := compound3242 A3
          let B0 := compound3242 L
          let Qprime := Q^3
          let cp0 := normalizedWeights3242 c0
          let cp2 := normalizedWeights3242 c2
          let cp3 := normalizedWeights3242 c3
          let nu := sourceMinima10 B2 B3 B0 (compound_real_unit3242 L hL)
            Qprime (powered_gt_one3242 Q hQ) cp0 cp2 cp3
          let mu := tripleProducts242 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3)
          B2.det=1 ∧ B3.det=1 ∧ B0.det=1 ∧
          (∀ s t, IsAlgebraic ℚ (B0 s t)) ∧
          (∀ s, |cp0 s|≤1) ∧ (∀ s, -1≤cp2 s ∧ cp2 s≤0) ∧
          (∀ s, -1≤cp3 s ∧ cp3 s≤0) ∧ (∑ s, (cp0 s+cp2 s+cp3 s))=0 ∧
          originalSourceGroup10 B2 B3 Qprime cp2 cp3 = directGroup3242 A2 A3 Q c2 c3 ∧
          (∀ j, κ*mu j ≤ nu j ∧ nu j ≤ 6*mu j) ∧
          nu 8 < nu 9*Qprime^(-delta/6) := by
  have h2 : IsUnit A2 := (Matrix.isUnit_iff_isUnit_det A2).mpr (by rw [h2d]; exact isUnit_one)
  have h3 : IsUnit A3 := (Matrix.isUnit_iff_isUnit_det A3).mpr (by rw [h3d]; exact isUnit_one)
  obtain ⟨C5,c10,κ,hC,hc,hk,he,hgap⟩ := source_uniform_gap3242 A2 A3 L h2 h3 hL
  refine ⟨C5,c10,κ,hC,hc,hk,he,?_⟩
  intro delta hd
  obtain ⟨T,hT,hs⟩ := hgap delta hd
  refine ⟨T,hT,by positivity,?_⟩
  intro Q hQ c0 c2 c3 hc0 hc2 hc3 hb hTQ hg
  exact ⟨compound_rat_det_one3242 A2 h2d,compound_rat_det_one3242 A3 h3d,
    compound_real_det_one3242 L hLd,compound_algebraic3242 L hAlg,
    normalized_real_bound3242 c0 hc0,normalized_finite_bounds3242 c2 hc2,
    normalized_finite_bounds3242 c3 hc3,normalized_balance3242 c0 c2 c3 hb,
    powered_group3242 A2 A3 Q c2 c3,
    hs Q hQ c0 c2 c3 (fun i => (hc2 i).2) (fun i => (hc3 i).2) hb hTQ hg⟩

end CompoundFeasibility.Exterior53_242
