import SubspaceBridge.SourceCompoundComparison52_239
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.ExteriorGap52_239
open Exterior52_237 Exterior52_238

theorem pair_gap239 (a : Fin 5 → ℝ) (ha : ∀ i, 0 < a i) (hm : Monotone a)
    (Q delta : ℝ) (hg : a 2 < a 3*Q^(-delta)) :
    pairProducts239 a 8 < pairProducts239 a 9*Q^(-delta) := by
  obtain ⟨h8,h9⟩ := pairProducts_top239 a ha hm
  rw [h8,h9]
  convert mul_lt_mul_of_pos_right hg (ha 4) using 1 <;> ring

theorem ratio_gap239 (mu nu : Fin 10 → ℝ) (κ Q delta : ℝ) (hk : 0 < κ) (hQ : 1 < Q)
    (hcomp : ∀ j, κ*mu j ≤ nu j ∧ nu j ≤ 2*mu j)
    (hg : mu 8 < mu 9*Q^(-delta)) : nu 8 < (2/κ)*nu 9*Q^(-delta) := by
  calc
    nu 8 ≤ 2*mu 8 := (hcomp 8).2
    _ < 2*(mu 9*Q^(-delta)) := mul_lt_mul_of_pos_left hg (by norm_num)
    _ = (2/κ)*(κ*mu 9)*Q^(-delta) := by field_simp; ring
    _ ≤ (2/κ)*nu 9*Q^(-delta) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcomp 9).1 (by positivity))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _).le

theorem powered_gap_exponent239 (Q delta : ℝ) (hQ : 1 < Q) :
    Q^(-delta/2) = (Q^2)^(-delta/4) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (zero_lt_one.trans hQ).le]
  congr 1
  ring

theorem source_uniform_gap239 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ C5 c10 κ : ℝ, 0 < C5 ∧ 0 < c10 ∧ 0 < κ ∧ κ = c10/(512*C5^4) ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 < T ∧
        ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ),
          (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 → T < Q →
          sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 2 <
            sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3*Q^(-delta) →
          (∀ j, κ*pairProducts239 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j ≤
            compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 j ∧
            compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 j ≤
              2*pairProducts239 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j) ∧
          compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 8 <
            compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 9*(Q^2)^(-delta/4) := by
  obtain ⟨C5,c10,κ,hC,hc,hk,he,hcompare⟩ := source_uniform_comparison239 A2 A3 L h2 h3 hL
  refine ⟨C5,c10,κ,hC,hc,hk,he,?_⟩
  intro delta hd
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 (2/κ) delta hd
  refine ⟨T,hT,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb hTQ hg
  have hcq := hcompare Q hQ c0 c2 c3 hc2 hc3 hb
  have hp := sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  have hpair := pair_gap239 _ hp.1 hp.2 Q delta hg
  have hr := ratio_gap239 _ _ κ Q delta hk hQ hcq hpair
  have hgenuine := absorb_compound_gap42 _ _ (2/κ) Q delta
    ((compoundMinima_pos_mono239 A2 A3 L hL Q hQ c0 c2 c3).1 9) hQ (hcut Q hTQ) hr
  exact ⟨hcq,by rw [powered_gap_exponent239 Q delta hQ] at hgenuine; exact hgenuine⟩

theorem source_rank3_compound_gap239 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1)
    (hL : IsUnit L) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ C5 c10 κ : ℝ, 0 < C5 ∧ 0 < c10 ∧ 0 < κ ∧ κ = c10/(512*C5^4) ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 < T ∧
        ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ),
          (∀ i, |c0 i| ≤ 1) → (∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) →
          (∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 → T < Q →
          sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 2 <
            sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3*Q^(-delta) →
          let B2 := compound237 A2
          let B3 := compound237 A3
          let B0 := compound237 L
          let Qprime := Q^2
          let cp0 := normalizedWeights238 c0
          let cp2 := normalizedWeights238 c2
          let cp3 := normalizedWeights238 c3
          let nu := sourceMinima10 B2 B3 B0 (compound_unit238 L hL)
            Qprime (powered_gt_one238 Q hQ) cp0 cp2 cp3
          let mu := pairProducts239 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3)
          originalSourceGroup10 B2 B3 Qprime cp2 cp3 = directGroup238 A2 A3 Q c2 c3 ∧
          (∀ j, κ*mu j ≤ nu j ∧ nu j ≤ 2*mu j) ∧
          nu 8 < nu 9*Qprime^(-delta/4) := by
  have h2 : IsUnit A2 := (Matrix.isUnit_iff_isUnit_det A2).mpr (by rw [h2d]; exact isUnit_one)
  have h3 : IsUnit A3 := (Matrix.isUnit_iff_isUnit_det A3).mpr (by rw [h3d]; exact isUnit_one)
  obtain ⟨C5,c10,κ,hC,hc,hk,he,hgap⟩ := source_uniform_gap239 A2 A3 L h2 h3 hL
  refine ⟨C5,c10,κ,hC,hc,hk,he,?_⟩
  intro delta hd
  obtain ⟨T,hT,hs⟩ := hgap delta hd
  refine ⟨T,hT,?_⟩
  intro Q hQ c0 c2 c3 hc0 hc2 hc3 hb hTQ hg
  exact ⟨powered_group238 A2 A3 Q c2 c3,
    hs Q hQ c0 c2 c3 (fun i => (hc2 i).2) (fun i => (hc3 i).2) hb hTQ hg⟩

end CompoundFeasibility.ExteriorGap52_239
