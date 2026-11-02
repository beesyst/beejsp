import SubspaceBridge.SourceFrameSampling10
import SubspaceBridge.OriginalSpanTransport10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSampling10
open OriginalDeformation10 OriginalSpanTransport10

theorem source_original_deformed_frame10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ),
    (∀ i, |c0 i| ≤ 1) → (∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) →
    (∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 → T < Q →
    ∀ u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3,
    LinearIndependent ℝ (fun i => integerReal (u i : Fin 10 → ℤ)) →
    (∀ i, coordinateGauge10 (originalCoordinates10 L hL Q hQ c0)
      (integerReal (u i : Fin 10 → ℤ)) = sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 i) →
    sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 8 <
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9*Q^(-delta) →
    let lam := sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3
    let d := gapDeformation10 lam
    ∃ (hdp : ∀ i, 0 < d i) (sigma : Equiv.Perm (Fin 10))
      (w : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3),
      LinearIndependent ℝ (fun j => integerReal (w j : Fin 10 → ℤ)) ∧
      (∀ j, coordinateGauge10 (originalDeformedCoordinates10 L hL Q hQ c0 d sigma hdp)
        (integerReal (w j : Fin 10 → ℤ)) =
        originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hdp j) ∧
      minimaFlag10 (fun i => integerReal (u i : Fin 10 → ℤ)) 9 =
        minimaFlag10 (fun i => integerReal (w i : Fin 10 → ℤ)) 9 ∧
      (∀ i, 0 < deformedWidths10 Q c0 d sigma i) ∧
      (∏ i, deformedWidths10 Q c0 d sigma i)*(∏ i, Q^(c2 i+c3 i)) = 1 ∧
      (∀ i, deformedWidths10 Q c0 d sigma i < Q^(5 : ℕ) ∧
        (deformedWidths10 Q c0 d sigma i)⁻¹ < Q^(5 : ℕ)) ∧
      ∀ (j : Fin 9) i, |(L *ᵥ integerReal (w j.castSucc : Fin 10 → ℤ)) i| ≤
        (Q^(5 : ℕ))^(-(delta/60))*deformedWidths10 Q c0 d sigma i := by
  obtain ⟨T,hT,hready⟩ := source_uniform_deformation10 A2 A3 L h2 h3 hL delta hd
  obtain ⟨T',hT',hcut⟩ := compound_gap_cutoff42 1048576 (2*delta) (by positivity)
  refine ⟨max T T',hT.trans_le (le_max_left _ _),?_⟩
  intro Q hQ c0 c2 c3 hc0 hc2 hc3 hb hlarge u hu hatt hgap
  have hr := hready Q hQ c0 c2 c3 hc0 hc2 hc3 hb
    ((le_max_left _ _).trans_lt hlarge) u hu hatt hgap
  rcases hr with ⟨_,_,hdp,_,_,_,sigma,hpos,hbal,hcmp,_,hsep,hshort,_,hsmall,hsizes,_⟩
  obtain ⟨w,hw,hmono,hwatt⟩ := exists_deformed_frame10 A2 A3 L hL Q hQ c0 c2 c3 _ sigma hdp
  have hcutQ : 1048576 < Q^delta := by
    convert hcut Q ((le_max_right _ _).trans_lt hlarge) using 1 <;> congr 1 <;> ring
  have hp := (sourceMinima10_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1
  have hstrict := span_gap_bound10 _ hp Q delta hQ hcutQ hgap
  have hinc : minimaFlag10 (fun i => integerReal (w i : Fin 10 → ℤ)) 9 ≤
      minimaFlag10 (fun i => integerReal (u i : Fin 10 → ℤ)) 9 := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    let i : Fin 10 := Fin.castLE (by omega) j
    by_contra hout
    have hlo := hsep 9 (w i) hout
    have hhi := (hmono (show i ≤ (8 : Fin 10) by change j.val ≤ 8; omega)).trans hshort
    rw [hwatt] at hlo
    exact (not_lt_of_ge hlo) (hhi.trans_lt hstrict)
  have heq := Submodule.eq_of_le_of_finrank_eq hinc
    (by rw [minimaFlag10_finrank _ hw,minimaFlag10_finrank _ hu])
  refine ⟨hdp,sigma,w,hw,hwatt,heq.symm,hpos,hbal,fun i => ⟨(hsizes i).1,(hsizes i).2.1⟩,?_⟩
  intro j i
  have hg := (deformed_gauge_bounds10 L hL Q hQ c0 _ sigma hdp
    (integerReal (w j.castSucc : Fin 10 → ℤ)) _).mp (hwatt j.castSucc).le i
  have hs := (hmono (show j.castSucc ≤ (8 : Fin 10) by change j.val ≤ 8; omega)).trans_lt hsmall
  exact hg.trans (mul_le_mul_of_nonneg_right hs.le (hpos i).le)

end CompoundFeasibility.SourceSampling10
