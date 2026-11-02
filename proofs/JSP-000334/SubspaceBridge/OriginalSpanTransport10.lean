import SubspaceBridge.OriginalDeformation10
open scoped BigOperators Matrix
namespace CompoundFeasibility.OriginalSpanTransport10
open OriginalDeformation10
noncomputable section

theorem span_gap_bound10 (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i)
    (Q delta : ℝ) (hQ : 1 < Q) (hcut : 1048576 < Q^delta)
    (hgap : lam 8 < lam 9 * Q^(-delta)) :
    1024*gapRadius10 lam < gapDeformation10 lam 9*lam 9/1024 := by
  have hq : 0 < Q := zero_lt_one.trans hQ
  have he : Q^(-delta)*Q^delta = 1 := by
    rw [← Real.rpow_add hq,neg_add_cancel,Real.rpow_zero]
  have hmul : lam 8 * Q^delta < lam 9 := by
    have hh := mul_lt_mul_of_pos_right hgap (Real.rpow_pos_of_pos hq delta)
    simpa only [mul_assoc,he,mul_one] using hh
  have hratio : 1048576*lam 8 < lam 9 := by
    have hh := mul_lt_mul_of_pos_left hcut (hp 8)
    nlinarith
  rw [gapDeformation10_last]
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 1024)).mpr
  apply (lt_div_iff₀ (hp 8)).mpr
  have hr := gapRadius10_pos lam hp
  nlinarith [mul_lt_mul_of_pos_left hratio hr]

theorem davenport_same_top_flag10 (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ)) (v : Fin 10 → Fin 10 → ℝ)
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice10Span b)
    (hatt : ∀ i, coordinateGauge10 e (v i) = successiveRadius10 b e i)
    (Q delta : ℝ) (hQ : 1 < Q) (hcut : 1048576 < Q^delta)
    (hgap : successiveRadius10 b e 8 < successiveRadius10 b e 9 * Q^(-delta)) :
    let lam := successiveRadius10 b e
    let d := gapDeformation10 lam
    ∃ (hd : ∀ i, 0 < d i) (sigma : Equiv.Perm (Fin 10)) (w : Fin 10 → Fin 10 → ℝ),
      LinearIndependent ℝ w ∧ (∀ i, w i ∈ lattice10Span b) ∧
      (∀ i, coordinateGauge10 (davenportCoordinates10 e d sigma hd) (w i) =
        successiveRadius10 b (davenportCoordinates10 e d sigma hd) i) ∧
      minimaFlag10 v 9 = minimaFlag10 w 9 := by
  dsimp only
  obtain ⟨_, _, _, hp, hm, _, _⟩ := exists_successive_minima10 b e
  let lam := successiveRadius10 b e
  let d := gapDeformation10 lam
  have hd := gapDeformation10_pos lam hp
  obtain ⟨sigma,hcmp,hvol,hsep⟩ := davenport_lemma10 b e v hv hvL hatt d hd
    (gapDeformation10_product lam hp) (gapDeformation10_antitone lam hp hm)
    (gapDeformation10_scaled lam hp hm)
  obtain ⟨w,hw,hwL,hp',hm',hwatt,_⟩ := exists_successive_minima10 b (davenportCoordinates10 e d sigma hd)
  have hstrict := span_gap_bound10 lam hp Q delta hQ hcut hgap
  have hinc : minimaFlag10 w 9 ≤ minimaFlag10 v 9 := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    let i : Fin 10 := Fin.castLE (by omega) j
    by_contra hout
    have hlo := hsep 9 (w i) (hwL i) hout
    have hhi := (hm' (show i ≤ (8 : Fin 10) by change j.val ≤ 8; omega)).trans (hcmp 8).2
    rw [gapDeformation10_first lam hp 8 le_rfl] at hhi
    rw [hwatt] at hlo
    exact (not_lt_of_ge hlo) (hhi.trans_lt hstrict)
  have heq : minimaFlag10 w 9 = minimaFlag10 v 9 :=
    Submodule.eq_of_le_of_finrank_eq hinc (by rw [minimaFlag10_finrank _ hw, minimaFlag10_finrank _ hv])
  exact ⟨hd,sigma,w,hw,hwL,hwatt,heq.symm⟩

theorem source_original_same_top_flag10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ)
    (u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3)
    (hu : LinearIndependent ℝ (fun i => integerReal (u i : Fin 10 → ℤ)))
    (hatt : ∀ i, coordinateGauge10 (originalCoordinates10 L hL Q hQ c0)
      (integerReal (u i : Fin 10 → ℤ)) = sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 i)
    (delta : ℝ) (hcut : 1048576 < Q^delta)
    (hgap : sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 8 <
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9 * Q^(-delta)) :
    let d := gapDeformation10 (sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3)
    ∃ (hd : ∀ i, 0 < d i) (sigma : Equiv.Perm (Fin 10))
      (w : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3),
      LinearIndependent ℝ (fun i => integerReal (w i : Fin 10 → ℤ)) ∧
      (∀ i, coordinateGauge10 (originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd)
        (integerReal (w i : Fin 10 → ℤ)) =
          originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd i) ∧
      minimaFlag10 (fun i => integerReal (u i : Fin 10 → ℤ)) 9 =
        minimaFlag10 (fun i => integerReal (w i : Fin 10 → ℤ)) 9 := by
  dsimp only
  let b := sourceRealBasis10 A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))
  let e := originalCoordinates10 L hL Q hQ c0
  have hrad (i) : sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 i = successiveRadius10 b e i :=
    sourceMinima10_eq_radius A2 A3 L hL Q hQ c0 c2 c3 i
  have hrfun : sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 = successiveRadius10 b e := funext hrad
  have hmem (z : originalSourceGroup10 A2 A3 Q c2 c3) : integerReal (z : Fin 10 → ℤ) ∈ lattice10Span b := by
    rw [sourceRealBasis10_span]
    exact ⟨z.val,z.property,rfl⟩
  have hgap' : successiveRadius10 b e 8 < successiveRadius10 b e 9 * Q^(-delta) := by
    simpa only [← hrad] using hgap
  obtain ⟨hd,sigma,v,hv,hvL,hva,heq⟩ := davenport_same_top_flag10 b e
    (fun i => integerReal (u i : Fin 10 → ℤ)) hu (fun i => hmem (u i))
    (fun i => (hatt i).trans (hrad i)) Q delta hQ hcut hgap'
  have hvG (i) : ∃ z : originalSourceGroup10 A2 A3 Q c2 c3, integerReal z.val = v i := by
    have hi := hvL i
    rw [sourceRealBasis10_span] at hi
    obtain ⟨z,hz,he⟩ := hi
    exact ⟨⟨z,hz⟩,he⟩
  choose w hw using hvG
  have hfun : (fun i => integerReal (w i : Fin 10 → ℤ)) = v := funext hw
  rw [hrfun]
  refine ⟨hd,sigma,w,hfun.symm ▸ hv,?_,by simpa only [hfun] using heq⟩
  intro i
  change coordinateGauge10 (davenportCoordinates10 e (gapDeformation10 (successiveRadius10 b e)) sigma hd)
    (integerReal (w i : Fin 10 → ℤ)) = _
  rw [hw i]
  exact hva i

end
end CompoundFeasibility.OriginalSpanTransport10
