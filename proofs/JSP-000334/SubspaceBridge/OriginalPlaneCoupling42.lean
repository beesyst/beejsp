import SubspaceBridge.SchlickeweiRealCompletion6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalPlaneRecovery42
open SourceWeights

theorem flag_last_eq_firstFive42 (v : Fin 6 → Fin 6 → ℝ) :
    minimaFlag6 v 5 = firstFiveSpan42 v := rfl

theorem separated_frame_span42 (v w : Fin 6 → Fin 6 → ℤ)
    (hv : LinearIndependent ℝ (fun j => integerReal (v j)))
    (hw : LinearIndependent ℝ (fun j => integerReal (w j)))
    (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (a b : ℝ)
    (hsep : ∀ j : Fin 5, integerReal (w j.castSucc) ∉
      minimaFlag6 (fun i => integerReal (v i)) 5 →
      b ≤ coordinateGauge6 e (integerReal (w j.castSucc)))
    (hsmall : ∀ j : Fin 5, coordinateGauge6 e (integerReal (w j.castSucc)) ≤ a)
    (hab : a < b) :
    firstFiveSpan42 (fun j i => (w j i : ℚ)) =
      firstFiveSpan42 (fun j i => (v j i : ℚ)) := by
  have hm (j : Fin 5) : integerReal (w j.castSucc) ∈
      firstFiveSpan42 (fun i => integerReal (v i)) := by
    by_contra hn
    exact (not_le_of_gt ((hsmall j).trans_lt hab)) (hsep j hn)
  have he : firstFiveSpan42 (fun j => integerReal (w j)) =
      firstFiveSpan42 (fun j => integerReal (v j)) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact hm j
    · rw [firstFiveSpan42_finrank _ hw,firstFiveSpan42_finrank _ hv]
  exact integer_firstFive_span_eq42 w v hw hv he

theorem decay_frame_coupling42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (q : ℝ) (hq : 1 < q)
    (c0 c2 c3 : Fin 4 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hb : ∑ i, (c0 i+c2 i+c3 i) = 0) (delta C K : ℝ)
    (hC : 0 < C) (hK : 0 < K) (hCK : C*K < q)
    (hfirst : 1/(C*q^(2 : ℕ)) ≤ directMinima42 A2 A3 L hL q hq c0 c2 c3 0)
    (hlast : directMinima42 A2 A3 L hL q hq c0 c2 c3 5 ≤ K*q^(6 : ℕ))
    (v : Fin 6 → directCompoundGroup42 A2 A3 q c2 c3)
    (hv : LinearIndependent ℝ (fun j => integerReal (v j : Fin 6 → ℤ)))
    (hgap : 4096 * directMinima42 A2 A3 L hL q hq c0 c2 c3 4 <
      directMinima42 A2 A3 L hL q hq c0 c2 c3 5)
    (hdec : sourceDavenportDecay42 A2 A3 L hL q hq c0 c2 c3 delta v) :
    ∃ sigma : Equiv.Perm (Fin 6),
      ∃ hW : ∀ i, 0 < actualWidths A2 A3 L hL q hq c0 c2 c3 sigma i,
      (∀ i, actualWidths A2 A3 L hL q hq c0 c2 c3 sigma i < q^(11 : ℕ) ∧
        (actualWidths A2 A3 L hL q hq c0 c2 c3 sigma i)⁻¹ < q^(11 : ℕ)) ∧
      (∏ i, actualWidths A2 A3 L hL q hq c0 c2 c3 sigma i *
        (q^(11 : ℕ))^(finiteWeight c2 i)*(q^(11 : ℕ))^(finiteWeight c3 i)) = 1 ∧
      ∃ w : Fin 6 → directCompoundGroup42 A2 A3 q c2 c3,
        LinearIndependent ℝ (fun j => integerReal (w j : Fin 6 → ℤ)) ∧
        (∀ j, coordinateGauge6 (weightedCoordinates6 (compoundFormEquiv42 L hL)
          (actualWidths A2 A3 L hL q hq c0 c2 c3 sigma) hW)
          (integerReal (w j : Fin 6 → ℤ)) =
          successiveRadius6 (directRealBasis42 A2 A3 (q^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11))
            (weightedCoordinates6 (compoundFormEquiv42 L hL)
              (actualWidths A2 A3 L hL q hq c0 c2 c3 sigma) hW) j) ∧
        successiveRadius6 (directRealBasis42 A2 A3 (q^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11))
          (weightedCoordinates6 (compoundFormEquiv42 L hL)
            (actualWidths A2 A3 L hL q hq c0 c2 c3 sigma) hW) 4 <
              (q^(11 : ℕ))^(-(delta/264)) ∧
        firstFiveSpan42 (fun j i => ((w j : Fin 6 → ℤ) i : ℚ)) =
          firstFiveSpan42 (fun j i => ((v j : Fin 6 → ℤ) i : ℚ)) := by
  let rho := directMinima42 A2 A3 L hL q hq c0 c2 c3
  let d := gapDeformation6 rho
  obtain ⟨hp,hm⟩ := directMinima42_pos_mono A2 A3 L hL q hq c0 c2 c3
  obtain ⟨hd,hprod,_,_,sigma,hbounds,_,hsep,hupper,hsmall,w,hwi,_,hwm,hwatt⟩ := hdec
  have hw := davenportWidths42_bounds q hq c0 hc0 rho hp hm C K hC hK hfirst hlast sigma
  have hW : ∀ i, 0 < actualWidths A2 A3 L hL q hq c0 c2 c3 sigma i := fun i => (hw i).1
  let e := weightedCoordinates6 (compoundFormEquiv42 L hL)
    (actualWidths A2 A3 L hL q hq c0 c2 c3 sigma) hW
  have he : e = davenportCoordinates6 (compoundCoordinates42 L hL q hq c0) d sigma hd :=
    davenportWidths42_coordinates L hL q hq c0 d sigma hd hW
  have hatt (j : Fin 6) : coordinateGauge6 e (integerReal (w j : Fin 6 → ℤ)) =
      successiveRadius6 (directRealBasis42 A2 A3 (q^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11)) e j := by
    calc
      _ = coordinateGauge6 (davenportCoordinates6 (compoundCoordinates42 L hL q hq c0) d sigma hd)
          (integerReal (w j : Fin 6 → ℤ)) := congrArg (fun E => coordinateGauge6 E (integerReal (w j : Fin 6 → ℤ))) he
      _ = _ := hwatt j
      _ = _ := (davenport_rescaled_minima42 A2 A3 L hL q hq c0 c2 c3 d sigma hd hW j).symm
  have hmargin : 64*gapRadius6 rho < d 5*rho 5/64 := by
    change 64*gapRadius6 rho < (gapRadius6 rho/rho 4)*rho 5/64
    calc
      _ = (gapRadius6 rho / rho 4) * (4096 * rho 4) / 64 := by
        have h4 : rho 4 ≠ 0 := ne_of_gt (hp 4)
        have hc :
            (gapRadius6 rho / rho 4) * rho 4 = gapRadius6 rho := by
          field_simp [h4]
        calc
          64 * gapRadius6 rho =
              ((gapRadius6 rho / rho 4) * rho 4) * 64 := by
            rw [hc]
            ring
          _ = (gapRadius6 rho / rho 4) * (4096 * rho 4) / 64 := by
            ring
      _ < _ := div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_left hgap (div_pos (gapRadius6_pos rho hp) (hp 4))) (by norm_num)
  have hspan := separated_frame_span42 (fun j => (v j : Fin 6 → ℤ))
    (fun j => (w j : Fin 6 → ℤ)) hv hwi e (64*gapRadius6 rho) (d 5*rho 5/64)
    (fun j hj => by rw [he]; exact hsep 5 (w j.castSucc) hj)
    (fun j => by
      rw [he,hwatt]
      exact (hwm (show j.castSucc ≤ (4 : Fin 6) by change j.val ≤ 4; omega)).trans hupper)
    hmargin
  refine ⟨sigma,hW,?_,?_,w,hwi,hatt,?_,hspan⟩
  · intro i
    have hbnd : C*K*q^(10 : ℕ) < q^(11 : ℕ) := by
      convert mul_lt_mul_of_pos_right hCK (pow_pos (zero_lt_one.trans hq) 10) using 1 <;> ring
    exact ⟨((hw i).2.1).trans_lt hbnd,((hw i).2.2).trans_lt hbnd⟩
  · exact davenportWidths42_normalization q (zero_lt_one.trans hq) c0 c2 c3 d sigma hb hprod
  · change successiveRadius6 _ e 4 < _
    rw [← hatt 4,he,hwatt]
    exact davenport_rescaled_small42 q delta _ (zero_lt_one.trans hq) hsmall

theorem source_coupling_cutoff42 (delta C K : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ q : ℝ, T < q →
      4096 < q^(delta/2) ∧ C*K < q ∧ 1 < q := by
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 4096 delta hd
  refine ⟨max T (C*K),hT.trans_le (le_max_left _ _),?_⟩
  intro q hq
  exact ⟨hcut q ((le_max_left _ _).trans_lt hq),
    (le_max_right _ _).trans_lt hq,hT.trans ((le_max_left _ _).trans_lt hq)⟩

theorem source_decay_frame_coupling42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (q : ℝ) (hq : 1 < q)
    (c0 c2 c3 : Fin 4 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hb : ∑ i, (c0 i+c2 i+c3 i) = 0) (delta C K : ℝ)
    (hC : 0 < C) (hK : 0 < K) (hCK : C*K < q)
    (hfirst : 1/(C*q^(2 : ℕ)) ≤ directMinima42 A2 A3 L hL q hq c0 c2 c3 0)
    (hlast : directMinima42 A2 A3 L hL q hq c0 c2 c3 5 ≤ K*q^(6 : ℕ))
    (v : Fin 6 → directCompoundGroup42 A2 A3 q c2 c3)
    (u : Fin 4 → originalSourceGroup4 A2 A3 q c2 c3) (kappa : ℝ)
    (hs : sourceHyperplane42 A2 A3 L hL q hq c0 c2 c3 kappa u v)
    (hcut : 4096 < q^(delta/2))
    (hgap : directMinima42 A2 A3 L hL q hq c0 c2 c3 4 <
      directMinima42 A2 A3 L hL q hq c0 c2 c3 5 * q^(-delta/2))
    (hdec : sourceDavenportDecay42 A2 A3 L hL q hq c0 c2 c3 delta v) :
    ∃ sigma : Equiv.Perm (Fin 6),
      ∃ hW : ∀ i, 0 < actualWidths A2 A3 L hL q hq c0 c2 c3 sigma i,
      (∀ i, actualWidths A2 A3 L hL q hq c0 c2 c3 sigma i < q^(11 : ℕ) ∧
        (actualWidths A2 A3 L hL q hq c0 c2 c3 sigma i)⁻¹ < q^(11 : ℕ)) ∧
      (∏ i, actualWidths A2 A3 L hL q hq c0 c2 c3 sigma i *
        (q^(11 : ℕ))^(finiteWeight c2 i)*(q^(11 : ℕ))^(finiteWeight c3 i)) = 1 ∧
      ∃ w : Fin 6 → directCompoundGroup42 A2 A3 q c2 c3,
        LinearIndependent ℝ (fun j => integerReal (w j : Fin 6 → ℤ)) ∧
        (∀ j, coordinateGauge6 (weightedCoordinates6 (compoundFormEquiv42 L hL)
          (actualWidths A2 A3 L hL q hq c0 c2 c3 sigma) hW)
          (integerReal (w j : Fin 6 → ℤ)) =
          successiveRadius6 (directRealBasis42 A2 A3 (q^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11))
            (weightedCoordinates6 (compoundFormEquiv42 L hL)
              (actualWidths A2 A3 L hL q hq c0 c2 c3 sigma) hW) j) ∧
        successiveRadius6 (directRealBasis42 A2 A3 (q^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11))
          (weightedCoordinates6 (compoundFormEquiv42 L hL)
            (actualWidths A2 A3 L hL q hq c0 c2 c3 sigma) hW) 4 <
              (q^(11 : ℕ))^(-(delta/264)) ∧
        firstFiveSpan42 (fun j i => ((w j : Fin 6 → ℤ) i : ℚ)) =
          firstFiveSpan42 (fun j i => (orderedWedges42 (fun k => (u k : Fin 4 → ℤ))
            (sourceMinima4 A2 A3 L hL q hq c0 c2 c3) j i : ℚ)) := by
  obtain ⟨_,_,hv,_,_,_,_,_,_,_,_,_,_,_,_,he,_⟩ := hs
  have hg := gap_margin42 4096 _ _ q delta (by norm_num)
    ((directMinima42_pos_mono A2 A3 L hL q hq c0 c2 c3).1 5) hq hcut hgap
  obtain ⟨sigma,hW,hbounds,hprod,w,hwi,hatt,hsmall,hspan⟩ :=
    decay_frame_coupling42 A2 A3 L hL q hq c0 c2 c3 hc0 hb delta C K
      hC hK hCK hfirst hlast v hv hg hdec
  exact ⟨sigma,hW,hbounds,hprod,w,hwi,hatt,hsmall,hspan.trans he.symm⟩

open SourceReadiness6
open SourceNormalIndex SourceWeights Auxiliary6 SourceMultiblock SourceMixed6 SourceHeightBounds6
open SourceNormalHeight SourceProper6 SourceMinorIntegration6 SourceLocalUpperIntegration6 SourceFieldLower6
open SourceFieldLowerIntegration6 SourceHeightUpper6 SourceHeightEnvelopes6
open Auxiliary6.SourceExpansion Auxiliary6.SourceBalance Auxiliary6.SourceVanishing
open Auxiliary6.SourceGrid Auxiliary6.SourceEvaluation

open SourceHeightIntegration6 SourceBlocks SourceLocalUpper6


theorem readiness_of_selected_frames42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c0 c2 c3 : Fin 4 → ℝ) (delta4 delta : ℝ) (V : Set ℝ)
    (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q)
    (hdelta : delta = selectionSlack delta4) (hd : 0 < delta) (hd1 : delta < 1)
    (c : Fin 3 → Fin 6 → ℝ) (hc : ∀ tau i, |c tau i| ≤ 1)
    (hbal : (∑ tau, ∑ i, c tau i) = 0)
    (hfin : ∀ i, c 1 i = finiteWeight c2 i ∧ c 2 i = finiteWeight c3 i)
    (sigma : V → Equiv.Perm (Fin 6))
    (hW : ∀ (q : V) i, 0 < actualWidths A2 A3 L (sourceUnit42 L hL) q.val
      (hQV q.val q.property) c0 c2 c3 (sigma q) i)
    (w : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3)
    (q0 : V) (hanchor : ∀ i, c 0 i = logWeight (q0.val^(11 : ℕ))
      (actualWidths A2 A3 L (sourceUnit42 L hL) q0.val
        (hQV q0.val q0.property) c0 c2 c3 (sigma q0) i))
    (hw : ∀ q, sourceFrames6 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 V hQV
      delta c sigma hW w q) :
    ∃ R : SourceReadiness42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V hQV,
      R.w = w ∧ R.sigma = sigma ∧ R.c = c := by
  obtain ⟨K,hK,hmem,D,E,hD,hE,haux⟩ :=
    source_auxiliary6_grid_vanishing A2 A3 L h2 h3 hL hAlg
  letI : FiniteDimensional ℚ K := hK
  have hex (q : V) := primitive_normal6 (fun j => (w q j : Fin 6 → ℤ))
    ((integer6_independent_iff42 _).mpr (hw q).1)
  choose M a hM ha hspan hann hker using hex
  have hn : ∀ q, sourceNormals6 A2 A3 c2 c3 V w M a q := by
    intro q
    exact ⟨hM q,ha q,hspan q,hann q,hker q,
      real_normal_kernel6 _ (hw q).1 _ (hM q) (hann q)⟩
  have hminor (q : V) : minorNormalization6 (fun j => (w q j : Fin 6 → ℤ)) (M q) (a q) ∧
      actualTransformedCofactors6 A2 A3 L (fun j => (w q j : Fin 6 → ℤ)) (M q) (a q) := by
    have hv := (integer6_independent_iff42 (fun j => (w q j : Fin 6 → ℤ))).mpr (hw q).1
    exact ⟨primitive_minor_data6 _ hv (M q) (a q) (hM q) (ha q) (hann q),
      actual_primitive_transformed6 A2 A3 L _ hv (M q) (a q) (hM q) (ha q) (hann q)⟩
  have hu (q : V) (s : MixedIndex6) (hs : s ∈ admissibleMixed6 c (delta/2)) :
      actualNormProduct6 A2 A3 L (M q) s ≤ 120*(q.val^(11 : ℕ))^(-delta/8) := by
    rcases hw q with ⟨_,_,_,_,hR,hp2,hp3⟩
    exact (actual_mixed_upper6 A2 A3 L (fun j => (w q j : Fin 6 → ℤ)) (M q) (a q)
      (hminor q).1 (hminor q).2 (q.val^(11 : ℕ)) delta
      (one_lt_pow₀ (hQV q.val q.property) (by decide)) hd c hbal hR hp2 hp3 s hs).2.le
  have hb := finite_mixed_reduction6 A2 A3 L V M c (delta/2)
  obtain ⟨C,hC,hlower⟩ := actual_mixed_field_lower6 K A2 A3 L hmem
  have he := source_height_branch6 A2 A3 L (sourceUnit42 L hL) V hQV delta hd c hc
    (fun q j => (w q j : Fin 6 → ℤ)) M a (fun q => (hminor q).1)
    (fun q => (hw q).2.2.2.2.1) hu hb K C hC (fun q s hs => (hlower (M q) s hs).1)
  let R : SourceReadiness42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V hQV := {
    unbounded := hV, delta := delta, delta_eq := hdelta, delta_pos := hd, delta_lt_one := hd1,
    c := c, weights_bounded := hc, weights_balance := hbal, finite_weights := hfin,
    sigma := sigma, widths_pos := hW, w := w, q0 := q0, anchor := hanchor, frames := hw,
    M := M, a := a, normals := hn, minors := hminor, upper := hu, mixed := hb,
    K := K, finite_dimensional := hK, hmem := hmem,
    cofactors_mem := actual_cofactor_mem6 K A2 A3 L hmem,
    C := C, C_pos := hC, lower := fun q s hs => hlower (M q) s hs, envelopes := he,
    D := D, E := E, D_ge_one := hD, E_ge_one := hE, auxiliary := haux }
  exact ⟨R,rfl,rfl,rfl⟩

theorem select_coupled_readiness42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c0 c2 c3 : Fin 4 → ℝ)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (delta4 : ℝ) (hd : 0 < delta4) (U : Set ℝ) (hU : ¬ BddAbove U)
    (hQU : ∀ q ∈ U, 1 < q) (sigma : U → Equiv.Perm (Fin 6))
    (hW : ∀ (q : U) i, 0 < actualWidths A2 A3 L (sourceUnit42 L hL) q.val
      (hQU q.val q.property) c0 c2 c3 (sigma q) i)
    (hbounds : ∀ (q : U) i,
      actualWidths A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val q.property) c0 c2 c3 (sigma q) i < q.val^(11 : ℕ) ∧
      (actualWidths A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val q.property) c0 c2 c3 (sigma q) i)⁻¹ < q.val^(11 : ℕ))
    (hprod : ∀ q : U, (∏ i, actualWidths A2 A3 L (sourceUnit42 L hL) q.val
      (hQU q.val q.property) c0 c2 c3 (sigma q) i *
        (q.val^(11 : ℕ))^(finiteWeight c2 i)*(q.val^(11 : ℕ))^(finiteWeight c3 i)) = 1)
    (w : (q : U) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3)
    (hwi : ∀ q : U, LinearIndependent ℝ (fun j => integerReal (w q j : Fin 6 → ℤ)))
    (hatt : ∀ (q : U) j,
      coordinateGauge6 (weightedCoordinates6 (compoundFormEquiv42 L (sourceUnit42 L hL))
        (actualWidths A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val q.property) c0 c2 c3 (sigma q)) (hW q))
          (integerReal (w q j : Fin 6 → ℤ)) =
      successiveRadius6 (directRealBasis42 A2 A3 (q.val^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11))
        (weightedCoordinates6 (compoundFormEquiv42 L (sourceUnit42 L hL))
          (actualWidths A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val q.property) c0 c2 c3 (sigma q)) (hW q)) j)
    (hsmall : ∀ q : U,
      successiveRadius6 (directRealBasis42 A2 A3 (q.val^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11))
        (weightedCoordinates6 (compoundFormEquiv42 L (sourceUnit42 L hL))
          (actualWidths A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val q.property) c0 c2 c3 (sigma q)) (hW q)) 4 <
          (q.val^(11 : ℕ))^(-(delta4/264))) :
    ∃ (V : Set ℝ) (hVU : V ⊆ U), ¬ BddAbove V ∧
      fixedSourceWeights42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V
        (fun q hq => hQU q (hVU hq)) ∧
      ∃ R : SourceReadiness42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V
        (fun q hq => hQU q (hVU hq)),
        R.w = (fun (q : V) (j : Fin 6) => w (⟨q.val,hVU q.property⟩ : U) j) ∧
        R.sigma = (fun (q : V) => sigma (⟨q.val,hVU q.property⟩ : U)) ∧
        ∃ q0 : V, R.c = fixedWeights
          (fun i => logWeight (q0.val^(11 : ℕ)) (actualWidths A2 A3 L (sourceUnit42 L hL)
            q0.val (hQU q0.val (hVU q0.property)) c0 c2 c3 (sigma ⟨q0.val,hVU q0.property⟩) i))
          (finiteWeight c2) (finiteWeight c3) := by
  classical
  let W (q : U) := actualWidths A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val q.property) c0 c2 c3 (sigma q)
  have hqp (q : U) : 1<q.val^(11 : ℕ) := one_lt_pow₀ (hQU q.val q.property) (by decide)
  have hab (q : U) (i : Fin 6) : -1<logWeight (q.val^(11 : ℕ)) (W q i) ∧
      logWeight (q.val^(11 : ℕ)) (W q i)<1 :=
    logWeight_bounds _ _ (hqp q) (hW q i) (hbounds q i).1 (hbounds q i).2
  let alpha : ℝ → Fin 6 → ℝ := fun q => if h : q ∈ U then
    fun i => logWeight (q^(11 : ℕ)) (W ⟨q,h⟩ i) else 0
  have hb : ∀ q ∈ U,∀ i,|alpha q i|≤1 := by
    intro q hq i
    simp only [alpha,dif_pos hq]
    exact abs_le.mpr ⟨(hab ⟨q,hq⟩ i).1.le,(hab ⟨q,hq⟩ i).2.le⟩
  let eps := selectionSlack delta4
  have hs := selectionSlack_bounds delta4 hd
  obtain ⟨V,hVU,hVb,q0,hq0,hclose⟩ := select_unbounded_weights U hU alpha hb eps hs.1
  let lift : V → U := fun q => ⟨q.val,hVU q.property⟩
  let u0 : U := ⟨q0,hVU hq0⟩
  let a0 : Fin 6 → ℝ := fun i => logWeight (q0^(11 : ℕ)) (W u0 i)
  let c := fixedWeights a0 (finiteWeight c2) (finiteWeight c3)
  have hc := fixedWeights_bounds_balance a0 (finiteWeight c2) (finiteWeight c3)
    (hab u0) (finiteWeight_bounds c2 hc2) (finiteWeight_bounds c3 hc3)
    (logWeight_balance _ (hqp u0) (W u0) (finiteWeight c2) (finiteWeight c3) (hW u0) (hprod u0))
  have happrox (q : V) (i : Fin 6) : |logWeight (q.val^(11 : ℕ)) (W (lift q) i)-a0 i|<eps := by
    have hh := hclose q.val q.property i
    simpa only [alpha,dif_pos (hVU q.property),dif_pos (hVU hq0),lift,u0,a0] using hh
  let hQV : ∀ q ∈ V, 1 < q := fun q hq => hQU q (hVU hq)
  let sigma' : V → Equiv.Perm (Fin 6) := fun q => sigma (lift q)
  let hW' := fun (q : V) i => hW (lift q) i
  let w' : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3 := fun q j => w (lift q) j
  have hframes : ∀ q : V, sourceFrames6 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 V hQV
      eps c sigma' hW' w' q := by
    intro q
    let b := directRealBasis42 A2 A3 (q.val^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11)
    let e := weightedCoordinates6 (compoundFormEquiv42 L (sourceUnit42 L hL)) (W (lift q)) (hW (lift q))
    have hiQ : LinearIndependent ℚ (fun j i => ((w (lift q) j : Fin 6 → ℤ) i : ℚ)) :=
      (integer6_independent_iff42 _).mpr (hwi (lift q))
    have hm : Monotone (successiveRadius6 b e) := (exists_successive_minima6 b e).choose_spec.2.2.2.1
    refine ⟨hwi (lift q),hiQ.comp Fin.castSucc (Fin.castSucc_injective 5),
      davenport_rescaled_group42 A2 A3 q.val c2 c3,hatt (lift q),?_,?_,?_⟩
    · intro j i
      have hg : coordinateGauge6 e (integerReal (w (lift q) j.castSucc : Fin 6 → ℤ))≤successiveRadius6 b e 4 := by
        have heq : coordinateGauge6 e (integerReal (w (lift q) j.castSucc : Fin 6 → ℤ))=
            successiveRadius6 b e j.castSucc := hatt (lift q) j.castSucc
        exact heq.le.trans (hm (show j.castSucc ≤ (4 : Fin 6) from by
          change j.val ≤ 4
          have hj := j.isLt
          omega))
      have hg' := weighted_form_bound (compoundFormEquiv42 L (sourceUnit42 L hL)) (W (lift q)) (hW (lift q))
        (integerReal (w (lift q) j.castSucc : Fin 6 → ℤ)) _ hg i
      exact real_form_slack (q.val^(11 : ℕ)) (W (lift q) i) (a0 i) eps delta4 eps
        (successiveRadius6 b e 4) _ (hqp (lift q)) (hW (lift q) i)
        (logWeight_power _ _ (hqp (lift q)) (hW (lift q) i)) (happrox q i) hs.2.2 (hsmall (lift q)) hg'
    · intro j i
      exact (finite_form_bounds A2 A3 q.val (hQU q.val (hVU q.property)) c2 c3
        (fun i => (hc2 i).2) (fun i => (hc3 i).2) (w (lift q) j.castSucc)).1 i
    · intro j i
      exact (finite_form_bounds A2 A3 q.val (hQU q.val (hVU q.property)) c2 c3
        (fun i => (hc2 i).2) (fun i => (hc3 i).2) (w (lift q) j.castSucc)).2 i
  have hfin : ∀ i, c 1 i = finiteWeight c2 i ∧ c 2 i = finiteWeight c3 i := by
    intro i
    constructor <;> rfl
  have hanchor : ∀ i, c 0 i = logWeight (q0^(11 : ℕ)) (W u0 i) := fun i => rfl
  have hfixed : fixedSourceWeights42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V hQV := by
    refine ⟨power11_unbounded V hVb,eps,eps,rfl,rfl,hs.1,hs.1,hs.2.1,hs.2.2,
      c,hc.1,hc.2,hfin,sigma',hW',w',⟨q0,hq0⟩,hanchor,?_⟩
    intro q
    obtain ⟨hli,hlq,hgroup,hatt',h0,h2',h3'⟩ := hframes q
    refine ⟨hab (lift q),?_,happrox q,hprod (lift q),hli,hlq,hgroup,hatt',hsmall (lift q),h0,h2',h3'⟩
    intro i
    exact logWeight_power _ _ (hqp (lift q)) (hW (lift q) i)
  obtain ⟨R,hRw,hRs,hRc⟩ := readiness_of_selected_frames42 A2 A3 L h2 h3 hL hAlg
    c0 c2 c3 delta4 eps V hVb hQV rfl hs.1 hs.2.1 c hc.1 hc.2 hfin
    sigma' hW' w' ⟨q0,hq0⟩ hanchor hframes
  exact ⟨V,hVU,hVb,hfixed,R,hRw,hRs,⟨q0,hq0⟩,hRc⟩

theorem source_original_coupled_readiness42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (delta4 : ℝ) (hd : 0 < delta4) (c0 c2 c3 : Fin 4 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hbalance : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ q ∈ U, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ U),
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQU q hq) c0 c2 c3 1 <
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQU q hq) c0 c2 c3 2 * q^(-delta4)) :
    ∃ (V : Set ℝ) (hVU : V ⊆ U)
      (R : SourceReadiness42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V
        (fun q hq => hQU q (hVU hq)))
      (u : (q : V) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3)
      (v : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3)
      (sigma : V → Equiv.Perm (Fin 6))
      (w : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3)
      (kappa : ℝ),
      ¬ BddAbove V ∧
      fixedSourceWeights42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V
        (fun q hq => hQU q (hVU hq)) ∧
      R.w = w ∧ R.sigma = sigma ∧
      (∃ q0 : V, R.c = fixedWeights
        (fun i => logWeight (q0.val^(11 : ℕ)) (actualWidths A2 A3 L (sourceUnit42 L hL)
          q0.val (hQU q0.val (hVU q0.property)) c0 c2 c3 (sigma q0) i))
        (finiteWeight c2) (finiteWeight c3)) ∧
      ∀ q : V,
        sourceHyperplane42 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property))
          c0 c2 c3 kappa (u q) (v q) ∧
        rationalDualLine42 (fun i => (u q i : Fin 4 → ℤ)) (fun j => (v q j : Fin 6 → ℤ))
          (sourceMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c0 c2 c3) ∧
        (firstFiveSpan42 (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) =
          firstFiveSpan42 (fun j i => (orderedWedges42 (fun k => (u q k : Fin 4 → ℤ))
            (sourceMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c0 c2 c3) j i : ℚ))) ∧
        (firstFiveSpan42 (fun j i => ((w q j : Fin 6 → ℤ) i : ℚ)) =
          firstFiveSpan42 (fun j i => ((v q j : Fin 6 → ℤ) i : ℚ))) ∧
        orderedWedges42 (fun k => (u q k : Fin 4 → ℤ))
          (sourceMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c0 c2 c3) 5 =
            wedge (u q 2 : Fin 4 → ℤ) (u q 3 : Fin 4 → ℤ) := by
  classical
  obtain ⟨_,_,_,_,kappa,C4,C,K,T,_,_,hC,hK,_,_,hfamily⟩ :=
    source_compound_unbounded_analytic_ready42 A2 A3 L h2 h3 hL hAlg delta4 hd
  obtain ⟨_,_,_,_,hF⟩ := hfamily c0 c2 c3 hc0 hc2 hc3 hbalance
  obtain ⟨U0,hU0U,hU0b,_,u0,v0,hfamily0⟩ := hF U hU hQU hgap
  obtain ⟨B,hB,hcut⟩ := source_coupling_cutoff42 delta4 C K hd
  let S := {q : ℝ | q ∈ U0 ∧ B < q}
  have hS : ¬ BddAbove S := JSP000334.sourceDual_unbounded_tail3 U0 hU0b B
  let hSU : S ⊆ U := fun q hq => hU0U hq.1
  let hQS : ∀ q ∈ S, 1 < q := fun q hq => hQU q (hSU hq)
  let lift0 : S → U0 := fun q => ⟨q.val,q.property.1⟩
  let uS := fun (q : S) => u0 (lift0 q)
  let vS := fun (q : S) => v0 (lift0 q)
  have hchosen (q : S) := by
    obtain ⟨_,hH,_,hg,_,_,_,hdec,hfirst,hlast,_,_⟩ := hfamily0 (lift0 q)
    exact source_decay_frame_coupling42 A2 A3 L (sourceUnit42 L hL) q.val (hQS q.val q.property)
      c0 c2 c3 hc0 hbalance delta4 C K hC hK (hcut q.val q.property.2).2.1
      hfirst hlast (vS q) (uS q) kappa hH (hcut q.val q.property.2).1 hg hdec
  choose sigma hW hbounds hprod w hwi hatt hsmall hcouple using hchosen
  obtain ⟨V,hVS,hV,hfixed,R,hRw,hRs,q0,hRc⟩ := select_coupled_readiness42 A2 A3 L h2 h3 hL hAlg
    c0 c2 c3 hc2 hc3 delta4 hd S hS hQS sigma hW hbounds hprod w hwi hatt hsmall
  let hVU : V ⊆ U := fun q hq => hSU (hVS hq)
  let lift : V → S := fun q => ⟨q.val,hVS q.property⟩
  let u := fun (q : V) => uS (lift q)
  let v := fun (q : V) => vS (lift q)
  let sigma' := fun (q : V) => sigma (lift q)
  let w' : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3 := fun q => w (lift q)
  refine ⟨V,hVU,R,u,v,sigma',w',kappa,hV,hfixed,hRw,hRs,⟨q0,hRc⟩,?_⟩
  intro q
  obtain ⟨_,hH,hdual,_,_,_,_,_,_,_,_,_⟩ := hfamily0 (lift0 (lift q))
  have hR : R.w q = w (lift q) := congrFun hRw q
  have hspan : firstFiveSpan42 (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) =
      firstFiveSpan42 (fun j i => (orderedWedges42 (fun k => (u q k : Fin 4 → ℤ))
        (sourceMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c0 c2 c3) j i : ℚ)) := by
    rw [hR]
    exact hcouple (lift q)
  have hHkeep := hH
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,he,hlast⟩ := hH
  exact ⟨hHkeep,hdual,hspan,(hcouple (lift q)).trans he,hlast⟩

end CompoundFeasibility.OriginalPlaneRecovery42
