import SubspaceBridge.CofactorSourceBounds3
open scoped BigOperators Matrix
namespace JSP000334
noncomputable section

theorem cofactor_original_normal_height3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (S : Set (Fin 3 → Fin 3)) (_hS : S.Nonempty) :
    ∀ (Q : ℝ) (hQ : 1 < Q), max 108 ((18 : ℝ)^(16/delta)) < Q →
      ∀ c₀ c₂ c₃ : Fin 3 → ℝ,
        (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) →
        (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) →
        (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        (∀ s ∈ S, -(3 * delta) / 4 ≤ c₀ (s 0) + c₂ (s 1) + c₃ (s 2)) →
        ∀ (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃),
          lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3 →
          LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) →
          (∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
            (integerTripleReal3 (u j : IntegerTriple)) =
              successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j) →
          dualFrameRelativeIndex3 (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃) u ≤ 6 →
          successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) 1 < Q ^ (-delta) →
          (∃ s ∈ S, cofactorSelectedProduct3 k₀ k₂ k₃ s
            (dualFrameVector3 (fun j => (u j : IntegerTriple)) 2) ≠ 0) →
          ∃ (z m : IntegerTriple) (g : ℤ),
            g ≠ 0 ∧ m ≠ 0 ∧
            (∀ i, ((dualFrameRelativeIndex3 (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃) u *
              (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
                dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i = (z i : ℚ)) ∧
            (∀ i, z i = g * m i) ∧ Ideal.span (Set.range m) = ⊤ ∧
            Finset.univ.gcd (fun i => (m i).natAbs) = 1 ∧
            (∃ r : ℚ, r ≠ 0 ∧ (fun i => (m i : ℚ)) =
              r • dualFrameVector3 (fun j => (u j : IntegerTriple)) 2) ∧
            Submodule.span ℚ ({fun i => (m i : ℚ)} : Set (Fin 3 → ℚ)) =
              Submodule.span ℚ {dualFrameVector3 (fun j => (u j : IntegerTriple)) 2} ∧
            (∀ j : Fin 2, (∑ i : Fin 3, m i * ((u j.castSucc : IntegerTriple) i)) = 0) ∧
            dualFrameRelativeIndex3 (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃) u ≤ 6 ∧
            Q ^ (delta/16) ≤ (rothKernelRowHeight m : ℝ) ∧ (rothKernelRowHeight m : ℝ) ≤ Q ^ (9 : ℝ) := by
  intro Q hQ hcut c₀ c₂ c₃ hc₀ hc₂' hc₃' hbalance hweights B u hB hu hatt hJ hsmall hnonzero
  have hc₂ := fun i => (hc₂' i).2
  have hc₃ := fun i => (hc₃' i).2
  have hp := lt_trans zero_lt_one hQ
  let G := cofactorSourceLattice3 k₂ k₃ Q c₂ c₃
  obtain ⟨c⟩ : Nonempty (Basis (Fin 3) ℤ G) := mixedCongruence3_has_basis _ _ _ _
  have hD : (0 : ℝ) < G.index := by
    rw [(cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1]
    unfold qCongruenceIndex3
    positivity
  have hDnat : G.index ≠ 0 := by exact_mod_cast hD.ne'
  have ha (i : Fin 3) : 0 < Q ^ c₀ i := Real.rpow_pos_of_pos hp _
  have hP : 0 < ∏ i : Fin 3, Q ^ c₀ i := Finset.prod_pos (fun i _ => ha i)
  have hcov : ZLattice.covolume (lattice3 B) = (G.index : ℝ) := by
    rw [hB, (cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1]
    exact (cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.2
  have hvol : MeasureTheory.volume.real (parallelepipedBody3 (cofactorSourceCoordinates3 k₀ Q c₀ hQ)) =
      8 * ∏ i : Fin 3, Q ^ c₀ i := by
    rw [← cofactorSourceBody3_eq_parallelepiped k₀ Q c₀ hQ]
    exact cofactorSourceBody3_volume k₀ Q c₀ hQ
  have hprod : (∏ j, successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j) *
      (∏ i : Fin 3, Q ^ c₀ i) ≤ (G.index : ℝ) := by
    have h := successive_minima3_parallelepiped_volume_upper B (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
    rw [hvol, hcov] at h
    nlinarith
  obtain ⟨_, _, _, hs, _, _⟩ := exists_successive_minima3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
  have hpoint : ∀ j i, |∑ l : Fin 3, cofactorRealMatrix3 k₀ i l *
      ((u j : IntegerTriple) l : ℝ)| ≤
      successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j * Q ^ c₀ i := by
    intro j i
    have h := cofactorSource_arch_bound k₀ Q c₀ hQ (integerTripleReal3 (u j : IntegerTriple)) i
    rw [hatt] at h
    exact h
  have hreal (i : Fin 3) := dualFrame3_source_real_bound G c u hu (cofactorRealMatrix3 k₀)
    (by rw [cofactorRealMatrix3_det]; norm_num) _ _ hs ha hpoint hprod i 2
  obtain ⟨z, m, g, hz, hg, hm, hgm, hprim, hgcd, hmq, horth⟩ :=
    conditional_actual_primitive_normal3 G c u hu
  have hrealz (i : Fin 3) : |(cofactorDualValue3 k₀ (fun l => (z l : ℚ)) i : ℝ)| ≤
      36 * (∏ l : Fin 3, Q ^ c₀ l) * (Q ^ c₀ i)⁻¹ * Q ^ (-2 * delta) := by
    rw [cofactor_scaled_real_value3 k₀ (fun j => (u j : IntegerTriple)) _ z hz]
    exact cofactor_actual_real_bound3 k₀ k₂ k₃ Q delta c₀ c₂ c₃ hQ hc₂ hc₃ B u hB hreal hsmall i
  have hfinite := cofactor_actual_finite_bounds3 k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃ c u hu
  dsimp only at hfinite
  have hez : (fun l => ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) *
      dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 l) = fun l => (z l : ℚ) := funext hz
  rw [hez] at hfinite
  obtain ⟨s, hsS, hsnonzero⟩ := hnonzero
  have hzproduct := cofactor_selected_product_upper3 k₀ k₂ k₃ Q delta c₀ c₂ c₃ hQ hd
    hbalance s (hweights s hsS) z hrealz hfinite.1 hfinite.2
  let q : ℚ := ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) / g
  have hq : q ≠ 0 := div_ne_zero
    (by exact_mod_cast mul_ne_zero (Nat.ne_of_gt (dualFrameRelativeIndex3_pos G c u hu)) hDnat)
    (by exact_mod_cast hg)
  have hmcast : (fun i => (m i : ℚ)) = q • dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 :=
    funext hmq
  have hline : Submodule.span ℚ ({fun i => (m i : ℚ)} : Set (Fin 3 → ℚ)) =
      Submodule.span ℚ {dualFrameVector3 (fun j => (u j : IntegerTriple)) 2} := by
    rw [hmcast]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hq) _
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hq2 : (padicNorm 2 q : ℝ) ≠ 0 := by exact_mod_cast padicNorm.nonzero hq
  have hq3 : (padicNorm 3 q : ℝ) ≠ 0 := by exact_mod_cast padicNorm.nonzero hq
  have hmproduct : cofactorSelectedProduct3 k₀ k₂ k₃ s (fun l => (m l : ℚ)) ≠ 0 := by
    rw [hmcast]
    change cofactorSelectedProduct3 k₀ k₂ k₃ s
      (fun l => q * dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 l) ≠ 0
    rw [cofactorSelectedProduct3_scale]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (abs_ne_zero.mpr hqreal) hq2) hq3) hsnonzero
  have hlower := cofactor_selected_product_lower3 k₀ k₂ k₃ s m hm hmproduct
  have hupper := cofactor_primitive_product_le3 k₀ k₂ k₃ s g hg z m hgm
  have hl := conditional_height_lower_power3 Q delta (rothKernelRowHeight m) hQ
    (conditional_height_pos3 m hm) (hlower.trans (hupper.trans hzproduct))
  have hfinalLower := conditional_height_lower_absorb3 Q delta (rothKernelRowHeight m) hQ hd
    ((le_max_right _ _).trans hcut.le) hl
  have hfinalUpper := cofactor_upper_height_power3 k₀ Q delta c₀ hQ hd hc₀
    ((le_max_left _ _).trans hcut.le) g hg z m hgm hrealz
  exact ⟨z, m, g, hg, hm, hz, hgm, hprim, hgcd, ⟨q, hq, hmcast⟩, hline, horth, hJ,
    hfinalLower, hfinalUpper⟩

theorem cofactor_source_normal_height3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (S : Set (Fin 3 → Fin 3)) (_hS : S.Nonempty) :
    ∃ C1 C2 C3 : ℝ, 0 < C1 ∧ 0 < C2 ∧ 0 < C3 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q), C3 < Q →
      ∀ c₀ c₂ c₃ : Fin 3 → ℝ,
        (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) →
        (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) →
        (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        (∀ s ∈ S, -(3 * delta) / 4 ≤ c₀ (s 0) + c₂ (s 1) + c₃ (s 2)) →
        ∀ (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃),
          lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3 →
          LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) →
          (∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
            (integerTripleReal3 (u j : IntegerTriple)) =
              successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j) →
          successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) 1 < Q ^ (-delta) →
          (∃ s ∈ S, cofactorSelectedProduct3 k₀ k₂ k₃ s
            (dualFrameVector3 (fun j => (u j : IntegerTriple)) 2) ≠ 0) →
          ∃ (z m : IntegerTriple) (g : ℤ),
            g ≠ 0 ∧ m ≠ 0 ∧
            (∀ i, ((dualFrameRelativeIndex3 (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃) u *
              (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
                dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i = (z i : ℚ)) ∧
            (∀ i, z i = g * m i) ∧ Ideal.span (Set.range m) = ⊤ ∧
            Finset.univ.gcd (fun i => (m i).natAbs) = 1 ∧
            (∃ r : ℚ, r ≠ 0 ∧ (fun i => (m i : ℚ)) =
              r • dualFrameVector3 (fun j => (u j : IntegerTriple)) 2) ∧
            Submodule.span ℚ ({fun i => (m i : ℚ)} : Set (Fin 3 → ℚ)) =
              Submodule.span ℚ {dualFrameVector3 (fun j => (u j : IntegerTriple)) 2} ∧
            (∀ j : Fin 2, (∑ i : Fin 3, m i * ((u j.castSucc : IntegerTriple) i)) = 0) ∧
            dualFrameRelativeIndex3 (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃) u ≤ 6 ∧
            Q ^ C1 ≤ (rothKernelRowHeight m : ℝ) ∧ (rothKernelRowHeight m : ℝ) ≤ Q ^ C2 := by
  refine ⟨delta / 16,9,max 108 ((18 : ℝ) ^ (16 / delta)),by positivity,
    by norm_num,lt_of_lt_of_le (by norm_num : (0 : ℝ) < 108) (le_max_left _ _),?_⟩
  intro Q hQ hcut c₀ c₂ c₃ hc₀ hc₂ hc₃ hb ht B u hB hu hatt hsmall hnz
  exact cofactor_original_normal_height3 k₀ k₂ k₃ delta hd S _hS Q hQ hcut
    c₀ c₂ c₃ hc₀ hc₂ hc₃ hb ht B u hB hu hatt
    (source_attaining_frame_index_le_six3 _ B _ u hB hu hatt) hsmall hnz

theorem cofactor_finiteWeight_real_local_value3 (k : Fin 3) (w : IntegerTriple) (i : Fin 3) :
    rothLocalAbs 0 (rothNormalLocalValue (cofactorIntegerMatrix3 k) w i) =
      |cofactorRealCoordinates3 k (integerTripleReal3 w) i| := by
  change |((rothNormalLocalValue (cofactorIntegerMatrix3 k) w i : ℚ) : ℝ)| =
    |∑ l : Fin 3, (cofactorRealMatrix3 k) i l * (w l : ℝ)|
  simp [rothNormalLocalValue, cofactorRealMatrix3]

theorem cofactor_finiteWeight_rational_local_value3 (k : Fin 3) (w : IntegerTriple) (i : Fin 3) :
    rothNormalLocalValue (cofactorIntegerMatrix3 k) w i =
      cofactorForms3 k i (fun l => (w l : ℚ)) := by
  rw [← cofactorIntegerMatrix3_apply]
  simp [rothNormalLocalValue,Matrix.mulVec,dotProduct]

theorem cofactor_finiteWeight_same_frame3 (n : ℕ) (hn : 16 ≤ n)
    (deltaSource deltaAux Q : ℝ) (hQ : 1 < Q) (he : 7/(n : ℝ) ≤ deltaSource-deltaAux)
    (c : Fin 3 → Fin 3 → ℝ) (hc : sourceWeightConditions3 c) (k₀ k₂ k₃ : Fin 3)
    (B : Basis (Fin 3) ℝ RealTriple)
    (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q (c 1) (c 2))
    (hatt : ∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q (c 0) hQ)
      (integerTripleReal3 (u j : IntegerTriple)) =
        successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q (c 0) hQ) j)
    (hsmall : successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q (c 0) hQ) 1 < Q^(-deltaSource)) :
    (∀ j : Fin 2, ∀ i, rothLocalAbs 0
      (rothNormalLocalValue (cofactorIntegerMatrix3 k₀) (u j.castSucc : IntegerTriple) i) ≤
        Q^(finiteWeightApprox3 n c 0 i-deltaAux)) ∧
    (∀ j : Fin 2, ∀ i, rothLocalAbs 1
      (rothNormalLocalValue (cofactorIntegerMatrix3 k₂) (u j.castSucc : IntegerTriple) i) ≤
        Q^(finiteWeightApprox3 n c 1 i)) ∧
    (∀ j : Fin 2, ∀ i, rothLocalAbs 2
      (rothNormalLocalValue (cofactorIntegerMatrix3 k₃) (u j.castSucc : IntegerTriple) i) ≤
        Q^(finiteWeightApprox3 n c 2 i)) := by
  obtain ⟨_,h0,hf⟩ := finiteWeightApprox3_bounds n hn c hc
  have hp := lt_trans zero_lt_one hQ
  obtain ⟨_,_,_,_,horder,_⟩ := exists_successive_minima3 B (cofactorSourceCoordinates3 k₀ Q (c 0) hQ)
  have hrad (j : Fin 2) : successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q (c 0) hQ) j.castSucc ≤
      Q^(-deltaSource) := by
    fin_cases j
    · exact horder.1.trans hsmall.le
    · exact hsmall.le
  have hpoint (j : Fin 2) := (cofactorSourceLattice3_spec k₂ k₃ Q (c 1) (c 2) hQ
    (fun i => (hc.2.1 1 (by decide) i).2) (fun i => (hc.2.1 2 (by decide) i).2)).1
      (u j.castSucc) |>.mp (u j.castSucc).property
  refine ⟨?_,?_,?_⟩
  · intro j i
    rw [cofactor_finiteWeight_real_local_value3]
    have hb := cofactorSource_arch_bound k₀ Q (c 0) hQ (integerTripleReal3 (u j.castSucc : IntegerTriple)) i
    rw [hatt] at hb
    calc
      _ ≤ Q^(-deltaSource)*Q^(c 0 i) := hb.trans
        (mul_le_mul_of_nonneg_right (hrad j) (Real.rpow_nonneg hp.le _))
      _ = Q^(c 0 i-deltaSource) := by rw [← Real.rpow_add hp]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith [h0 i])
  · intro j i
    simp only [rothLocalAbs,Fin.reduceEq,ite_false,ite_true,cofactor_finiteWeight_rational_local_value3]
    exact ((hpoint j).1 i).trans (Real.rpow_le_rpow_of_exponent_le hQ.le (hf 1 (by decide) i))
  · intro j i
    simp only [rothLocalAbs,Fin.reduceEq,ite_false,ite_true,cofactor_finiteWeight_rational_local_value3]
    exact ((hpoint j).2 i).trans (Real.rpow_le_rpow_of_exponent_le hQ.le (hf 2 (by decide) i))

theorem cofactor_source_family_contradiction3
    (k₀ k₂ k₃ : Fin 3) (S : Set (Fin 3 → Fin 3)) (hS : S.Nonempty) :
    ∀ (deltaSource : ℝ), 0 < deltaSource →
    ∀ (U : Set ℝ), ¬ BddAbove U →
    ∀ (c : ℝ → Fin 3 → Fin 3 → ℝ),
      (∀ Q ∈ U, sourceWeightConditions3 (c Q)) →
      (∀ Q ∈ U, ∀ s ∈ S,
        -deltaSource/2 ≤ c Q 0 (s 0)+c Q 1 (s 1)+c Q 2 (s 2)) →
      (∀ Q ∈ U, ∀ hQ : 1 < Q,
        ∃ (B : Basis (Fin 3) ℝ RealTriple)
          (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q (c Q 1) (c Q 2)),
          lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q (c Q 1) (c Q 2)).toIntSubmodule.map integerTripleReal3 ∧
          LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) ∧
          (∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q (c Q 0) hQ)
            (integerTripleReal3 (u j : IntegerTriple)) =
              successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q (c Q 0) hQ) j) ∧
          dualFrameRelativeIndex3 (cofactorSourceLattice3 k₂ k₃ Q (c Q 1) (c Q 2)) u ≤ 6 ∧
          successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q (c Q 0) hQ) 1 < Q^(-deltaSource) ∧
          (∃ s ∈ S, cofactorSelectedProduct3 k₀ k₂ k₃ s
            (dualFrameVector3 (fun j => (u j : IntegerTriple)) 2) ≠ 0)) → False := by
  classical
  let L : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ :=
    ![cofactorIntegerMatrix3 k₀, cofactorIntegerMatrix3 k₂, cofactorIntegerMatrix3 k₃]
  have hL : ∀ tau, (rothLocalRationalMatrix (L tau)).det ≠ 0 := by
    intro tau
    fin_cases tau <;>
      change (cofactorRationalMatrix3 _).det ≠ 0 <;>
      rw [cofactorRationalMatrix3_det] <;> norm_num
  obtain ⟨D,E,hD,hE,haux⟩ := roth_auxiliary_integer_satz34 L hL
  intro deltaSource hd U hU c hc htuple hframes
  obtain ⟨n,deltaAux,etaCandidate,hn,he,haeq,_,ha,ha',_,_,hfinite,hreduce⟩ :=
    finiteWeightReduction3 deltaSource hd
  obtain ⟨d,hdmem,U',hsub,hU',hdconditions,htransport⟩ := hreduce U hU c hc
  obtain ⟨eta,theta,m,hm,Gamma,heta,htheta,htheta',hetad,hgap,hcount,
    hGamma,hGamma',hGammaAux,hrho,hselect⟩ :=
    source_compatible_parameter_selection3 D E deltaAux hD hE ha ha'
  obtain ⟨Q,r,hQ,hmono,hlogsep,hthreshold,hr,hsep,hbalance,hsum,hbudgets⟩ := hselect U' hU'
  have hQone (h : Fin m) : 1 < Q h := (hQ h).2.2
  have hQU (h : Fin m) : Q h ∈ U := hsub (hQ h).1
  choose B u hB hu hatt hJ hsmall hnonzero using
    (fun h : Fin m => hframes (Q h) (hQU h) (hQone h))
  have hcut (h : Fin m) : max 108 ((18 : ℝ)^(16/deltaSource)) < Q h := by
    have hcut' := sameIndex_cutoff_transport3 deltaSource hd
    rw [← haeq] at hcut'
    exact hcut'.trans_lt (hQ h).2.1
  have hweights (h : Fin m) (s : Fin 3 → Fin 3) (hs : s ∈ S) :
      -(3*deltaSource)/4 ≤ c (Q h) 0 (s 0)+c (Q h) 1 (s 1)+c (Q h) 2 (s 2) := by
    linarith [htuple (Q h) (hQU h) s hs]
  have hzero (h : Fin m) :
      ∑ i, (c (Q h) 0 i+c (Q h) 1 i+c (Q h) 2 i) = 0 := by
    have hh := (hc (Q h) (hQU h)).2.2
    rw [Fin.sum_univ_three] at hh
    simpa only [Finset.sum_add_distrib] using hh
  have hnormal (h : Fin m) := cofactor_original_normal_height3 k₀ k₂ k₃ deltaSource hd S hS
    (Q h) (hQone h) (hcut h) (c (Q h) 0) (c (Q h) 1) (c (Q h) 2)
    (hc (Q h) (hQU h)).1
    ((hc (Q h) (hQU h)).2.1 1 (by decide))
    ((hc (Q h) (hQU h)).2.1 2 (by decide)) (hzero h) (hweights h)
    (B h) (u h) (hB h) (hu h) (hatt h) (hJ h) (hsmall h) (hnonzero h)
  choose z V g hg hV hz hgm hprim hgcd hscale hline horth hJ' hheightLower hheightUpper using hnormal
  have hrow (h : Fin m) : (∃ i, V h i ≠ 0) ∧ Ideal.span (Set.range (V h)) = ⊤ := by
    refine ⟨?_,hprim h⟩
    by_contra hh
    push_neg at hh
    exact hV h (funext hh)
  have henvelope (h : Fin m) :
      (Q h)^(deltaAux/16) ≤ (rothKernelRowHeight (V h) : ℝ) ∧
      (rothKernelRowHeight (V h) : ℝ) ≤ (Q h)^(9 : ℝ) := by
    refine ⟨?_,hheightUpper h⟩
    have hl := sameIndex_height_transport3 deltaSource (Q h) hd (hQone h)
    rw [← haeq] at hl
    exact hl.trans (hheightLower h)
  obtain ⟨hgrowth,hden,hheight⟩ := hbudgets
    (fun h => (rothKernelRowHeight (V h) : ℝ)) henvelope
  let w : Fin m → Fin 2 → IntegerTriple := fun h j => (u h j.castSucc : IntegerTriple)
  have hli (h : Fin m) : LinearIndependent ℚ (fun j : Fin 2 => fun i : Fin 3 => (w h j i : ℚ)) :=
    (dualFrameMatrix3_rational_independent (fun j => (u h j : IntegerTriple)) (hu h)).comp
      Fin.castSucc (Fin.castSucc_injective 2)
  have hexponent : 7/(n : ℝ) ≤ deltaSource-deltaAux := by
    have ha2 := (finiteWeight_delta3 deltaSource hd).2.2.1
    rw [← haeq] at ha2
    linarith
  have hpoints (h : Fin m) := cofactor_finiteWeight_same_frame3 n hn deltaSource deltaAux (Q h) (hQone h)
    hexponent (c (Q h)) (hc (Q h) (hQU h)) k₀ k₂ k₃ (B h) (u h) (hatt h) (hsmall h)
  have hfixed (h : Fin m) : finiteWeightApprox3 n (c (Q h)) = d :=
    (htransport (Q h) (hQ h).1).1
  have hw0 (h : Fin m) (j : Fin 2) (i : Fin 3) :
      rothLocalAbs 0 (rothNormalLocalValue (L 0) (w h j) i) ≤ (Q h)^(d 0 i-deltaAux) := by
    have hh := (hpoints h).1 j i
    rw [hfixed h] at hh
    simpa only [L,w,Matrix.cons_val_zero] using hh
  have hw1 (h : Fin m) (j : Fin 2) (i : Fin 3) :
      rothLocalAbs 1 (rothNormalLocalValue (L 1) (w h j) i) ≤ (Q h)^(d 1 i) := by
    have hh := (hpoints h).2.1 j i
    rw [hfixed h] at hh
    simpa only [L,w,Matrix.cons_val_one,Matrix.cons_val_zero] using hh
  have hw2 (h : Fin m) (j : Fin 2) (i : Fin 3) :
      rothLocalAbs 2 (rothNormalLocalValue (L 2) (w h j) i) ≤ (Q h)^(d 2 i) := by
    have hh := (hpoints h).2.2 j i
    rw [hfixed h] at hh
    simpa only [L,w,Matrix.cons_val_two,Matrix.cons_val_one,Matrix.cons_val_zero] using hh
  have habs (tau i : Fin 3) : |d tau i| ≤ 1 := by
    by_cases ht : tau = 0
    · simpa only [ht] using hdconditions.1 i
    · exact abs_le.mpr ⟨(hdconditions.2.1 tau ht i).1,by linarith [(hdconditions.2.1 tau ht i).2]⟩
  obtain ⟨P,hP,hhom,hPH,hsourceIndex,hhigh⟩ := haux eta heta m hcount r hr
  have hhighIndex : rothSourceHighIndex r V ((m : ℝ)*eta) P :=
    hhigh deltaAux d Q ⟨0,hm⟩ hdconditions.2.2 habs hetad ha' hQone
      (fun h => (hthreshold h).1) (fun h => (hthreshold h).2) hbalance w hw0 hw1 hw2 V hrow hli horth
  obtain ⟨J,k,hweight,hpivot,hnonzeroRestriction⟩ := roth_full_kernel_omega65_nonvanishing
    m hm theta Gamma htheta htheta' hGamma hGamma' r V P hr hsep hrow
    (fun h _ => hgrowth h) hden hP hhom (hheight P hPH)
  have hweight' : rothSourceDerivativeWeight r J < (m : ℝ)*eta := hweight.trans_lt hgap
  exact hnonzeroRestriction (hhighIndex J hweight' k hpivot)

end
end JSP000334
