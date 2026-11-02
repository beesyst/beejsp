import SubspaceBridge.SameIndexAssembly3
open scoped BigOperators Matrix
namespace JSP000334

def selectedBadQ3 (k₀ k₂ k₃ : Fin 3) (S : Set (Fin 3 → Fin 3)) (deltaSource : ℝ) : Set ℝ :=
  {Q | ∃ hQ : 1 < Q, ∃ c : Fin 3 → Fin 3 → ℝ,
    sourceWeightConditions3 c ∧
    (∀ s ∈ S, -deltaSource/2 ≤ c 0 (s 0)+c 1 (s 1)+c 2 (s 2)) ∧
      ∃ (B : Basis (Fin 3) ℝ RealTriple)
          (u : Fin 3 → qSourceLattice3 k₂ k₃ Q (c 1) (c 2)),
          lattice3 B = (qSourceLattice3 k₂ k₃ Q (c 1) (c 2)).toIntSubmodule.map integerTripleReal3 ∧
          LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) ∧
          (∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q (c 0) hQ)
            (integerTripleReal3 (u j : IntegerTriple)) =
              successiveRadius3 B (qSourceCoordinates3 k₀ Q (c 0) hQ) j) ∧
          dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q (c 1) (c 2)) u ≤ 6 ∧
          successiveRadius3 B (qSourceCoordinates3 k₀ Q (c 0) hQ) 1 < Q^(-deltaSource) ∧
          (∃ s ∈ S, conditionalSelectedProduct3 k₀ k₂ k₃ s
            (dualFrameVector3 (fun j => (u j : IntegerTriple)) 2) ≠ 0)}

theorem selectedBadQ3_bddAbove (k₀ k₂ k₃ : Fin 3) (S : Set (Fin 3 → Fin 3))
    (hS : S.Nonempty) (deltaSource : ℝ) (hd : 0 < deltaSource) :
    BddAbove (selectedBadQ3 k₀ k₂ k₃ S deltaSource) := by
  classical
  by_contra hU
  have hw (Q : ℝ) : ∃ c : Fin 3 → Fin 3 → ℝ,
      Q ∈ selectedBadQ3 k₀ k₂ k₃ S deltaSource →
      sourceWeightConditions3 c ∧
      (∀ s ∈ S, -deltaSource/2 ≤ c 0 (s 0)+c 1 (s 1)+c 2 (s 2)) ∧
      ∀ hQ : 1 < Q,
      ∃ (B : Basis (Fin 3) ℝ RealTriple)
          (u : Fin 3 → qSourceLattice3 k₂ k₃ Q (c 1) (c 2)),
          lattice3 B = (qSourceLattice3 k₂ k₃ Q (c 1) (c 2)).toIntSubmodule.map integerTripleReal3 ∧
          LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) ∧
          (∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q (c 0) hQ)
            (integerTripleReal3 (u j : IntegerTriple)) =
              successiveRadius3 B (qSourceCoordinates3 k₀ Q (c 0) hQ) j) ∧
          dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q (c 1) (c 2)) u ≤ 6 ∧
          successiveRadius3 B (qSourceCoordinates3 k₀ Q (c 0) hQ) 1 < Q^(-deltaSource) ∧
          (∃ s ∈ S, conditionalSelectedProduct3 k₀ k₂ k₃ s
            (dualFrameVector3 (fun j => (u j : IntegerTriple)) 2) ≠ 0) := by
    by_cases h : Q ∈ selectedBadQ3 k₀ k₂ k₃ S deltaSource
    · obtain ⟨hQ,c,hc,ht,hf⟩ := h
      exact ⟨c,fun _ => ⟨hc,ht,fun _ => hf⟩⟩
    · exact ⟨0,fun hh => (h hh).elim⟩
  choose c hc using hw
  exact sameIndex_source_family_contradiction3 k₀ k₂ k₃ S hS deltaSource hd
    (selectedBadQ3 k₀ k₂ k₃ S deltaSource) hU c
    (fun Q h => (hc Q h).1) (fun Q h => (hc Q h).2.1)
    (fun Q h => (hc Q h).2.2)

theorem source_attaining_frame_index_le_six3 (G : AddSubgroup IntegerTriple)
    (B : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (u : Fin 3 → G)
    (hB : lattice3 B = G.toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 e (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B e j) : dualFrameRelativeIndex3 G u ≤ 6 := by
  have hb := successive_minima3_attaining_index_le_six B e
  rw [hB] at hb
  rw [dualFrameRelativeIndex3,integerTripleRealEquiv3_index G u]
  apply hb (fun j => integerTripleRealEquiv3 G (u j))
  · simpa only [integerTripleRealEquiv3_apply] using hu
  · simpa only [integerTripleRealEquiv3_apply] using hatt

theorem normalized_uniform_selected_vanishing3 (k₀ k₂ k₃ : Fin 3)
    (S : Set (Fin 3 → Fin 3)) (hS : S.Nonempty) (deltaSource : ℝ) (hd : 0 < deltaSource) :
    ∃ Q0 : ℝ, 1 ≤ Q0 ∧
      ∀ Q : ℝ, Q0 < Q → ∀ hQ : 1 < Q,
      ∀ c : Fin 3 → Fin 3 → ℝ, sourceWeightConditions3 c →
        (∀ s ∈ S, -deltaSource/2 ≤ c 0 (s 0)+c 1 (s 1)+c 2 (s 2)) →
      ∀ (B : Basis (Fin 3) ℝ RealTriple)
        (u : Fin 3 → qSourceLattice3 k₂ k₃ Q (c 1) (c 2)),
          lattice3 B = (qSourceLattice3 k₂ k₃ Q (c 1) (c 2)).toIntSubmodule.map integerTripleReal3 →
          LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) →
          (∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q (c 0) hQ)
            (integerTripleReal3 (u j : IntegerTriple)) =
              successiveRadius3 B (qSourceCoordinates3 k₀ Q (c 0) hQ) j) →
          successiveRadius3 B (qSourceCoordinates3 k₀ Q (c 0) hQ) 1 < Q^(-deltaSource) →
      ∀ s ∈ S, conditionalSelectedProduct3 k₀ k₂ k₃ s
        (dualFrameVector3 (fun j => (u j : IntegerTriple)) 2) = 0 := by
  obtain ⟨B0,hB0⟩ := selectedBadQ3_bddAbove k₀ k₂ k₃ S hS deltaSource hd
  refine ⟨max 1 B0,le_max_left _ _,?_⟩
  intro Q hcut hQ c hc ht B u hB hu hatt hsmall s hs
  have hJ := source_attaining_frame_index_le_six3 _ B _ u hB hu hatt
  by_contra hnz
  have hbad : Q ∈ selectedBadQ3 k₀ k₂ k₃ S deltaSource :=
    ⟨hQ,c,hc,ht,B,u,hB,hu,hatt,hJ,hsmall,s,hs,hnz⟩
  exact (not_lt_of_ge (hB0 hbad)) (lt_of_le_of_lt (le_max_right _ _) hcut)

noncomputable def sourceIntegralWidths3 (A : Fin 3 → ℝ) (f₂ f₃ : Fin 3 → ℤ) :
    Fin 3 → Fin 3 → ℝ := ![A,fun i => (2 : ℝ)^(f₂ i : ℝ),fun i => (3 : ℝ)^(f₃ i : ℝ)]

def sourceIntegralLattice3 (k₂ k₃ : Fin 3) (f₂ f₃ : Fin 3 → ℤ) : AddSubgroup IntegerTriple :=
  mixedCongruence3 (retainedIntegerMatrix3 k₂) (retainedIntegerMatrix3 k₃)
    (fun i => (-f₂ i).toNat) (fun i => (-f₃ i).toNat)

theorem sourceIntegralWidths3_pos (A : Fin 3 → ℝ) (f₂ f₃ : Fin 3 → ℤ)
    (hA : ∀ i, 0 < A i) : ∀ tau i, 0 < sourceIntegralWidths3 A f₂ f₃ tau i := by
  intro tau i
  fin_cases tau
  · exact hA i
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · exact Real.rpow_pos_of_pos (by norm_num) _

theorem sourceIntegral_threshold_exact3 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q) (f : ℤ) :
    qThreshold p Q (Real.log ((p : ℝ)^(f : ℝ))/Real.log Q) = ((-f : ℤ) : ℝ) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hlQ := (Real.log_pos hQ).ne'
  have hlp := (Real.log_pos hp').ne'
  unfold qThreshold
  rw [Real.log_rpow (by linarith : (0 : ℝ) < p)]
  push_cast
  field_simp
  ring

theorem sourceIntegral_prime_threshold3 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q) (f : ℤ) :
    Nat.ceil (qThreshold p Q (Real.log ((p : ℝ)^(f : ℝ))/Real.log Q)) = (-f).toNat := by
  rw [sourceIntegral_threshold_exact3 p hp Q hQ f,Nat.ceil_intCast]

theorem sourceIntegral_lattice_eq3 (k₂ k₃ : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (A : Fin 3 → ℝ) (f₂ f₃ : Fin 3 → ℤ) :
    qSourceLattice3 k₂ k₃ Q (sourceLogWeights3 Q (sourceIntegralWidths3 A f₂ f₃) 1)
      (sourceLogWeights3 Q (sourceIntegralWidths3 A f₂ f₃) 2) = sourceIntegralLattice3 k₂ k₃ f₂ f₃ := by
  unfold qSourceLattice3 sourceIntegralLattice3
  congr 1 <;> funext i <;>
    simp only [sourceLogWeights3,sourceIntegralWidths3,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_zero] <;>
    apply sourceIntegral_prime_threshold3 _ (by decide) Q hQ

theorem sourceIntegral_coordinates_eq3 (k₀ : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (A : Fin 3 → ℝ) (f₂ f₃ : Fin 3 → ℤ) (hA : ∀ i, 0 < A i) :
    qSourceCoordinates3 k₀ Q (sourceLogWeights3 Q (sourceIntegralWidths3 A f₂ f₃) 0) hQ =
      archCoordinates3 (retainedRealCoordinates3 k₀) A hA := by
  ext x i
  change retainedRealCoordinates3 k₀ x i /
      Q^(sourceLogWeights3 Q (sourceIntegralWidths3 A f₂ f₃) 0 i) = _
  rw [sourceLogWeights3_rpow Q hQ _ (sourceIntegralWidths3_pos A f₂ f₃ hA)]
  rfl

theorem sourceIntegral_rounding_eq_one3 (Q : ℝ) (hQ : 1 < Q)
    (A : Fin 3 → ℝ) (f₂ f₃ : Fin 3 → ℤ)
    (hf₂ : ∀ i, f₂ i ≤ 0) (hf₃ : ∀ i, f₃ i ≤ 0) :
    qRoundingFactor3 Q (sourceLogWeights3 Q (sourceIntegralWidths3 A f₂ f₃) 1)
      (sourceLogWeights3 Q (sourceIntegralWidths3 A f₂ f₃) 2) = 1 := by
  apply qRoundingFactor3_eq_one_of_integral
  · intro i
    refine ⟨(-f₂ i).toNat,?_⟩
    change qThreshold 2 Q (Real.log ((2 : ℝ)^(f₂ i : ℝ))/Real.log Q) = _
    have h := sourceIntegral_threshold_exact3 2 (by decide) Q hQ (f₂ i)
    norm_num only [Nat.cast_ofNat] at h
    rw [h]
    norm_cast
    exact (Int.toNat_of_nonneg (by linarith [hf₂ i])).symm
  · intro i
    refine ⟨(-f₃ i).toNat,?_⟩
    change qThreshold 3 Q (Real.log ((3 : ℝ)^(f₃ i : ℝ))/Real.log Q) = _
    have h := sourceIntegral_threshold_exact3 3 (by decide) Q hQ (f₃ i)
    norm_num only [Nat.cast_ofNat] at h
    rw [h]
    norm_cast
    exact (Int.toNat_of_nonneg (by linarith [hf₃ i])).symm

theorem sourceIntegral_covolume_eq_index3 (k₂ k₃ : Fin 3) (f₂ f₃ : Fin 3 → ℤ) :
    ZLattice.covolume ((sourceIntegralLattice3 k₂ k₃ f₂ f₃).toIntSubmodule.map integerTripleReal3) =
      ((sourceIntegralLattice3 k₂ k₃ f₂ f₃).index : ℝ) := by
  exact mixedCongruence3_covolume_eq_index (retainedIntegerMatrix3 k₂) (retainedIntegerMatrix3 k₃)
    (retainedIntegerMatrix3_isUnit k₂) (retainedIntegerMatrix3_isUnit k₃) _ _

theorem selected_product_index_scaling_zero3 (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (c₂ c₃ : Fin 3 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (s : Fin 3 → Fin 3) :
    conditionalSelectedProduct3 k₀ k₂ k₃ s
      (fun i => (((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
        (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
        dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i)) = 0 ↔
    conditionalSelectedProduct3 k₀ k₂ k₃ s
      (dualFrameVector3 (fun j => (u j : IntegerTriple)) 2) = 0 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let G := qSourceLattice3 k₂ k₃ Q c₂ c₃
  obtain ⟨b⟩ : Nonempty (Basis (Fin 3) ℤ G) := mixedCongruence3_has_basis _ _ _ _
  have hJ := dualFrameRelativeIndex3_pos G b u hu
  have hD : 0 < G.index := by
    rw [(qSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1]
    unfold qCongruenceIndex3
    positivity
  let q : ℚ := ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact_mod_cast (mul_pos hJ hD).ne'
  have hreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have h2 : (padicNorm 2 q : ℝ) ≠ 0 := by exact_mod_cast padicNorm.nonzero hq
  have h3 : (padicNorm 3 q : ℝ) ≠ 0 := by exact_mod_cast padicNorm.nonzero hq
  rw [conditionalSelectedProduct3_scale]
  exact mul_eq_zero_iff_left (mul_ne_zero (mul_ne_zero (abs_ne_zero.mpr hreal) h2) h3)

theorem sourceIntegral_weights_conditions3 (Q : ℝ) (hQ : 1 < Q)
    (A : Fin 3 → ℝ) (f₂ f₃ : Fin 3 → ℤ) (hA : ∀ i, 0 < A i)
    (hf₂ : ∀ i, f₂ i ≤ 0) (hf₃ : ∀ i, f₃ i ≤ 0)
    (hcut : ∀ i, A i < Q ∧ (A i)⁻¹ < Q ∧
      (2 : ℝ)^(-(f₂ i : ℝ)) < Q ∧ (3 : ℝ)^(-(f₃ i : ℝ)) < Q)
    (hnorm : (∏ i, A i*(2 : ℝ)^(f₂ i : ℝ)*(3 : ℝ)^(f₃ i : ℝ)) = 1) :
    sourceWeightConditions3 (sourceLogWeights3 Q (sourceIntegralWidths3 A f₂ f₃)) := by
  apply sourceLogWeights3_conditions Q hQ _ (sourceIntegralWidths3_pos A f₂ f₃ hA)
  · intro tau i
    fin_cases tau
    · exact (hcut i).2.1
    · change ((2 : ℝ)^(f₂ i : ℝ))⁻¹ < Q
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      exact (hcut i).2.2.1
    · change ((3 : ℝ)^(f₃ i : ℝ))⁻¹ < Q
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      exact (hcut i).2.2.2
  · intro i
    exact (hcut i).1
  · intro tau ht i
    fin_cases tau
    · exact (ht rfl).elim
    · exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by exact_mod_cast hf₂ i)
    · exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by exact_mod_cast hf₃ i)
  · rw [Fin.prod_univ_three]
    change (∏ i, A i)*(∏ i, (2 : ℝ)^(f₂ i : ℝ))*(∏ i, (3 : ℝ)^(f₃ i : ℝ)) = 1
    simpa only [Finset.prod_mul_distrib] using hnorm

theorem sourceIntegral_lattice_spec3 (k₂ k₃ : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (A : Fin 3 → ℝ) (f₂ f₃ : Fin 3 → ℤ) (hA : ∀ i, 0 < A i)
    (hf₂ : ∀ i, f₂ i ≤ 0) (hf₃ : ∀ i, f₃ i ≤ 0) :
    ∀ x : IntegerTriple, x ∈ sourceIntegralLattice3 k₂ k₃ f₂ f₃ ↔
      (∀ i, (padicNorm 2 (threeCoordinateSumForms k₂ i (fun j => (x j : ℚ))) : ℝ) ≤ (2 : ℝ)^(f₂ i : ℝ)) ∧
      (∀ i, (padicNorm 3 (threeCoordinateSumForms k₃ i (fun j => (x j : ℚ))) : ℝ) ≤ (3 : ℝ)^(f₃ i : ℝ)) := by
  let W := sourceIntegralWidths3 A f₂ f₃
  have hW := sourceIntegralWidths3_pos A f₂ f₃ hA
  have hc₂ (i) : sourceLogWeights3 Q W 1 i ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (Real.log_pos hQ).le
    apply Real.log_nonpos (hW 1 i).le
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by exact_mod_cast hf₂ i)
  have hc₃ (i) : sourceLogWeights3 Q W 2 i ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (Real.log_pos hQ).le
    apply Real.log_nonpos (hW 2 i).le
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by exact_mod_cast hf₃ i)
  have h := (qSourceLattice3_spec k₂ k₃ Q (sourceLogWeights3 Q W 1)
    (sourceLogWeights3 Q W 2) hQ hc₂ hc₃).1
  rw [sourceIntegral_lattice_eq3 k₂ k₃ Q hQ A f₂ f₃] at h
  have h2 (i) : Q^(sourceLogWeights3 Q W 1 i) = (2 : ℝ)^(f₂ i : ℝ) :=
    sourceLogWeights3_rpow Q hQ W hW 1 i
  have h3 (i) : Q^(sourceLogWeights3 Q W 2 i) = (3 : ℝ)^(f₃ i : ℝ) :=
    sourceLogWeights3_rpow Q hQ W hW 2 i
  simpa only [h2,h3] using h

theorem source_uniform_selected_vanishing3 (k₀ k₂ k₃ : Fin 3)
    (S : Set (Fin 3 → Fin 3)) (hS : S.Nonempty) (deltaSource : ℝ) (hd : 0 < deltaSource) :
    ∃ Q0 : ℝ, 1 ≤ Q0 ∧ ∀ Q : ℝ, Q0 < Q →
      ∀ (A : Fin 3 → ℝ) (f₂ f₃ : Fin 3 → ℤ) (hA : ∀ i, 0 < A i),
      (∀ i, f₂ i ≤ 0) → (∀ i, f₃ i ≤ 0) →
      (∀ i, A i < Q ∧ (A i)⁻¹ < Q ∧ (2 : ℝ)^(-(f₂ i : ℝ)) < Q ∧
        (3 : ℝ)^(-(f₃ i : ℝ)) < Q) →
      (∏ i, A i*(2 : ℝ)^(f₂ i : ℝ)*(3 : ℝ)^(f₃ i : ℝ)) = 1 →
      (∀ s ∈ S, 1 ≤ A (s 0)*(2 : ℝ)^(f₂ (s 1) : ℝ)*
        (3 : ℝ)^(f₃ (s 2) : ℝ)*Q^(deltaSource/2)) →
      ∀ (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → sourceIntegralLattice3 k₂ k₃ f₂ f₃),
      lattice3 B = (sourceIntegralLattice3 k₂ k₃ f₂ f₃).toIntSubmodule.map integerTripleReal3 →
      LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) →
      (∀ j, coordinateGauge3 (archCoordinates3 (retainedRealCoordinates3 k₀) A hA)
        (integerTripleReal3 (u j : IntegerTriple)) =
          successiveRadius3 B (archCoordinates3 (retainedRealCoordinates3 k₀) A hA) j) →
      successiveRadius3 B (archCoordinates3 (retainedRealCoordinates3 k₀) A hA) 1 < Q^(-deltaSource) →
      ∀ s ∈ S, conditionalSelectedProduct3 k₀ k₂ k₃ s
        (fun i => (((dualFrameRelativeIndex3 (sourceIntegralLattice3 k₂ k₃ f₂ f₃) u *
          (sourceIntegralLattice3 k₂ k₃ f₂ f₃).index : ℕ) : ℚ) *
          dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i)) = 0 := by
  obtain ⟨Q0,hQ0,hvan⟩ := normalized_uniform_selected_vanishing3 k₀ k₂ k₃ S hS deltaSource hd
  refine ⟨Q0,hQ0,?_⟩
  intro Q hcut
  have hQ : 1 < Q := lt_of_le_of_lt hQ0 hcut
  intro A f₂ f₃ hA hf₂ hf₃ hsourcecut hnorm htuple
  let W := sourceIntegralWidths3 A f₂ f₃
  let c := sourceLogWeights3 Q W
  have hc := sourceIntegral_weights_conditions3 Q hQ A f₂ f₃ hA hf₂ hf₃ hsourcecut hnorm
  have ht (s : Fin 3 → Fin 3) (hs : s ∈ S) :
      -deltaSource/2 ≤ c 0 (s 0)+c 1 (s 1)+c 2 (s 2) :=
    sourceWeight48_log3 Q deltaSource hQ W (sourceIntegralWidths3_pos A f₂ f₃ hA) s (htuple s hs)
  have hresult := hvan Q hcut hQ c hc ht
  rw [sourceIntegral_lattice_eq3 k₂ k₃ Q hQ A f₂ f₃,
    sourceIntegral_coordinates_eq3 k₀ Q hQ A f₂ f₃ hA] at hresult
  intro B u hB hu hatt hsmall s hs
  have hz := hresult B u hB hu hatt hsmall s hs
  rw [conditionalSelectedProduct3_scale,hz,mul_zero]

end JSP000334
