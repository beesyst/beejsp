import SubspaceBridge.SelectedProductVanishing3
open scoped BigOperators Matrix
open MeasureTheory
namespace JSP000334
noncomputable section

def cofactorIntegerMatrix3 (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℤ :=
  (retainedIntegerMatrix3 k).adjugate.transpose

theorem cofactorIntegerMatrix3_det (k : Fin 3) : (cofactorIntegerMatrix3 k).det = 1 := by
  rw [cofactorIntegerMatrix3,Matrix.det_transpose,Matrix.det_adjugate,retainedIntegerMatrix3_det]
  split_ifs <;> norm_num

theorem cofactorIntegerMatrix3_isUnit (k : Fin 3) : IsUnit (cofactorIntegerMatrix3 k) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [cofactorIntegerMatrix3_det]
  exact isUnit_one

def cofactorForms3 (k i : Fin 3) (x : Fin 3 → ℚ) : ℚ :=
  ∑ j : Fin 3, (cofactorIntegerMatrix3 k i j : ℚ) * x j

theorem cofactorIntegerMatrix3_apply (k i : Fin 3) (x : IntegerTriple) :
    (((cofactorIntegerMatrix3 k *ᵥ x) i : ℤ) : ℚ) =
      cofactorForms3 k i (fun j => (x j : ℚ)) := by
  simp [Matrix.mulVec,dotProduct,cofactorForms3]

theorem exists_cofactor_mixedCongruence3_Q_lattice
    (k₂ k₃ : Fin 3) (c₂ c₃ : Fin 3 → ℝ) (Q : ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    let a := fun i => Nat.ceil (-c₂ i * Real.log Q / Real.log 2)
    let b := fun i => Nat.ceil (-c₃ i * Real.log Q / Real.log 3)
    ∃ G : AddSubgroup IntegerTriple,
      (∀ x, x ∈ G ↔
        (∀ i, (padicNorm 2 (cofactorForms3 k₂ i (fun j => (x j : ℚ))) : ℝ) ≤
          Real.rpow Q (c₂ i)) ∧
        (∀ i, (padicNorm 3 (cofactorForms3 k₃ i (fun j => (x j : ℚ))) : ℝ) ≤
          Real.rpow Q (c₃ i))) ∧
      G = mixedCongruence3 (cofactorIntegerMatrix3 k₂) (cofactorIntegerMatrix3 k₃) a b ∧
      Finite (IntegerTriple ⧸ G) ∧
      G.index = 2 ^ (∑ i, a i) * 3 ^ (∑ i, b i) ∧
      ZLattice.covolume (G.toIntSubmodule.map integerTripleReal3) =
        (2 : ℝ) ^ (∑ i, a i) * 3 ^ (∑ i, b i) := by
  obtain ⟨G, hmem, heq, hf, hi, hv⟩ := exists_mixedCongruence3_Q_lattice
    (cofactorIntegerMatrix3 k₂) (cofactorIntegerMatrix3 k₃)
    (cofactorIntegerMatrix3_isUnit k₂) (cofactorIntegerMatrix3_isUnit k₃)
    c₂ c₃ Q hQ hc₂ hc₃
  refine ⟨G, ?_, heq, hf, hi, hv⟩
  intro x
  simpa only [cofactorIntegerMatrix3_apply] using hmem x


def cofactorRealMatrix3 (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (cofactorIntegerMatrix3 k).map (Int.castRingHom ℝ)

theorem cofactorRealMatrix3_det (k : Fin 3) : (cofactorRealMatrix3 k).det = 1 := by
  have hc : (cofactorRealMatrix3 k).det = ((cofactorIntegerMatrix3 k).det : ℝ) :=
    ((Int.castRingHom ℝ).map_det _).symm
  rw [hc,cofactorIntegerMatrix3_det]
  norm_num

def cofactorRealCoordinates3 (k : Fin 3) : RealTriple ≃ₗ[ℝ] RealTriple :=
  LinearEquiv.ofBijective (Matrix.toLin' (cofactorRealMatrix3 k)) (by
    have hu : IsUnit (cofactorRealMatrix3 k) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      rw [cofactorRealMatrix3_det]
      norm_num
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu, Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩)

theorem cofactorRealCoordinates3_abs_det (k : Fin 3) :
    |LinearMap.det (cofactorRealCoordinates3 k).toLinearMap| = 1 := by
  change |LinearMap.det (Matrix.toLin' (cofactorRealMatrix3 k))| = 1
  rw [LinearMap.det_toLin', cofactorRealMatrix3_det]
  norm_num

theorem cofactorRealBody3_volume (k : Fin 3) (w : Fin 3 → ℝ) (hw : ∀ i, 0 < w i) :
    volume.real (archBody3 (cofactorRealCoordinates3 k) w) = 8 * ∏ i, w i := by
  rw [archBody3_volume _ _ hw, cofactorRealCoordinates3_abs_det, div_one]

def cofactorSourceBody3 (k : Fin 3) (Q : ℝ) (c₀ : Fin 3 → ℝ) : Set RealTriple :=
  {x | ∀ i, |(cofactorRealMatrix3 k *ᵥ x) i| ≤ Q ^ c₀ i}

def cofactorSourceCoordinates3 (k : Fin 3) (Q : ℝ) (c₀ : Fin 3 → ℝ) (hQ : 1 < Q) :
    RealTriple ≃ₗ[ℝ] RealTriple :=
  archCoordinates3 (cofactorRealCoordinates3 k) (fun i => Q ^ c₀ i)
    (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) (c₀ i))

def cofactorSourceLattice3 (k₂ k₃ : Fin 3) (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ) : AddSubgroup IntegerTriple :=
  mixedCongruence3 (cofactorIntegerMatrix3 k₂) (cofactorIntegerMatrix3 k₃)
    (fun i => Nat.ceil (qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (qThreshold 3 Q (c₃ i)))

theorem cofactorSourceBody3_eq_parallelepiped (k : Fin 3) (Q : ℝ) (c₀ : Fin 3 → ℝ) (hQ : 1 < Q) :
    cofactorSourceBody3 k Q c₀ = parallelepipedBody3 (cofactorSourceCoordinates3 k Q c₀ hQ) := by
  change archBody3 (cofactorRealCoordinates3 k) (fun i => Q ^ c₀ i) = _
  exact archBody3_eq_parallelepiped _ _ _

theorem cofactorSourceBody3_volume (k : Fin 3) (Q : ℝ) (c₀ : Fin 3 → ℝ) (hQ : 1 < Q) :
    volume.real (cofactorSourceBody3 k Q c₀) = 8 * ∏ i, Q ^ c₀ i := by
  change volume.real (archBody3 (cofactorRealCoordinates3 k) (fun i => Q ^ c₀ i)) = _
  exact cofactorRealBody3_volume _ _ (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) (c₀ i))

theorem cofactorSourceLattice3_spec (k₂ k₃ : Fin 3) (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    (∀ x, x ∈ cofactorSourceLattice3 k₂ k₃ Q c₂ c₃ ↔
      (∀ i, (padicNorm 2 (cofactorForms3 k₂ i (fun j => (x j : ℚ))) : ℝ) ≤ Q ^ c₂ i) ∧
      (∀ i, (padicNorm 3 (cofactorForms3 k₃ i (fun j => (x j : ℚ))) : ℝ) ≤ Q ^ c₃ i)) ∧
    Finite (IntegerTriple ⧸ cofactorSourceLattice3 k₂ k₃ Q c₂ c₃) ∧
    (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index = qCongruenceIndex3 Q c₂ c₃ ∧
    ZLattice.covolume ((cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3) =
      (qCongruenceIndex3 Q c₂ c₃ : ℝ) := by
  obtain ⟨G, hm, heq, hf, hi, hv⟩ :=
    exists_cofactor_mixedCongruence3_Q_lattice k₂ k₃ c₂ c₃ Q hQ hc₂ hc₃
  have heq' : G = cofactorSourceLattice3 k₂ k₃ Q c₂ c₃ := heq
  subst G
  refine ⟨hm, hf, hi, ?_⟩
  simpa only [qCongruenceIndex3, qThreshold, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hv

theorem exists_cofactorSource_minima_upper
    (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    ∃ B : Basis (Fin 3) ℝ RealTriple,
      lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3 ∧
      (∏ i, successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) i) ≤ qRoundingFactor3 Q c₂ c₃ ∧
      qRoundingFactor3 Q c₂ c₃ < 216 := by
  let a := fun i => Nat.ceil (qThreshold 2 Q (c₂ i))
  let b := fun i => Nat.ceil (qThreshold 3 Q (c₃ i))
  obtain ⟨c⟩ := mixedCongruence3_has_basis (cofactorIntegerMatrix3 k₂) (cofactorIntegerMatrix3 k₃) a b
  let B := mixedCongruence3_realBasis _ _ (cofactorIntegerMatrix3_isUnit k₂)
    (cofactorIntegerMatrix3_isUnit k₃) a b c
  have hL : lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3 :=
    (mixedCongruence3_realImage_eq_lattice3 _ _ (cofactorIntegerMatrix3_isUnit k₂)
      (cofactorIntegerMatrix3_isUnit k₃) a b c).symm
  refine ⟨B, hL, ?_, (qRoundingFactor3_bounds Q c₂ c₃ hQ hc₂ hc₃).2⟩
  have h := successive_minima3_parallelepiped_volume_upper B (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
  have hvol : volume.real (parallelepipedBody3 (cofactorSourceCoordinates3 k₀ Q c₀ hQ)) =
      8 * ∏ i, Q ^ c₀ i := by
    rw [← cofactorSourceBody3_eq_parallelepiped k₀ Q c₀ hQ]
    exact cofactorSourceBody3_volume k₀ Q c₀ hQ
  have hcov : ZLattice.covolume (lattice3 B) = (qCongruenceIndex3 Q c₂ c₃ : ℝ) := by
    rw [hL]
    exact (cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.2
  rw [hvol, hcov, qCongruenceIndex3_balanced Q c₀ c₂ c₃ hQ hb] at h
  have hW : 0 < ∏ i, Q ^ c₀ i :=
    Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
  apply (mul_le_mul_right (mul_pos (by norm_num : (0 : ℝ) < 8) hW)).mp
  nlinarith
theorem cofactorSource_arch_bound (k : Fin 3) (Q : ℝ) (c : Fin 3 → ℝ)
    (hQ : 1 < Q) (x : RealTriple) (i : Fin 3) :
    |cofactorRealCoordinates3 k x i| ≤
      coordinateGauge3 (cofactorSourceCoordinates3 k Q c hQ) x * Q ^ c i := by
  have h : |cofactorSourceCoordinates3 k Q c hQ x i| ≤
      coordinateGauge3 (cofactorSourceCoordinates3 k Q c hQ) x := by
    simpa only [coordinateGauge3,Real.norm_eq_abs] using
      norm_le_pi_norm (cofactorSourceCoordinates3 k Q c hQ x) i
  change |cofactorRealCoordinates3 k x i / Q ^ c i| ≤ _ at h
  rw [abs_div,abs_of_pos (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)] at h
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)).mp h

theorem exists_cofactorSource_integer_attaining_frame
    (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    ∃ (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃),
      lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3 ∧
      LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) ∧
      (∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
        (integerTripleReal3 (u j : IntegerTriple)) =
          successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j) ∧
      Finite ((cofactorSourceLattice3 k₂ k₃ Q c₂ c₃) ⧸ Submodule.span ℤ (Set.range u)) ∧
      (Submodule.span ℤ (Set.range u)).toAddSubgroup.index ≤ 6 ∧
      (∀ i j, |cofactorRealCoordinates3 k₀ (integerTripleReal3 (u j : IntegerTriple)) i| ≤
        successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j * Q ^ c₀ i) ∧
      (∀ i j, (padicNorm 2 (cofactorForms3 k₂ i
        (fun l => ((u j : IntegerTriple) l : ℚ))) : ℝ) ≤ Q ^ c₂ i) ∧
      (∀ i j, (padicNorm 3 (cofactorForms3 k₃ i
        (fun l => ((u j : IntegerTriple) l : ℚ))) : ℝ) ≤ Q ^ c₃ i) ∧
      (∏ j, successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j) ≤
        qRoundingFactor3 Q c₂ c₃ ∧ qRoundingFactor3 Q c₂ c₃ < 216 ∧
      (∏ j, successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j) < 216 := by
  obtain ⟨B, hL, hp, hR⟩ := exists_cofactorSource_minima_upper k₀ k₂ k₃ Q c₀ c₂ c₃ hQ hc₂ hc₃ hb
  have hv := exists_successive_minima3_bounded_index B (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
  rw [hL] at hv
  obtain ⟨v, hvLI, hvAtt, hvFin, hvIndex, _⟩ := hv
  let G := cofactorSourceLattice3 k₂ k₃ Q c₂ c₃
  let u : Fin 3 → G := fun j => (integerTripleRealEquiv3 G).symm (v j)
  have huv : (fun j => integerTripleRealEquiv3 G (u j)) = v :=
    funext (fun j => (integerTripleRealEquiv3 G).apply_symm_apply (v j))
  have hcast (j : Fin 3) : integerTripleReal3 (u j : IntegerTriple) = (v j : RealTriple) :=
    integerTripleRealEquiv3_symm_apply G (v j)
  have huLI : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) := by
    simpa only [hcast] using hvLI
  have huAtt : ∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
      (integerTripleReal3 (u j : IntegerTriple)) =
        successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j := by
    simpa only [hcast] using hvAtt
  have huFin : Finite (G ⧸ Submodule.span ℤ (Set.range u)) := by
    apply (integerTripleRealEquiv3_finite_iff G u).mpr
    rw [huv]
    exact hvFin
  have huIndex : (Submodule.span ℤ (Set.range u)).toAddSubgroup.index ≤ 6 := by
    rw [integerTripleRealEquiv3_index G u, huv]
    exact hvIndex
  refine ⟨B, u, hL, huLI, huAtt, huFin, huIndex, ?_, ?_, ?_, hp, hR, hp.trans_lt hR⟩
  · intro i j
    have h := cofactorSource_arch_bound k₀ Q c₀ hQ (integerTripleReal3 (u j : IntegerTriple)) i
    rwa [huAtt j] at h
  · intro i j
    exact ((cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).1
      (u j : IntegerTriple) |>.mp (u j).property).1 i
  · intro i j
    exact ((cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).1
      (u j : IntegerTriple) |>.mp (u j).property).2 i


end
end JSP000334
