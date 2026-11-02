import SubspaceBridge.CofactorFixedDual3
import SubspaceBridge.GapTransport3
open scoped BigOperators Matrix
namespace JSP000334
noncomputable section

def cofactor_sourceIntegralLattice3 (k₂ k₃ : Fin 3) (f₂ f₃ : Fin 3 → ℤ) : AddSubgroup IntegerTriple :=
  mixedCongruence3 (cofactorIntegerMatrix3 k₂) (cofactorIntegerMatrix3 k₃)
    (fun i => (-f₂ i).toNat) (fun i => (-f₃ i).toNat)

theorem cofactor_source_davenport_lemma3 (k₂ k₃ : Fin 3) (f₂ f₃ : Fin 3 → ℤ)
    (L : RealTriple ≃ₗ[ℝ] RealTriple) (A rho : Fin 3 → ℝ)
    (hA : ∀ i, 0 < A i) (hrho : ∀ i, 0 < rho i)
    (hprod : (∏ i,rho i)=1) (hr01 : rho 1 ≤ rho 0) (hr12 : rho 2 ≤ rho 1)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactor_sourceIntegralLattice3 k₂ k₃ f₂ f₃)
    (hB : lattice3 B = (cofactor_sourceIntegralLattice3 k₂ k₃ f₂ f₃).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (archCoordinates3 L A hA) (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (archCoordinates3 L A hA) j)
    (hm01 : rho 0*successiveRadius3 B (archCoordinates3 L A hA) 0 ≤
      rho 1*successiveRadius3 B (archCoordinates3 L A hA) 1)
    (hm12 : rho 1*successiveRadius3 B (archCoordinates3 L A hA) 1 ≤
      rho 2*successiveRadius3 B (archCoordinates3 L A hA) 2) :
    dualFrameRelativeIndex3 (cofactor_sourceIntegralLattice3 k₂ k₃ f₂ f₃) u ≤ 6 ∧
    ∃ sigma : Equiv.Perm (Fin 3),
      (∀ j, rho j*successiveRadius3 B (archCoordinates3 L A hA) j/8 ≤
        successiveRadius3 B (davenportCoordinates3 L A rho sigma hA hrho) j ∧
        successiveRadius3 B (davenportCoordinates3 L A rho sigma hA hrho) j ≤
          3072*(rho j*successiveRadius3 B (archCoordinates3 L A hA) j)) ∧
      ∀ j : Fin 3, ∀ z : cofactor_sourceIntegralLattice3 k₂ k₃ f₂ f₃,
        integerTripleReal3 (z : IntegerTriple) ∉
          minimaFlag3 (fun k => integerTripleReal3 (u k : IntegerTriple)) j →
        rho j*successiveRadius3 B (archCoordinates3 L A hA) j/8 ≤
          coordinateGauge3 (davenportCoordinates3 L A rho sigma hA hrho)
            (integerTripleReal3 (z : IntegerTriple)) := by
  refine ⟨source_attaining_frame_index_le_six3 _ B _ u hB hu hatt,?_⟩
  have hmem (z : cofactor_sourceIntegralLattice3 k₂ k₃ f₂ f₃) :
      integerTripleReal3 (z : IntegerTriple) ∈ lattice3 B := by
    rw [hB]
    exact Submodule.mem_map.mpr ⟨(z : IntegerTriple),z.property,rfl⟩
  obtain ⟨sigma,hbounds,hsep⟩ := davenport_lemma3 B L A rho hA hrho hprod hr01 hr12
    (fun j => integerTripleReal3 (u j : IntegerTriple)) hu (fun j => hmem (u j)) hatt hm01 hm12
  exact ⟨sigma,hbounds,fun j z hz => hsep j _ (hmem z) hz⟩

theorem cofactor_gap_rescaled_lattice3 (k₂ k₃ : Fin 3) (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ)
    (hQ : 0 < Q) :
    cofactorSourceLattice3 k₂ k₃ (Q ^ (5 : ℕ)) (fun i => c₂ i / 5) (fun i => c₃ i / 5) =
      cofactorSourceLattice3 k₂ k₃ Q c₂ c₃ := by
  unfold cofactorSourceLattice3
  simp_rw [gap_rescaled_threshold3 _ Q _ hQ]

theorem cofactor_gap_source_product3 (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hatt : ∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
      (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j) :
    (1 : ℝ) / 6 ≤ ∏ j, successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j ∧
    (∏ j, successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j) < 216 := by
  let P := ∏ i, Q ^ c₀ i
  have hP : 0 < P := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by linarith) _)
  obtain ⟨hcov,hvol,_,hupper⟩ := cofactor_sourceReal_width_geometry3 k₀ k₂ k₃ Q hQ c₂ c₃ hc₂ hc₃
    (fun i => Q ^ c₀ i) (fun i => Real.rpow_pos_of_pos (by linarith) _) B u hB hatt
  have hi : ((cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℝ) =
      P * qRoundingFactor3 Q c₂ c₃ := by
    rw [(cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1,
      qCongruenceIndex3_balanced Q c₀ c₂ c₃ hQ hb]
  have hlow := source_minima_product_lower3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
    ((cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℝ) P hP hvol hcov
  change (∏ j, successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j) * P ≤ _ at hupper
  rw [hi] at hlow hupper
  have hR := qRoundingFactor3_bounds Q c₂ c₃ hQ hc₂ hc₃
  have hlow' : qRoundingFactor3 Q c₂ c₃ / 6 ≤
      ∏ j, successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j := by
    have he : P * qRoundingFactor3 Q c₂ c₃ / (6 * P) = qRoundingFactor3 Q c₂ c₃ / 6 := by
      field_simp
      <;> ring
    rwa [he] at hlow
  refine ⟨by linarith, ?_⟩
  have hu : (∏ j, successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j) ≤
      qRoundingFactor3 Q c₂ c₃ := by nlinarith
  exact hu.trans_lt hR.2

theorem cofactor_gap_integer_real_lower3 (k : Fin 3) (x : IntegerTriple) (hx : x ≠ 0) :
    ∃ i, 1 ≤ |cofactorRealCoordinates3 k (integerTripleReal3 x) i| := by
  have hn : cofactorIntegerMatrix3 k *ᵥ x ≠ 0 := by
    intro h
    apply hx
    have hi : (cofactorIntegerMatrix3 k)⁻¹ * cofactorIntegerMatrix3 k = 1 :=
      Matrix.nonsing_inv_mul _ (by rw [cofactorIntegerMatrix3_det]; exact isUnit_one)
    have hh : (cofactorIntegerMatrix3 k)⁻¹ *ᵥ (cofactorIntegerMatrix3 k *ᵥ x) =
        (cofactorIntegerMatrix3 k)⁻¹ *ᵥ (0 : IntegerTriple) := by
      exact congrArg (fun z : IntegerTriple => (cofactorIntegerMatrix3 k)⁻¹ *ᵥ z) h
    simpa only [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec, Matrix.mulVec_zero] using hh
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hn
  refine ⟨i, ?_⟩
  have hc : cofactorRealCoordinates3 k (integerTripleReal3 x) i =
      (((cofactorIntegerMatrix3 k *ᵥ x) i : ℤ) : ℝ) := by
    change (cofactorRealMatrix3 k *ᵥ integerTripleReal3 x) i = _
    simp [cofactorRealMatrix3, Matrix.mulVec, dotProduct, integerTripleReal3]
  rw [hc]
  exact_mod_cast Int.one_le_abs hi

theorem cofactor_gap_source_first_lower3 (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₀ : ∀ i, c₀ i ≤ 1)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
      (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j) :
    1 / Q ≤ successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) 0 := by
  have hn : (u 0 : IntegerTriple) ≠ 0 := by
    intro h
    apply hu.ne_zero 0
    rw [h, map_zero]
  obtain ⟨i,hi⟩ := cofactor_gap_integer_real_lower3 k₀ (u 0) hn
  have hh := cofactorSource_arch_bound k₀ Q c₀ hQ (integerTripleReal3 (u 0 : IntegerTriple)) i
  rw [hatt] at hh
  have hb : Q ^ c₀ i ≤ Q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hQ.le (hc₀ i)
  have hp : 0 ≤ successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) 0 := by
    rw [← hatt]
    exact norm_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hb hp
  apply (div_le_iff₀ (by linarith : 0 < Q)).mpr
  change 1 ≤ _
  nlinarith

theorem cofactor_gap_lattice_scale_mem3 (k₂ k₃ : Fin 3) (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ)
    (x : IntegerTriple) :
    (gapLatticeScale3 Q c₂ c₃ : ℤ) • x ∈ cofactorSourceLattice3 k₂ k₃ Q c₂ c₃ := by
  rw [cofactorSourceLattice3, mem_mixedCongruence3]
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro i
    apply dvd_mul_of_dvd_left
    have hd : (2 : ℤ) ^ Nat.ceil (qThreshold 2 Q (c₂ i)) ∣
        (2 : ℤ) ^ gapPrimeExponent3 2 Q c₂ :=
      pow_dvd_pow _ (Finset.le_sup (f := fun j => Nat.ceil (qThreshold 2 Q (c₂ j))) (Finset.mem_univ i))
    exact hd.trans (by simp [gapLatticeScale3])
  · intro i
    apply dvd_mul_of_dvd_left
    have hd : (3 : ℤ) ^ Nat.ceil (qThreshold 3 Q (c₃ i)) ∣
        (3 : ℤ) ^ gapPrimeExponent3 3 Q c₃ :=
      pow_dvd_pow _ (Finset.le_sup (f := fun j => Nat.ceil (qThreshold 3 Q (c₃ j))) (Finset.mem_univ i))
    exact hd.trans (by simp [gapLatticeScale3])

theorem cofactor_gap_source_last_upper3 (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₀ : ∀ i, -1 ≤ c₀ i)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (B : Basis (Fin 3) ℝ RealTriple)
    (hB : lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3) :
    successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) 2 ≤ 6 * Q ^ (3 : ℕ) := by
  let d : ℝ := gapLatticeScale3 Q c₂ c₃
  have hd : 0 < d := by
    change 0 < (gapLatticeScale3 Q c₂ c₃ : ℝ)
    exact_mod_cast (gap_lattice_scale_bounds3 Q hQ c₂ c₃ hc₂ hc₃).1
  let v : Fin 3 → RealTriple := fun j => d • (Pi.basisFun ℝ (Fin 3)) j
  have hv : LinearIndependent ℝ v := by
    have hh := (Pi.basisFun ℝ (Fin 3)).linearIndependent.units_smul
      (fun _ => Units.mk0 d hd.ne')
    change LinearIndependent ℝ (fun j => d • (Pi.basisFun ℝ (Fin 3)) j) at hh
    exact hh
  apply successiveRadius3_le_family B _ 2 v hv
  · intro j
    rw [hB]
    refine Submodule.mem_map.mpr ⟨(gapLatticeScale3 Q c₂ c₃ : ℤ) • Pi.single j 1,
      cofactor_gap_lattice_scale_mem3 k₂ k₃ Q c₂ c₃ _, ?_⟩
    ext i
    simp [v, d, integerTripleReal3, Pi.single_apply, Pi.basisFun_apply]
  · intro j
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    change |cofactorRealCoordinates3 k₀ (v j) i / Q ^ c₀ i| ≤ _
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), div_le_iff₀
      (Real.rpow_pos_of_pos (by linarith) _)]
    have hcoeff : |cofactorRealCoordinates3 k₀ ((Pi.basisFun ℝ (Fin 3)) j) i| ≤ 1 := by
      change |(cofactorRealMatrix3 k₀ *ᵥ ((Pi.basisFun ℝ (Fin 3)) j)) i| ≤ 1
      rw [Pi.basisFun_apply,Matrix.mulVec_single_one]
      change |((cofactorIntegerMatrix3 k₀ i j : ℤ) : ℝ)| ≤ 1
      fin_cases k₀ <;> fin_cases i <;> fin_cases j <;>
        norm_num [cofactorIntegerMatrix3_table,
          Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    have hb : 1 / Q ≤ Q ^ c₀ i := by
      simpa [Real.rpow_neg_one, one_div] using
        Real.rpow_le_rpow_of_exponent_le hQ.le (hc₀ i)
    have hscale : d ≤ 6 * Q ^ (2 : ℕ) := (gap_lattice_scale_bounds3 Q hQ c₂ c₃ hc₂ hc₃).2.le
    have hdiv : (6 * Q ^ (3 : ℕ)) * (1 / Q) = 6 * Q ^ (2 : ℕ) := by
      field_simp [ne_of_gt (lt_trans zero_lt_one hQ)]
      <;> ring
    have hfinal := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 6 * Q ^ (3 : ℕ))
    rw [hdiv] at hfinal
    have he : |cofactorRealCoordinates3 k₀ (v j) i| ≤ d := by
      change |cofactorRealCoordinates3 k₀ (d • (Pi.basisFun ℝ (Fin 3)) j) i| ≤ d
      rw [map_smul, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hd]
      nlinarith
    exact he.trans (hscale.trans hfinal)

theorem cofactor_gap_source_integral_lattice3 (k₂ k₃ : Fin 3) (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ) :
    cofactor_sourceIntegralLattice3 k₂ k₃
      (fun i => -(Nat.ceil (qThreshold 2 Q (c₂ i)) : ℤ))
      (fun i => -(Nat.ceil (qThreshold 3 Q (c₃ i)) : ℤ)) =
      cofactorSourceLattice3 k₂ k₃ Q c₂ c₃ := by
  simp [cofactor_sourceIntegralLattice3, cofactorSourceLattice3]

theorem cofactor_gap_source_davenport3 (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ)
    (c₀ c₂ c₃ : Fin 3 → ℝ) (hQ : 1 < Q)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
      (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j)
    (hgap : successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) 1 <
      successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) 2 * Q ^ (-delta)) :
    let l := successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
    ∃ (hr : ∀ i, 0 < gapFactors3 l i) (sigma : Equiv.Perm (Fin 3)),
      successiveRadius3 B (davenportCoordinates3 (cofactorRealCoordinates3 k₀)
        (fun i => Q ^ c₀ i) (gapFactors3 l) sigma
        (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) hr) 1 <
          18432 * Q ^ (-delta / 3) ∧
      (∀ j, gapFactors3 l j * l j / 8 ≤
        successiveRadius3 B (davenportCoordinates3 (cofactorRealCoordinates3 k₀)
          (fun i => Q ^ c₀ i) (gapFactors3 l) sigma
          (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) hr) j) ∧
      ∀ j : Fin 3, ∀ z : cofactorSourceLattice3 k₂ k₃ Q c₂ c₃,
        integerTripleReal3 (z : IntegerTriple) ∉
          minimaFlag3 (fun k => integerTripleReal3 (u k : IntegerTriple)) j →
        gapFactors3 l j * l j / 8 ≤
          coordinateGauge3 (davenportCoordinates3 (cofactorRealCoordinates3 k₀)
            (fun i => Q ^ c₀ i) (gapFactors3 l) sigma
            (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) hr)
              (integerTripleReal3 (z : IntegerTriple)) := by
  intro l
  obtain ⟨_,_,_,hl,hm,_⟩ := exists_successive_minima3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
  obtain ⟨hr,hprod,hr01,hr21,he0,he1,hle⟩ := gapFactors3_properties l hl hm.1 hm.2
  let f₂ := fun i => -(Nat.ceil (qThreshold 2 Q (c₂ i)) : ℤ)
  let f₃ := fun i => -(Nat.ceil (qThreshold 3 Q (c₃ i)) : ℤ)
  have hG : cofactor_sourceIntegralLattice3 k₂ k₃ f₂ f₃ = cofactorSourceLattice3 k₂ k₃ Q c₂ c₃ :=
    cofactor_gap_source_integral_lattice3 k₂ k₃ Q c₂ c₃
  let ui : Fin 3 → cofactor_sourceIntegralLattice3 k₂ k₃ f₂ f₃ :=
    fun j => ⟨(u j : IntegerTriple), by rw [hG]; exact (u j).property⟩
  have hBi : lattice3 B = (cofactor_sourceIntegralLattice3 k₂ k₃ f₂ f₃).toIntSubmodule.map integerTripleReal3 := by
    rw [hG]; exact hB
  obtain ⟨_,sigma,hbounds,hsep⟩ := cofactor_source_davenport_lemma3 k₂ k₃ f₂ f₃
    (cofactorRealCoordinates3 k₀) (fun i => Q ^ c₀ i) (gapFactors3 l)
    (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) hr hprod hr01 hr21.le
    B ui hBi hu hatt (by change gapFactors3 l 0 * l 0 ≤ gapFactors3 l 1 * l 1; rw [he0,he1])
    (by change gapFactors3 l 1 * l 1 ≤ gapFactors3 l 2 * l 2; rw [he1]; exact hle)
  refine ⟨hr,sigma,?_,fun j => (hbounds j).1,?_⟩
  · have hp := (cofactor_gap_source_product3 k₀ k₂ k₃ Q c₀ c₂ c₃ hQ hc₂ hc₃ hb B u hB hatt).2
    have hR := (gapRadius3_quantitative l hl Q delta (lt_trans zero_lt_one hQ) hp hgap).2
    have hd := (hbounds 1).2
    change _ ≤ 3072 * (gapFactors3 l 1 * l 1) at hd
    rw [he1] at hd
    nlinarith
  · intro j z hz
    exact hsep j ⟨(z : IntegerTriple), by rw [hG]; exact z.property⟩ hz

structure cofactor_GapDeformedData3 (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ)
    (c₀ c₂ c₃ : Fin 3 → ℝ) (hQ : 1 < Q)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃) where
  sigma : Equiv.Perm (Fin 3)
  widths : Fin 3 → ℝ
  positive : ∀ i, 0 < widths i
  correspondence : widths = davenportWidths3 (fun i => Q ^ c₀ i)
    (gapFactors3 (successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ))) sigma
  bounds : ∀ i, 1 / (6 * Q ^ (4 : ℕ)) ≤ widths i ∧ widths i ≤ 36 * Q ^ (4 : ℕ)
  normalization : (∏ i, widths i * (Q ^ (5 : ℕ)) ^ (c₂ i / 5) * (Q ^ (5 : ℕ)) ^ (c₃ i / 5)) = 1
  cutoff : ∀ i, widths i < Q ^ (5 : ℕ) ∧ (widths i)⁻¹ < Q ^ (5 : ℕ)
  small : successiveRadius3 B (archCoordinates3 (cofactorRealCoordinates3 k₀) widths positive) 1 <
    (Q ^ (5 : ℕ)) ^ (-(delta / 18))
  lattice_eq : lattice3 B =
    (cofactorSourceLattice3 k₂ k₃ (Q ^ (5 : ℕ)) (fun i => c₂ i / 5) (fun i => c₃ i / 5)).toIntSubmodule.map integerTripleReal3
  frame : Fin 3 → cofactorSourceLattice3 k₂ k₃ (Q ^ (5 : ℕ)) (fun i => c₂ i / 5) (fun i => c₃ i / 5)
  independent : LinearIndependent ℝ (fun j => integerTripleReal3 (frame j : IntegerTriple))
  attaining : ∀ j, coordinateGauge3 (archCoordinates3 (cofactorRealCoordinates3 k₀) widths positive)
    (integerTripleReal3 (frame j : IntegerTriple)) =
    successiveRadius3 B (archCoordinates3 (cofactorRealCoordinates3 k₀) widths positive) j
  separation : ∀ j : Fin 3, ∀ z : cofactorSourceLattice3 k₂ k₃ Q c₂ c₃,
    integerTripleReal3 (z : IntegerTriple) ∉ minimaFlag3 (fun k => integerTripleReal3 (u k : IntegerTriple)) j →
      gapFactors3 (successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ)) j *
        successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j / 8 ≤
          coordinateGauge3 (archCoordinates3 (cofactorRealCoordinates3 k₀) widths positive)
            (integerTripleReal3 (z : IntegerTriple))

theorem cofactor_gap_deformed_data3 (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ)
    (c₀ c₂ c₃ : Fin 3 → ℝ) (hQ : 1 < Q) (hlarge : 36 < Q)
    (hcut : 18432 < Q ^ (delta / 18))
    (hc₀ : ∀ i, -1 ≤ c₀ i ∧ c₀ i ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
      (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j)
    (hgap : successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) 1 <
      successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) 2 * Q ^ (-delta)) :
    Nonempty (cofactor_GapDeformedData3 k₀ k₂ k₃ Q delta c₀ c₂ c₃ hQ B u) := by
  classical
  have hQ0 := lt_trans zero_lt_one hQ
  let l := successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
  obtain ⟨hr,sigma,hsmall,_,hsep⟩ := cofactor_gap_source_davenport3 k₀ k₂ k₃ Q delta c₀ c₂ c₃ hQ
    (fun i => (hc₂ i).2) (fun i => (hc₃ i).2) hb B u hB hu hatt hgap
  let w := davenportWidths3 (fun i => Q ^ c₀ i) (gapFactors3 l) sigma
  have hw : ∀ i, 0 < w i := davenportWidths3_pos _ _ _ (fun i => Real.rpow_pos_of_pos hQ0 _) hr
  obtain ⟨_,_,_,hl,hm,_⟩ := exists_successive_minima3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
  have hp := cofactor_gap_source_product3 k₀ k₂ k₃ Q c₀ c₂ c₃ hQ (fun i => (hc₂ i).2) (fun i => (hc₃ i).2) hb B u hB hatt
  have hfirst := cofactor_gap_source_first_lower3 k₀ k₂ k₃ Q c₀ c₂ c₃ hQ (fun i => (hc₀ i).2) B u hu hatt
  have hlast := cofactor_gap_source_last_upper3 k₀ k₂ k₃ Q c₀ c₂ c₃ hQ (fun i => (hc₀ i).1) hc₂ hc₃ B hB
  have hrb := gapFactors3_bounds l hl hm.1 hm.2 hp.1 hp.2 Q hQ hfirst hlast
  have hAb : ∀ i, 1 / Q ≤ Q ^ c₀ i ∧ Q ^ c₀ i ≤ Q := by
    intro i
    constructor
    · simpa [Real.rpow_neg_one, one_div] using Real.rpow_le_rpow_of_exponent_le hQ.le (hc₀ i).1
    · simpa using Real.rpow_le_rpow_of_exponent_le hQ.le (hc₀ i).2
  have hwb := gap_deformed_width_bounds3 Q hQ (fun i => Q ^ c₀ i) (gapFactors3 l)
    (fun i => Real.rpow_pos_of_pos hQ0 _) hr hAb hrb sigma
  have hprod := (gapFactors3_properties l hl hm.1 hm.2).2.1
  have hL : lattice3 B =
      (cofactorSourceLattice3 k₂ k₃ (Q ^ (5 : ℕ)) (fun i => c₂ i / 5) (fun i => c₃ i / 5)).toIntSubmodule.map integerTripleReal3 := by
    rw [cofactor_gap_rescaled_lattice3 k₂ k₃ Q c₂ c₃ hQ0]; exact hB
  let e := archCoordinates3 (cofactorRealCoordinates3 k₀) w hw
  obtain ⟨v,hv,hvL,_,_,hvatt⟩ := exists_successive_minima3 B e
  have hex (j : Fin 3) : ∃ z : cofactorSourceLattice3 k₂ k₃ (Q ^ (5 : ℕ)) (fun i => c₂ i / 5) (fun i => c₃ i / 5),
      integerTripleReal3 (z : IntegerTriple) = v j := by
    have hh := hvL j
    rw [hL] at hh
    obtain ⟨z,hz,hzv⟩ := Submodule.mem_map.mp hh
    exact ⟨⟨z,hz⟩,hzv⟩
  choose z hz using hex
  refine ⟨{
    sigma := sigma
    widths := w
    positive := hw
    correspondence := rfl
    bounds := fun i => ⟨(hwb i).1,(hwb i).2.1⟩
    normalization := gap_deformed_normalization3 Q hQ0 c₀ c₂ c₃ (gapFactors3 l) hb hprod sigma
    cutoff := fun i => gap_width_cutoff3 Q hlarge (w i) (hwb i).2.1 (hwb i).2.2
    small := gap_rescaled_small3 Q delta _ hQ0 hcut hsmall
    lattice_eq := hL
    frame := z
    independent := ?_
    attaining := ?_
    separation := hsep }⟩
  · have heq : (fun j => integerTripleReal3 (z j : IntegerTriple)) = v := funext hz
    rw [heq]; exact hv
  · intro j
    rw [hz]
    exact hvatt j

structure cofactor_GapSatz51Family3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (Omega : Set ℝ) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → cofactorSourceLattice3 k₂ k₃ Q.val c₂ c₃) where
  cutoff : ℝ
  domain : Set ℝ
  domain_eq : domain = gapRescaledDomain3 Omega cutoff
  unbounded : ¬ BddAbove domain
  original : domain → Omega
  parameter : ∀ t : domain, (original t).val ^ (5 : ℕ) = t.val
  large : ∀ t : domain, cutoff < (original t).val
  data : ∀ t : domain, cofactor_GapDeformedData3 k₀ k₂ k₃ (original t).val delta c₀ c₂ c₃
    (hQ (original t).val (original t).property) (B (original t)) (u (original t))

theorem cofactor_gap_satz51_family3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hc₀ : ∀ i, -1 ≤ c₀ i ∧ c₀ i ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (Omega : Set ℝ) (hOmega : ¬ BddAbove Omega) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → cofactorSourceLattice3 k₂ k₃ Q.val c₂ c₃)
    (hB : ∀ Q : Omega, lattice3 (B Q) =
      (cofactorSourceLattice3 k₂ k₃ Q.val c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : ∀ Q : Omega, LinearIndependent ℝ (fun j => integerTripleReal3 (u Q j : IntegerTriple)))
    (hatt : ∀ Q : Omega, ∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property))
      (integerTripleReal3 (u Q j : IntegerTriple)) =
      successiveRadius3 (B Q) (cofactorSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) j)
    (hgap : ∀ Q : Omega, successiveRadius3 (B Q) (cofactorSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 1 <
      successiveRadius3 (B Q) (cofactorSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 2 * Q.val ^ (-delta)) :
    Nonempty (cofactor_GapSatz51Family3 k₀ k₂ k₃ delta c₀ c₂ c₃ Omega hQ B u) := by
  classical
  obtain ⟨C,hC⟩ := gap_power_cutoff3 delta hd
  let cut := max 36 C
  let U := gapRescaledDomain3 Omega cut
  have hex (t : U) : ∃ q : Omega, cut < q.val ∧ q.val ^ (5 : ℕ) = t.val := by
    obtain ⟨q,hq,heq⟩ := t.property
    exact ⟨⟨q,hq.1⟩,hq.2,heq⟩
  choose q hlarge hparam using hex
  have hdata (t : U) : Nonempty (cofactor_GapDeformedData3 k₀ k₂ k₃ (q t).val delta c₀ c₂ c₃
      (hQ (q t).val (q t).property) (B (q t)) (u (q t))) := by
    have h36 : 36 < (q t).val := lt_of_le_of_lt (le_max_left _ _) (hlarge t)
    have hcut : C < (q t).val := lt_of_le_of_lt (le_max_right _ _) (hlarge t)
    exact cofactor_gap_deformed_data3 k₀ k₂ k₃ (q t).val delta c₀ c₂ c₃ (hQ _ (q t).property)
      h36 (hC _ hcut) hc₀ hc₂ hc₃ hb (B (q t)) (u (q t)) (hB (q t)) (hu (q t))
      (hatt (q t)) (hgap (q t))
  exact ⟨{
    cutoff := cut
    domain := U
    domain_eq := rfl
    unbounded := gapRescaledDomain3_unbounded Omega hOmega cut
    original := q
    parameter := hparam
    large := hlarge
    data := fun t => Classical.choice (hdata t) }⟩

theorem cofactor_gap_satz51_apply3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (Omega : Set ℝ) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → cofactorSourceLattice3 k₂ k₃ Q.val c₂ c₃)
    (F : cofactor_GapSatz51Family3 k₀ k₂ k₃ delta c₀ c₂ c₃ Omega hQ B u) :
    ∃ v : IntegerTriple, v ≠ 0 ∧ ∃ U : Set ℝ, U ⊆ F.domain ∧ ¬ BddAbove U ∧
      ∀ t : F.domain, t.val ∈ U →
        Submodule.span ℚ {dualFrameVector3 (fun j => ((F.data t).frame j : IntegerTriple)) 2} =
          Submodule.span ℚ {fun i => (v i : ℚ)} := by
  classical
  let A : ℝ → Fin 3 → ℝ := fun t => if ht : t ∈ F.domain then (F.data ⟨t,ht⟩).widths else fun _ => 1
  have hAval (t : F.domain) : A t.val = (F.data t).widths := by simp [A,t.property]
  let b : F.domain → Basis (Fin 3) ℝ RealTriple := fun t => B (F.original t)
  let frame (t : F.domain) : Fin 3 → cofactorSourceLattice3 k₂ k₃ t.val (fun i => c₂ i / 5) (fun i => c₃ i / 5) :=
    fun j => ⟨((F.data t).frame j : IntegerTriple), by
      have hp := ((F.data t).frame j).property
      simpa only [F.parameter t] using hp⟩
  have hQt : ∀ t ∈ F.domain, 1 < t := by
    intro t ht
    have hh := (gap_rescaled_weight_bounds3 (F.original ⟨t,ht⟩).val
      (hQ _ (F.original ⟨t,ht⟩).property) c₂ hc₂).1
    simpa only [F.parameter ⟨t,ht⟩] using hh
  have hA : ∀ t ∈ F.domain, ∀ i, 0 < A t i := by
    intro t ht i
    rw [hAval ⟨t,ht⟩]
    exact (F.data ⟨t,ht⟩).positive i
  have hcut : ∀ t ∈ F.domain, ∀ i, A t i < t ∧ (A t i)⁻¹ < t := by
    intro t ht i
    rw [hAval ⟨t,ht⟩]
    simpa only [F.parameter ⟨t,ht⟩] using (F.data ⟨t,ht⟩).cutoff i
  have hnorm : ∀ t ∈ F.domain, (∏ i, A t i * t ^ (c₂ i / 5) * t ^ (c₃ i / 5)) = 1 := by
    intro t ht
    rw [hAval ⟨t,ht⟩]
    simpa only [F.parameter ⟨t,ht⟩] using (F.data ⟨t,ht⟩).normalization
  have hbl : ∀ t : F.domain, lattice3 (b t) =
      (cofactorSourceLattice3 k₂ k₃ t.val (fun i => c₂ i / 5) (fun i => c₃ i / 5)).toIntSubmodule.map integerTripleReal3 := by
    intro t
    simpa only [F.parameter t] using (F.data t).lattice_eq
  have hli : ∀ t : F.domain, LinearIndependent ℝ (fun j => integerTripleReal3 (frame t j : IntegerTriple)) :=
    fun t => (F.data t).independent
  have hatt : ∀ t : F.domain, ∀ j,
      coordinateGauge3 (archCoordinates3 (cofactorRealCoordinates3 k₀) (A t.val) (hA t.val t.property))
        (integerTripleReal3 (frame t j : IntegerTriple)) =
      successiveRadius3 (b t)
        (archCoordinates3 (cofactorRealCoordinates3 k₀) (A t.val) (hA t.val t.property)) j := by
    intro t j
    simpa only [hAval t] using (F.data t).attaining j
  have hsmall : ∀ t : F.domain, successiveRadius3 (b t)
      (archCoordinates3 (cofactorRealCoordinates3 k₀) (A t.val) (hA t.val t.property)) 1 <
        t.val ^ (-(delta / 18)) := by
    intro t
    simpa only [hAval t,F.parameter t] using (F.data t).small
  have hc₂' : ∀ i, -1 ≤ c₂ i / 5 ∧ c₂ i / 5 ≤ 0 :=
    fun i => ⟨by linarith [(hc₂ i).1],by linarith [(hc₂ i).2]⟩
  have hc₃' : ∀ i, -1 ≤ c₃ i / 5 ∧ c₃ i / 5 ≤ 0 :=
    fun i => ⟨by linarith [(hc₃ i).1],by linarith [(hc₃ i).2]⟩
  exact cofactor_source_fixed_dual_direction3 k₀ k₂ k₃ (delta / 18) (by linarith)
    (fun i => c₂ i / 5) (fun i => c₃ i / 5) hc₂' hc₃' F.domain F.unbounded
    A hQt hA hcut hnorm b frame hbl hli hatt hsmall

theorem cofactor_source_gap_satz51_applicable3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hc₀ : ∀ i, -1 ≤ c₀ i ∧ c₀ i ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (Omega : Set ℝ) (hOmega : ¬ BddAbove Omega) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → cofactorSourceLattice3 k₂ k₃ Q.val c₂ c₃)
    (hB : ∀ Q : Omega, lattice3 (B Q) =
      (cofactorSourceLattice3 k₂ k₃ Q.val c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : ∀ Q : Omega, LinearIndependent ℝ (fun j => integerTripleReal3 (u Q j : IntegerTriple)))
    (hatt : ∀ Q : Omega, ∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property))
      (integerTripleReal3 (u Q j : IntegerTriple)) =
      successiveRadius3 (B Q) (cofactorSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) j)
    (hgap : ∀ Q : Omega, successiveRadius3 (B Q) (cofactorSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 1 <
      successiveRadius3 (B Q) (cofactorSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 2 * Q.val ^ (-delta)) :
    ∃ F : cofactor_GapSatz51Family3 k₀ k₂ k₃ delta c₀ c₂ c₃ Omega hQ B u,
      ∃ v : IntegerTriple, v ≠ 0 ∧ ∃ U : Set ℝ, U ⊆ F.domain ∧ ¬ BddAbove U ∧
        ∀ t : F.domain, t.val ∈ U →
          Submodule.span ℚ {dualFrameVector3 (fun j => ((F.data t).frame j : IntegerTriple)) 2} =
            Submodule.span ℚ {fun i => (v i : ℚ)} := by
  obtain ⟨F⟩ := cofactor_gap_satz51_family3 k₀ k₂ k₃ delta hd c₀ c₂ c₃ hc₀ hc₂ hc₃ hb Omega hOmega hQ B u hB hu hatt hgap
  exact ⟨F,cofactor_gap_satz51_apply3 k₀ k₂ k₃ delta hd c₀ c₂ c₃ hc₂ hc₃ Omega hQ B u F⟩

end
end JSP000334
