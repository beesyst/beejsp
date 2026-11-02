import SubspaceBridge.Davenport3
import SubspaceBridge.FixedDualDirection3

open scoped BigOperators Matrix
namespace JSP000334

noncomputable def gapRadius3 (l : Fin 3 → ℝ) : ℝ :=
  (l 0 * l 1 ^ 2) ^ ((1 : ℝ) / 3)

noncomputable def gapFactors3 (l : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![gapRadius3 l / l 0, gapRadius3 l / l 1, gapRadius3 l / l 1]

theorem gapRadius3_pos (l : Fin 3 → ℝ) (hl : ∀ i, 0 < l i) :
    0 < gapRadius3 l := Real.rpow_pos_of_pos (mul_pos (hl 0) (pow_pos (hl 1) 2)) _

theorem gapRadius3_cube (l : Fin 3 → ℝ) (hl : ∀ i, 0 < l i) :
    gapRadius3 l ^ 3 = l 0 * l 1 ^ 2 := by
  unfold gapRadius3
  rw [← Real.rpow_natCast, ← Real.rpow_mul (mul_pos (hl 0) (pow_pos (hl 1) 2)).le]
  norm_num

theorem gapFactors3_properties (l : Fin 3 → ℝ) (hl : ∀ i, 0 < l i)
    (h01 : l 0 ≤ l 1) (h12 : l 1 ≤ l 2) :
    (∀ i, 0 < gapFactors3 l i) ∧ (∏ i, gapFactors3 l i) = 1 ∧
    gapFactors3 l 1 ≤ gapFactors3 l 0 ∧ gapFactors3 l 2 = gapFactors3 l 1 ∧
    gapFactors3 l 0 * l 0 = gapRadius3 l ∧
    gapFactors3 l 1 * l 1 = gapRadius3 l ∧
    gapRadius3 l ≤ gapFactors3 l 2 * l 2 := by
  have hR := gapRadius3_pos l hl
  have hc := gapRadius3_cube l hl
  have h0 := (hl 0).ne'
  have h1 := (hl 1).ne'
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> exact div_pos hR (hl _)
  · simp only [Fin.prod_univ_three, gapFactors3, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]
    field_simp
    nlinarith [hc]
  · exact div_le_div_of_nonneg_left hR.le (hl 0) h01
  · exact div_mul_cancel₀ _ h0
  · exact div_mul_cancel₀ _ h1
  · change gapRadius3 l ≤ gapRadius3 l / l 1 * l 2
    calc
      _ = gapRadius3 l / l 1 * l 1 := (div_mul_cancel₀ _ h1).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h12 (div_pos hR (hl 1)).le

theorem gap_rescaled_power3 (Q c : ℝ) (hQ : 0 < Q) :
    (Q ^ (5 : ℕ)) ^ (c / 5) = Q ^ c := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
  congr 1
  ring

theorem gap_rescaled_threshold3 (p : ℕ) (Q c : ℝ) (hQ : 0 < Q) :
    qThreshold p (Q ^ (5 : ℕ)) (c / 5) = qThreshold p Q c := by
  unfold qThreshold
  rw [Real.log_pow]
  ring

theorem gap_rescaled_lattice3 (k₂ k₃ : Fin 3) (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ)
    (hQ : 0 < Q) :
    qSourceLattice3 k₂ k₃ (Q ^ (5 : ℕ)) (fun i => c₂ i / 5) (fun i => c₃ i / 5) =
      qSourceLattice3 k₂ k₃ Q c₂ c₃ := by
  unfold qSourceLattice3
  simp_rw [gap_rescaled_threshold3 _ Q _ hQ]

theorem gapRadius3_quantitative (l : Fin 3 → ℝ) (hl : ∀ i, 0 < l i)
    (Q delta : ℝ) (hQ : 0 < Q) (hprod : (∏ i, l i) < 216)
    (hgap : l 1 < l 2 * Q ^ (-delta)) :
    gapRadius3 l ^ 3 < 216 * Q ^ (-delta) ∧
      gapRadius3 l < 6 * Q ^ (-delta / 3) := by
  have hcube := gapRadius3_cube l hl
  have hp := Real.rpow_pos_of_pos hQ (-delta)
  have hmul := mul_lt_mul_of_pos_left hgap (mul_pos (hl 0) (hl 1))
  have hbound := mul_lt_mul_of_pos_right hprod hp
  rw [Fin.prod_univ_three] at hbound
  have hc : gapRadius3 l ^ 3 < 216 * Q ^ (-delta) := by
    nlinarith [hmul, hbound]
  refine ⟨hc, ?_⟩
  have he : (6 * Q ^ (-delta / 3)) ^ (3 : ℕ) = 216 * Q ^ (-delta) := by
    have hh : (Q ^ (-delta / 3)) ^ (3 : ℕ) = Q ^ (-delta) := by
      rw [← Real.rpow_mul_natCast hQ.le]
      congr 1
      ring
    rw [mul_pow, hh]
    norm_num
  have hn : 0 ≤ 6 * Q ^ (-delta / 3) := by positivity
  exact lt_of_pow_lt_pow_left₀ 3 hn (he.symm ▸ hc)

theorem gap_power_cutoff3 (delta : ℝ) (hd : 0 < delta) :
    ∃ C : ℝ, ∀ Q : ℝ, C < Q → 18432 < Q ^ (delta / 18) := by
  obtain ⟨C,hC⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < delta/18 by linarith)).eventually
      (Filter.eventually_gt_atTop 18432))
  exact ⟨C, fun Q h => hC Q h.le⟩

theorem gap_rescaled_small3 (Q delta t : ℝ) (hQ : 0 < Q)
    (hcut : 18432 < Q ^ (delta / 18))
    (ht : t < 18432 * Q ^ (-delta / 3)) :
    t < (Q ^ (5 : ℕ)) ^ (-(delta / 18)) := by
  have hp := Real.rpow_pos_of_pos hQ (-delta / 3)
  have hb := mul_lt_mul_of_pos_right hcut hp
  have he : Q ^ (delta / 18) * Q ^ (-delta / 3) =
      (Q ^ (5 : ℕ)) ^ (-(delta / 18)) := by
    rw [← Real.rpow_add hQ, ← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    congr 1
    ring
  exact ht.trans (he ▸ hb)

theorem gap_source_product3 (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (qSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hatt : ∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q c₀ hQ)
      (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j) :
    (1 : ℝ) / 6 ≤ ∏ j, successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j ∧
    (∏ j, successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j) < 216 := by
  let P := ∏ i, Q ^ c₀ i
  have hP : 0 < P := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by linarith) _)
  obtain ⟨hcov,hvol,_,hupper⟩ := sourceReal_width_geometry3 k₀ k₂ k₃ Q hQ c₂ c₃ hc₂ hc₃
    (fun i => Q ^ c₀ i) (fun i => Real.rpow_pos_of_pos (by linarith) _) B u hB hatt
  have hi : ((qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℝ) =
      P * qRoundingFactor3 Q c₂ c₃ := by
    rw [(qSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1,
      qCongruenceIndex3_balanced Q c₀ c₂ c₃ hQ hb]
  have hlow := source_minima_product_lower3 B (qSourceCoordinates3 k₀ Q c₀ hQ)
    ((qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℝ) P hP hvol hcov
  change (∏ j, successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j) * P ≤ _ at hupper
  rw [hi] at hlow hupper
  have hR := qRoundingFactor3_bounds Q c₂ c₃ hQ hc₂ hc₃
  have hlow' : qRoundingFactor3 Q c₂ c₃ / 6 ≤
      ∏ j, successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j := by
    have he : P * qRoundingFactor3 Q c₂ c₃ / (6 * P) = qRoundingFactor3 Q c₂ c₃ / 6 := by
      field_simp
      <;> ring
    rwa [he] at hlow
  refine ⟨by linarith, ?_⟩
  have hu : (∏ j, successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j) ≤
      qRoundingFactor3 Q c₂ c₃ := by nlinarith
  exact hu.trans_lt hR.2

theorem gap_integer_real_lower3 (k : Fin 3) (x : IntegerTriple) (hx : x ≠ 0) :
    ∃ i, 1 ≤ |retainedRealCoordinates3 k (integerTripleReal3 x) i| := by
  have hn : retainedIntegerMatrix3 k *ᵥ x ≠ 0 := by
    intro h
    apply hx
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    fin_cases k <;>
      simp [retainedIntegerMatrix3, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Pi.single_apply, Fin.succAbove] at h0 h1 h2
    all_goals ext i; fin_cases i <;> simp_all
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hn
  refine ⟨i, ?_⟩
  have hc : retainedRealCoordinates3 k (integerTripleReal3 x) i =
      (((retainedIntegerMatrix3 k *ᵥ x) i : ℤ) : ℝ) := by
    change (retainedRealMatrix3 k *ᵥ integerTripleReal3 x) i = _
    simp [retainedRealMatrix3, Matrix.mulVec, dotProduct, integerTripleReal3]
  rw [hc]
  exact_mod_cast Int.one_le_abs hi

theorem gap_source_first_lower3 (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₀ : ∀ i, c₀ i ≤ 1)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q c₀ hQ)
      (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j) :
    1 / Q ≤ successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) 0 := by
  have hn : (u 0 : IntegerTriple) ≠ 0 := by
    intro h
    apply hu.ne_zero 0
    rw [h, map_zero]
  obtain ⟨i,hi⟩ := gap_integer_real_lower3 k₀ (u 0) hn
  have hh := qSource_arch_bound k₀ Q c₀ hQ (integerTripleReal3 (u 0 : IntegerTriple)) i
  rw [hatt] at hh
  have hb : Q ^ c₀ i ≤ Q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hQ.le (hc₀ i)
  have hp : 0 ≤ successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) 0 := by
    rw [← hatt]
    exact norm_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hb hp
  apply (div_le_iff₀ (by linarith : 0 < Q)).mpr
  change 1 ≤ _
  nlinarith


noncomputable def gapPrimeExponent3 (p : ℕ) (Q : ℝ) (c : Fin 3 → ℝ) : ℕ :=
  Finset.univ.sup (fun i => Nat.ceil (qThreshold p Q (c i)))

noncomputable def gapLatticeScale3 (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ) : ℕ :=
  2 ^ gapPrimeExponent3 2 Q c₂ * 3 ^ gapPrimeExponent3 3 Q c₃

theorem gap_prime_power_bound3 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q)
    (c : Fin 3 → ℝ) (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 0) :
    (p : ℝ) ^ gapPrimeExponent3 p Q c < p * Q := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i => Nat.ceil (qThreshold p Q (c i)))
  change (p : ℝ) ^ Finset.univ.sup _ < _
  rw [hi, pow_ceil_factorization _ _ (by exact_mod_cast (lt_trans Nat.zero_lt_one hp)),
    qThreshold_rpow p hp Q (c i) hQ]
  have hb : Q ^ (-c i) ≤ Q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith [(hc i).1] : -c i ≤ 1)
  have hf := (ceilingFactor_bounds (p : ℝ) _ (by exact_mod_cast hp)
    (qThreshold_nonneg p hp Q (c i) hQ (hc i).2)).2
  have hm := mul_lt_mul_of_pos_left hf (Real.rpow_pos_of_pos (show 0 < Q by linarith) (-c i))
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
  have hn := mul_le_mul_of_nonneg_right hb hp0
  nlinarith

theorem gap_lattice_scale_bounds3 (Q : ℝ) (hQ : 1 < Q) (c₂ c₃ : Fin 3 → ℝ)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) :
    0 < gapLatticeScale3 Q c₂ c₃ ∧ (gapLatticeScale3 Q c₂ c₃ : ℝ) < 6 * Q ^ (2 : ℕ) := by
  have hp : 0 < gapLatticeScale3 Q c₂ c₃ := by unfold gapLatticeScale3; positivity
  refine ⟨hp, ?_⟩
  have h2 := gap_prime_power_bound3 2 (by decide) Q hQ c₂ hc₂
  have h3 := gap_prime_power_bound3 3 (by decide) Q hQ c₃ hc₃
  have hm := mul_lt_mul h2 h3.le (by positivity : 0 < (3 : ℝ) ^ gapPrimeExponent3 3 Q c₃)
    (by positivity : 0 ≤ (2 : ℝ) * Q)
  push_cast [gapLatticeScale3]
  norm_num at hm
  nlinarith

theorem gap_lattice_scale_mem3 (k₂ k₃ : Fin 3) (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ)
    (x : IntegerTriple) :
    (gapLatticeScale3 Q c₂ c₃ : ℤ) • x ∈ qSourceLattice3 k₂ k₃ Q c₂ c₃ := by
  rw [qSourceLattice3, mem_mixedCongruence3]
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

theorem gap_source_last_upper3 (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₀ : ∀ i, -1 ≤ c₀ i)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (B : Basis (Fin 3) ℝ RealTriple)
    (hB : lattice3 B = (qSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3) :
    successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) 2 ≤ 6 * Q ^ (3 : ℕ) := by
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
      gap_lattice_scale_mem3 k₂ k₃ Q c₂ c₃ _, ?_⟩
    ext i
    simp [v, d, integerTripleReal3, Pi.single_apply, Pi.basisFun_apply]
  · intro j
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    change |retainedRealCoordinates3 k₀ (v j) i / Q ^ c₀ i| ≤ _
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), div_le_iff₀
      (Real.rpow_pos_of_pos (by linarith) _)]
    have hcoeff : |retainedRealCoordinates3 k₀ ((Pi.basisFun ℝ (Fin 3)) j) i| ≤ 1 := by
      fin_cases k₀ <;> fin_cases i <;> fin_cases j <;>
        norm_num [retainedRealCoordinates3_apply, Pi.basisFun_apply, Pi.single_apply, Fin.succAbove] <;>
        split_ifs <;> norm_num
    have hb : 1 / Q ≤ Q ^ c₀ i := by
      simpa [Real.rpow_neg_one, one_div] using
        Real.rpow_le_rpow_of_exponent_le hQ.le (hc₀ i)
    have hscale : d ≤ 6 * Q ^ (2 : ℕ) := (gap_lattice_scale_bounds3 Q hQ c₂ c₃ hc₂ hc₃).2.le
    have hdiv : (6 * Q ^ (3 : ℕ)) * (1 / Q) = 6 * Q ^ (2 : ℕ) := by
      field_simp [ne_of_gt (lt_trans zero_lt_one hQ)]
      <;> ring
    have hfinal := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 6 * Q ^ (3 : ℕ))
    rw [hdiv] at hfinal
    have he : |retainedRealCoordinates3 k₀ (v j) i| ≤ d := by
      change |retainedRealCoordinates3 k₀ (d • (Pi.basisFun ℝ (Fin 3)) j) i| ≤ d
      rw [map_smul, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hd]
      nlinarith
    exact he.trans (hscale.trans hfinal)

theorem gapFactors3_bounds (l : Fin 3 → ℝ) (hl : ∀ i, 0 < l i)
    (h01 : l 0 ≤ l 1) (h12 : l 1 ≤ l 2)
    (hprod : (1 : ℝ) / 6 ≤ ∏ i, l i) (hupper : (∏ i, l i) < 216)
    (Q : ℝ) (hQ : 1 < Q) (hfirst : 1 / Q ≤ l 0)
    (hlast : l 2 ≤ 6 * Q ^ (3 : ℕ)) :
    ∀ i, 1 / (36 * Q ^ (3 : ℕ)) ≤ gapFactors3 l i ∧ gapFactors3 l i ≤ 6 * Q := by
  have hQ0 : 0 < Q := by linarith
  have hR := gapRadius3_pos l hl
  have hc := gapRadius3_cube l hl
  obtain ⟨hr,hp,hr01,hr21,he0,he1,hRs⟩ := gapFactors3_properties l hl h01 h12
  have hRc : gapRadius3 l ^ 3 < 216 := by
    rw [Fin.prod_univ_three] at hupper
    have hm := mul_le_mul_of_nonneg_left h12 (mul_pos (hl 0) (hl 1)).le
    nlinarith
  have hR6 : gapRadius3 l < 6 := lt_of_pow_lt_pow_left₀ 3 (by norm_num) (by norm_num; exact hRc)
  let s := gapFactors3 l 2 * l 2
  have hs : 0 < s := mul_pos (hr 2) (hl 2)
  have he : gapRadius3 l ^ 2 * s = ∏ i, l i := by
    rw [Fin.prod_univ_three]
    change gapRadius3 l ^ 2 * (gapRadius3 l / l 1 * l 2) = _
    calc
      _ = gapRadius3 l ^ 3 * l 2 / l 1 := by ring
      _ = _ := by rw [hc]; field_simp [(hl 1).ne'] <;> ring
  change gapRadius3 l ≤ s at hRs
  have hsq : gapRadius3 l ^ 2 ≤ s ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsq hs.le
  rw [he] at hm
  have hs6 : (1 : ℝ) / 6 ≤ s := by
    apply le_of_not_gt
    intro hslt
    have ht : s ^ (3 : ℕ) < ((1 : ℝ) / 6) ^ (3 : ℕ) :=
      pow_lt_pow_left₀ hslt hs.le (by decide)
    nlinarith
  have hlower : 1 / (36 * Q ^ (3 : ℕ)) ≤ gapFactors3 l 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 36 * Q ^ (3 : ℕ))).mpr
    have hh := mul_le_mul_of_nonneg_left hlast (hr 2).le
    change (1 : ℝ) / 6 ≤ gapFactors3 l 2 * l 2 at hs6
    nlinarith
  have hu0 : gapFactors3 l 0 ≤ 6 * Q := by
    change gapRadius3 l / l 0 ≤ _
    apply (div_le_iff₀ (hl 0)).mpr
    have hh := (div_le_iff₀ (show 0 < Q by linarith)).mp hfirst
    nlinarith
  intro i
  fin_cases i
  · exact ⟨hlower.trans (by rw [hr21]; exact hr01), hu0⟩
  · exact ⟨by simpa only [hr21] using hlower, hr01.trans hu0⟩
  · exact ⟨hlower, by change gapFactors3 l 2 ≤ _; rw [hr21]; exact hr01.trans hu0⟩

theorem gap_deformed_width_bounds3 (Q : ℝ) (hQ : 1 < Q)
    (A rho : Fin 3 → ℝ) (hA : ∀ i, 0 < A i) (hr : ∀ i, 0 < rho i)
    (hAb : ∀ i, 1 / Q ≤ A i ∧ A i ≤ Q)
    (hrb : ∀ i, 1 / (36 * Q ^ (3 : ℕ)) ≤ rho i ∧ rho i ≤ 6 * Q)
    (sigma : Equiv.Perm (Fin 3)) :
    ∀ i, 1 / (6 * Q ^ (4 : ℕ)) ≤ davenportWidths3 A rho sigma i ∧
      davenportWidths3 A rho sigma i ≤ 36 * Q ^ (4 : ℕ) ∧
      (davenportWidths3 A rho sigma i)⁻¹ ≤ 6 * Q ^ (4 : ℕ) := by
  have hQ0 : 0 < Q := by linarith
  intro i
  have hw : 0 < davenportWidths3 A rho sigma i := div_pos (hA i) (hr (sigma i))
  have hinv : (davenportWidths3 A rho sigma i)⁻¹ ≤ 6 * Q ^ (2 : ℕ) := by
    change (A i / rho (sigma i))⁻¹ ≤ _
    rw [inv_div, div_le_iff₀ (hA i)]
    have hb := (div_le_iff₀ hQ0).mp (hAb i).1
    have hm := mul_le_mul_of_nonneg_right hb (show 0 ≤ 6 * Q by positivity)
    nlinarith [(hrb (sigma i)).2]
  have hpow : Q ^ (2 : ℕ) ≤ Q ^ (4 : ℕ) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hQ.le 2
    nlinarith [mul_nonneg (sq_nonneg Q) (sub_nonneg.mpr hh)]
  have hinv4 : (davenportWidths3 A rho sigma i)⁻¹ ≤ 6 * Q ^ (4 : ℕ) := by nlinarith
  refine ⟨?_, ?_, hinv4⟩
  · apply (div_le_iff₀ (by positivity : 0 < 6 * Q ^ (4 : ℕ))).mpr
    have hh := mul_le_mul_of_nonneg_left hinv4 hw.le
    rw [mul_inv_cancel₀ hw.ne'] at hh
    nlinarith
  · change A i / rho (sigma i) ≤ _
    apply (div_le_iff₀ (hr (sigma i))).mpr
    have hb := (div_le_iff₀ (by positivity : 0 < 36 * Q ^ (3 : ℕ))).mp (hrb (sigma i)).1
    have hm := mul_le_mul_of_nonneg_right hb hQ0.le
    nlinarith [(hAb i).2]

theorem gap_source_normalization3 (Q : ℝ) (hQ : 0 < Q) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    (∏ i, Q ^ c₀ i * Q ^ c₂ i * Q ^ c₃ i) = 1 := by
  simp_rw [← Real.rpow_add hQ]
  rw [← Real.rpow_sum_of_pos hQ, hb, Real.rpow_zero]

theorem gap_deformed_normalization3 (Q : ℝ) (hQ : 0 < Q) (c₀ c₂ c₃ rho : Fin 3 → ℝ)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) (hr : (∏ i, rho i) = 1)
    (sigma : Equiv.Perm (Fin 3)) :
    (∏ i, davenportWidths3 (fun j => Q ^ c₀ j) rho sigma i *
      (Q ^ (5 : ℕ)) ^ (c₂ i / 5) * (Q ^ (5 : ℕ)) ^ (c₃ i / 5)) = 1 := by
  simp_rw [gap_rescaled_power3 Q _ hQ]
  simp only [Finset.prod_mul_distrib, davenportWidths3_product _ _ _ hr]
  simpa only [Finset.prod_mul_distrib] using gap_source_normalization3 Q hQ c₀ c₂ c₃ hb

theorem gap_width_cutoff3 (Q : ℝ) (hQ : 36 < Q) (w : ℝ) (hw : w ≤ 36 * Q ^ (4 : ℕ))
    (hi : w⁻¹ ≤ 6 * Q ^ (4 : ℕ)) : w < Q ^ (5 : ℕ) ∧ w⁻¹ < Q ^ (5 : ℕ) := by
  have hQ0 : 0 < Q := by linarith
  have hp : 0 < Q ^ (4 : ℕ) := by positivity
  constructor <;> nlinarith

theorem gap_source_integral_lattice3 (k₂ k₃ : Fin 3) (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ) :
    sourceIntegralLattice3 k₂ k₃
      (fun i => -(Nat.ceil (qThreshold 2 Q (c₂ i)) : ℤ))
      (fun i => -(Nat.ceil (qThreshold 3 Q (c₃ i)) : ℤ)) =
      qSourceLattice3 k₂ k₃ Q c₂ c₃ := by
  simp [sourceIntegralLattice3, qSourceLattice3]

theorem gap_source_davenport3 (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ)
    (c₀ c₂ c₃ : Fin 3 → ℝ) (hQ : 1 < Q)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (qSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q c₀ hQ)
      (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j)
    (hgap : successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) 1 <
      successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) 2 * Q ^ (-delta)) :
    let l := successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ)
    ∃ (hr : ∀ i, 0 < gapFactors3 l i) (sigma : Equiv.Perm (Fin 3)),
      successiveRadius3 B (davenportCoordinates3 (retainedRealCoordinates3 k₀)
        (fun i => Q ^ c₀ i) (gapFactors3 l) sigma
        (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) hr) 1 <
          18432 * Q ^ (-delta / 3) ∧
      (∀ j, gapFactors3 l j * l j / 8 ≤
        successiveRadius3 B (davenportCoordinates3 (retainedRealCoordinates3 k₀)
          (fun i => Q ^ c₀ i) (gapFactors3 l) sigma
          (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) hr) j) ∧
      ∀ j : Fin 3, ∀ z : qSourceLattice3 k₂ k₃ Q c₂ c₃,
        integerTripleReal3 (z : IntegerTriple) ∉
          minimaFlag3 (fun k => integerTripleReal3 (u k : IntegerTriple)) j →
        gapFactors3 l j * l j / 8 ≤
          coordinateGauge3 (davenportCoordinates3 (retainedRealCoordinates3 k₀)
            (fun i => Q ^ c₀ i) (gapFactors3 l) sigma
            (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) hr)
              (integerTripleReal3 (z : IntegerTriple)) := by
  intro l
  obtain ⟨_,_,_,hl,hm,_⟩ := exists_successive_minima3 B (qSourceCoordinates3 k₀ Q c₀ hQ)
  obtain ⟨hr,hprod,hr01,hr21,he0,he1,hle⟩ := gapFactors3_properties l hl hm.1 hm.2
  let f₂ := fun i => -(Nat.ceil (qThreshold 2 Q (c₂ i)) : ℤ)
  let f₃ := fun i => -(Nat.ceil (qThreshold 3 Q (c₃ i)) : ℤ)
  have hG : sourceIntegralLattice3 k₂ k₃ f₂ f₃ = qSourceLattice3 k₂ k₃ Q c₂ c₃ :=
    gap_source_integral_lattice3 k₂ k₃ Q c₂ c₃
  let ui : Fin 3 → sourceIntegralLattice3 k₂ k₃ f₂ f₃ :=
    fun j => ⟨(u j : IntegerTriple), by rw [hG]; exact (u j).property⟩
  have hBi : lattice3 B = (sourceIntegralLattice3 k₂ k₃ f₂ f₃).toIntSubmodule.map integerTripleReal3 := by
    rw [hG]; exact hB
  obtain ⟨_,sigma,hbounds,hsep⟩ := source_davenport_lemma3 k₂ k₃ f₂ f₃
    (retainedRealCoordinates3 k₀) (fun i => Q ^ c₀ i) (gapFactors3 l)
    (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) hr hprod hr01 hr21.le
    B ui hBi hu hatt (by change gapFactors3 l 0 * l 0 ≤ gapFactors3 l 1 * l 1; rw [he0,he1])
    (by change gapFactors3 l 1 * l 1 ≤ gapFactors3 l 2 * l 2; rw [he1]; exact hle)
  refine ⟨hr,sigma,?_,fun j => (hbounds j).1,?_⟩
  · have hp := (gap_source_product3 k₀ k₂ k₃ Q c₀ c₂ c₃ hQ hc₂ hc₃ hb B u hB hatt).2
    have hR := (gapRadius3_quantitative l hl Q delta (lt_trans zero_lt_one hQ) hp hgap).2
    have hd := (hbounds 1).2
    change _ ≤ 3072 * (gapFactors3 l 1 * l 1) at hd
    rw [he1] at hd
    nlinarith
  · intro j z hz
    exact hsep j ⟨(z : IntegerTriple), by rw [hG]; exact z.property⟩ hz

structure GapDeformedData3 (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ)
    (c₀ c₂ c₃ : Fin 3 → ℝ) (hQ : 1 < Q)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃) where
  sigma : Equiv.Perm (Fin 3)
  widths : Fin 3 → ℝ
  positive : ∀ i, 0 < widths i
  correspondence : widths = davenportWidths3 (fun i => Q ^ c₀ i)
    (gapFactors3 (successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ))) sigma
  bounds : ∀ i, 1 / (6 * Q ^ (4 : ℕ)) ≤ widths i ∧ widths i ≤ 36 * Q ^ (4 : ℕ)
  normalization : (∏ i, widths i * (Q ^ (5 : ℕ)) ^ (c₂ i / 5) * (Q ^ (5 : ℕ)) ^ (c₃ i / 5)) = 1
  cutoff : ∀ i, widths i < Q ^ (5 : ℕ) ∧ (widths i)⁻¹ < Q ^ (5 : ℕ)
  small : successiveRadius3 B (archCoordinates3 (retainedRealCoordinates3 k₀) widths positive) 1 <
    (Q ^ (5 : ℕ)) ^ (-(delta / 18))
  lattice_eq : lattice3 B =
    (qSourceLattice3 k₂ k₃ (Q ^ (5 : ℕ)) (fun i => c₂ i / 5) (fun i => c₃ i / 5)).toIntSubmodule.map integerTripleReal3
  frame : Fin 3 → qSourceLattice3 k₂ k₃ (Q ^ (5 : ℕ)) (fun i => c₂ i / 5) (fun i => c₃ i / 5)
  independent : LinearIndependent ℝ (fun j => integerTripleReal3 (frame j : IntegerTriple))
  attaining : ∀ j, coordinateGauge3 (archCoordinates3 (retainedRealCoordinates3 k₀) widths positive)
    (integerTripleReal3 (frame j : IntegerTriple)) =
    successiveRadius3 B (archCoordinates3 (retainedRealCoordinates3 k₀) widths positive) j
  separation : ∀ j : Fin 3, ∀ z : qSourceLattice3 k₂ k₃ Q c₂ c₃,
    integerTripleReal3 (z : IntegerTriple) ∉ minimaFlag3 (fun k => integerTripleReal3 (u k : IntegerTriple)) j →
      gapFactors3 (successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ)) j *
        successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j / 8 ≤
          coordinateGauge3 (archCoordinates3 (retainedRealCoordinates3 k₀) widths positive)
            (integerTripleReal3 (z : IntegerTriple))

theorem gap_deformed_data3 (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ)
    (c₀ c₂ c₃ : Fin 3 → ℝ) (hQ : 1 < Q) (hlarge : 36 < Q)
    (hcut : 18432 < Q ^ (delta / 18))
    (hc₀ : ∀ i, -1 ≤ c₀ i ∧ c₀ i ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (qSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q c₀ hQ)
      (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j)
    (hgap : successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) 1 <
      successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) 2 * Q ^ (-delta)) :
    Nonempty (GapDeformedData3 k₀ k₂ k₃ Q delta c₀ c₂ c₃ hQ B u) := by
  classical
  have hQ0 := lt_trans zero_lt_one hQ
  let l := successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ)
  obtain ⟨hr,sigma,hsmall,_,hsep⟩ := gap_source_davenport3 k₀ k₂ k₃ Q delta c₀ c₂ c₃ hQ
    (fun i => (hc₂ i).2) (fun i => (hc₃ i).2) hb B u hB hu hatt hgap
  let w := davenportWidths3 (fun i => Q ^ c₀ i) (gapFactors3 l) sigma
  have hw : ∀ i, 0 < w i := davenportWidths3_pos _ _ _ (fun i => Real.rpow_pos_of_pos hQ0 _) hr
  obtain ⟨_,_,_,hl,hm,_⟩ := exists_successive_minima3 B (qSourceCoordinates3 k₀ Q c₀ hQ)
  have hp := gap_source_product3 k₀ k₂ k₃ Q c₀ c₂ c₃ hQ (fun i => (hc₂ i).2) (fun i => (hc₃ i).2) hb B u hB hatt
  have hfirst := gap_source_first_lower3 k₀ k₂ k₃ Q c₀ c₂ c₃ hQ (fun i => (hc₀ i).2) B u hu hatt
  have hlast := gap_source_last_upper3 k₀ k₂ k₃ Q c₀ c₂ c₃ hQ (fun i => (hc₀ i).1) hc₂ hc₃ B hB
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
      (qSourceLattice3 k₂ k₃ (Q ^ (5 : ℕ)) (fun i => c₂ i / 5) (fun i => c₃ i / 5)).toIntSubmodule.map integerTripleReal3 := by
    rw [gap_rescaled_lattice3 k₂ k₃ Q c₂ c₃ hQ0]; exact hB
  let e := archCoordinates3 (retainedRealCoordinates3 k₀) w hw
  obtain ⟨v,hv,hvL,_,_,hvatt⟩ := exists_successive_minima3 B e
  have hex (j : Fin 3) : ∃ z : qSourceLattice3 k₂ k₃ (Q ^ (5 : ℕ)) (fun i => c₂ i / 5) (fun i => c₃ i / 5),
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

theorem gap_rescaled_weight_bounds3 (Q : ℝ) (hQ : 1 < Q)
    (c : Fin 3 → ℝ) (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 0) :
    1 < Q ^ (5 : ℕ) ∧ ∀ i, (-1 ≤ c i / 5 ∧ c i / 5 ≤ 0) ∧
      (Q ^ (5 : ℕ)) ^ (-(c i / 5)) < Q ^ (5 : ℕ) := by
  have hp : 1 < Q ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast]
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt hQ (by norm_num : (0 : ℝ) < 5)
  refine ⟨hp,fun i => ⟨⟨by linarith [(hc i).1],by linarith [(hc i).2]⟩, ?_⟩⟩
  have he : -(c i / 5) < 1 := by linarith [(hc i).1]
  simpa using Real.rpow_lt_rpow_of_exponent_lt hp he

def gapRescaledDomain3 (Omega : Set ℝ) (C : ℝ) : Set ℝ :=
  (fun Q : ℝ => Q ^ (5 : ℕ)) '' {Q | Q ∈ Omega ∧ C < Q}

theorem gapRescaledDomain3_unbounded (Omega : Set ℝ) (hOmega : ¬ BddAbove Omega) (C : ℝ) :
    ¬ BddAbove (gapRescaledDomain3 Omega C) := by
  rintro ⟨b,hb⟩
  obtain ⟨Q,hQ,hbQ⟩ := not_bddAbove_iff'.mp hOmega (max C (max 1 b))
  have hbQ' : max C (max 1 b) < Q := lt_of_not_ge hbQ
  have hCQ : C < Q := lt_of_le_of_lt (le_max_left _ _) hbQ'
  have h1 : 1 < Q := lt_of_le_of_lt ((le_max_left 1 b).trans (le_max_right C (max 1 b))) hbQ'
  have hb' : b < Q := lt_of_le_of_lt ((le_max_right 1 b).trans (le_max_right C (max 1 b))) hbQ'
  have hpow : Q ≤ Q ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le h1.le (by norm_num : (1 : ℝ) ≤ 5)
  have hh := hb (show Q ^ (5 : ℕ) ∈ gapRescaledDomain3 Omega C from ⟨Q,⟨hQ,hCQ⟩,rfl⟩)
  linarith

structure GapSatz51Family3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (Omega : Set ℝ) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → qSourceLattice3 k₂ k₃ Q.val c₂ c₃) where
  cutoff : ℝ
  domain : Set ℝ
  domain_eq : domain = gapRescaledDomain3 Omega cutoff
  unbounded : ¬ BddAbove domain
  original : domain → Omega
  parameter : ∀ t : domain, (original t).val ^ (5 : ℕ) = t.val
  large : ∀ t : domain, cutoff < (original t).val
  data : ∀ t : domain, GapDeformedData3 k₀ k₂ k₃ (original t).val delta c₀ c₂ c₃
    (hQ (original t).val (original t).property) (B (original t)) (u (original t))

theorem gap_satz51_family3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hc₀ : ∀ i, -1 ≤ c₀ i ∧ c₀ i ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (Omega : Set ℝ) (hOmega : ¬ BddAbove Omega) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → qSourceLattice3 k₂ k₃ Q.val c₂ c₃)
    (hB : ∀ Q : Omega, lattice3 (B Q) =
      (qSourceLattice3 k₂ k₃ Q.val c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : ∀ Q : Omega, LinearIndependent ℝ (fun j => integerTripleReal3 (u Q j : IntegerTriple)))
    (hatt : ∀ Q : Omega, ∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property))
      (integerTripleReal3 (u Q j : IntegerTriple)) =
      successiveRadius3 (B Q) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) j)
    (hgap : ∀ Q : Omega, successiveRadius3 (B Q) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 1 <
      successiveRadius3 (B Q) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 2 * Q.val ^ (-delta)) :
    Nonempty (GapSatz51Family3 k₀ k₂ k₃ delta c₀ c₂ c₃ Omega hQ B u) := by
  classical
  obtain ⟨C,hC⟩ := gap_power_cutoff3 delta hd
  let cut := max 36 C
  let U := gapRescaledDomain3 Omega cut
  have hex (t : U) : ∃ q : Omega, cut < q.val ∧ q.val ^ (5 : ℕ) = t.val := by
    obtain ⟨q,hq,heq⟩ := t.property
    exact ⟨⟨q,hq.1⟩,hq.2,heq⟩
  choose q hlarge hparam using hex
  have hdata (t : U) : Nonempty (GapDeformedData3 k₀ k₂ k₃ (q t).val delta c₀ c₂ c₃
      (hQ (q t).val (q t).property) (B (q t)) (u (q t))) := by
    have h36 : 36 < (q t).val := lt_of_le_of_lt (le_max_left _ _) (hlarge t)
    have hcut : C < (q t).val := lt_of_le_of_lt (le_max_right _ _) (hlarge t)
    exact gap_deformed_data3 k₀ k₂ k₃ (q t).val delta c₀ c₂ c₃ (hQ _ (q t).property)
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

theorem gap_satz51_apply3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (Omega : Set ℝ) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → qSourceLattice3 k₂ k₃ Q.val c₂ c₃)
    (F : GapSatz51Family3 k₀ k₂ k₃ delta c₀ c₂ c₃ Omega hQ B u) :
    ∃ v : IntegerTriple, v ≠ 0 ∧ ∃ U : Set ℝ, U ⊆ F.domain ∧ ¬ BddAbove U ∧
      ∀ t : F.domain, t.val ∈ U →
        Submodule.span ℚ {dualFrameVector3 (fun j => ((F.data t).frame j : IntegerTriple)) 2} =
          Submodule.span ℚ {fun i => (v i : ℚ)} := by
  classical
  let A : ℝ → Fin 3 → ℝ := fun t => if ht : t ∈ F.domain then (F.data ⟨t,ht⟩).widths else fun _ => 1
  have hAval (t : F.domain) : A t.val = (F.data t).widths := by simp [A,t.property]
  let b : F.domain → Basis (Fin 3) ℝ RealTriple := fun t => B (F.original t)
  let frame (t : F.domain) : Fin 3 → qSourceLattice3 k₂ k₃ t.val (fun i => c₂ i / 5) (fun i => c₃ i / 5) :=
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
      (qSourceLattice3 k₂ k₃ t.val (fun i => c₂ i / 5) (fun i => c₃ i / 5)).toIntSubmodule.map integerTripleReal3 := by
    intro t
    simpa only [F.parameter t] using (F.data t).lattice_eq
  have hli : ∀ t : F.domain, LinearIndependent ℝ (fun j => integerTripleReal3 (frame t j : IntegerTriple)) :=
    fun t => (F.data t).independent
  have hatt : ∀ t : F.domain, ∀ j,
      coordinateGauge3 (archCoordinates3 (retainedRealCoordinates3 k₀) (A t.val) (hA t.val t.property))
        (integerTripleReal3 (frame t j : IntegerTriple)) =
      successiveRadius3 (b t)
        (archCoordinates3 (retainedRealCoordinates3 k₀) (A t.val) (hA t.val t.property)) j := by
    intro t j
    simpa only [hAval t] using (F.data t).attaining j
  have hsmall : ∀ t : F.domain, successiveRadius3 (b t)
      (archCoordinates3 (retainedRealCoordinates3 k₀) (A t.val) (hA t.val t.property)) 1 <
        t.val ^ (-(delta / 18)) := by
    intro t
    simpa only [hAval t,F.parameter t] using (F.data t).small
  have hc₂' : ∀ i, -1 ≤ c₂ i / 5 ∧ c₂ i / 5 ≤ 0 :=
    fun i => ⟨by linarith [(hc₂ i).1],by linarith [(hc₂ i).2]⟩
  have hc₃' : ∀ i, -1 ≤ c₃ i / 5 ∧ c₃ i / 5 ≤ 0 :=
    fun i => ⟨by linarith [(hc₃ i).1],by linarith [(hc₃ i).2]⟩
  exact source_fixed_dual_direction3 k₀ k₂ k₃ (delta / 18) (by linarith)
    (fun i => c₂ i / 5) (fun i => c₃ i / 5) hc₂' hc₃' F.domain F.unbounded
    A hQt hA hcut hnorm b frame hbl hli hatt hsmall

theorem source_gap_satz51_applicable3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hc₀ : ∀ i, -1 ≤ c₀ i ∧ c₀ i ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (Omega : Set ℝ) (hOmega : ¬ BddAbove Omega) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → qSourceLattice3 k₂ k₃ Q.val c₂ c₃)
    (hB : ∀ Q : Omega, lattice3 (B Q) =
      (qSourceLattice3 k₂ k₃ Q.val c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : ∀ Q : Omega, LinearIndependent ℝ (fun j => integerTripleReal3 (u Q j : IntegerTriple)))
    (hatt : ∀ Q : Omega, ∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property))
      (integerTripleReal3 (u Q j : IntegerTriple)) =
      successiveRadius3 (B Q) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) j)
    (hgap : ∀ Q : Omega, successiveRadius3 (B Q) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 1 <
      successiveRadius3 (B Q) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 2 * Q.val ^ (-delta)) :
    ∃ F : GapSatz51Family3 k₀ k₂ k₃ delta c₀ c₂ c₃ Omega hQ B u,
      ∃ v : IntegerTriple, v ≠ 0 ∧ ∃ U : Set ℝ, U ⊆ F.domain ∧ ¬ BddAbove U ∧
        ∀ t : F.domain, t.val ∈ U →
          Submodule.span ℚ {dualFrameVector3 (fun j => ((F.data t).frame j : IntegerTriple)) 2} =
            Submodule.span ℚ {fun i => (v i : ℚ)} := by
  obtain ⟨F⟩ := gap_satz51_family3 k₀ k₂ k₃ delta hd c₀ c₂ c₃ hc₀ hc₂ hc₃ hb Omega hOmega hQ B u hB hu hatt hgap
  exact ⟨F,gap_satz51_apply3 k₀ k₂ k₃ delta hd c₀ c₂ c₃ hc₂ hc₃ Omega hQ B u F⟩

end JSP000334
