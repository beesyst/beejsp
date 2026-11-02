import SubspaceBridge.SourceSupport10
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary10.SourceBalance10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10 SourceExpansion10 SourceSupport10

variable {K : Type*} [Field K] [CharZero K]
theorem chart_block_weight {m : ℕ} (B : Matrix (Fin 10) (Fin 10) K)
    (h : Fin m) (u : Vars10 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars10 m => if v.1 = h then 1 else 0)
      (linearChart B u) (if u.1 = h then 1 else 0) := by
  unfold linearChart
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro j hj
  simpa only [zero_add] using
    (MvPolynomial.isWeightedHomogeneous_C _ (B u.2 j)).mul
      (MvPolynomial.isWeightedHomogeneous_X K (fun v : Vars10 m => if v.1 = h then 1 else 0) (u.1,j))

theorem expansion_block_weight {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 10) (Fin 10) K) (J : Vars10 m →₀ ℕ)
    (P : MvPolynomial (Vars10 m) ℤ) (hP : homogeneous10 r P) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars10 m => if v.1 = h then 1 else 0)
      (expansion L J P) (r h - ∑ j : Fin 10, J (h,j)) := by
  classical
  let Q := derivative10 J (P.map (Int.castRingHom K))
  let w := fun v : Vars10 m => if v.1 = h then 1 else 0
  have hdegree (d : Vars10 m →₀ ℕ) (hd : d ∈ Q.support) :
      (∑ j : Fin 10, d (h,j)) = r h - ∑ j : Fin 10, J (h,j) := by
    have hcoeff : P.coeff (d + J) ≠ 0 := by
      intro hz
      have hn := MvPolynomial.mem_support_iff.mp hd
      rw [derivative10_coeff, MvPolynomial.coeff_map, hz, map_zero, zero_mul] at hn
      exact hn rfl
    have hh := hP (d + J) (MvPolynomial.mem_support_iff.mpr hcoeff) h
    simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hh
    omega
  change MvPolynomial.IsWeightedHomogeneous w
    (MvPolynomial.eval₂Hom MvPolynomial.C
      (linearChart (L)⁻¹) Q) _
  conv_lhs => arg 2; rw [MvPolynomial.as_sum Q]
  rw [map_sum]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp)]
  have hw : (∑ u : Vars10 m, d u * w u) = ∑ j : Fin 10, d (h,j) := by
    have he := rothAux_weight_block d h
    rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun u (n : ℕ) => n • w u) (by intro u; simp)] at he
    simpa only [nsmul_eq_mul, Nat.cast_id, w] using he
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun u : Vars10 m => linearChart (L)⁻¹ u ^ d u)
    (fun u => d u * w u)
    (fun u _ => by simpa only [nsmul_eq_mul] using
      (chart_block_weight (L)⁻¹ h u).pow (d u))
  simpa only [zero_add, hw, hdegree d hd] using
    (MvPolynomial.isWeightedHomogeneous_C w (Q.coeff d)).mul hprod

theorem expansion_block_degree {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 10) (Fin 10) K) (J : Vars10 m →₀ ℕ)
    (P : MvPolynomial (Vars10 m) ℤ) (hP : homogeneous10 r P)
    (b : Vars10 m →₀ ℕ) (hb : (expansion L J P).coeff b ≠ 0) (h : Fin m) :
    (∑ j : Fin 10, b (h,j)) = r h - ∑ j : Fin 10, J (h,j) := by
  have hw := expansion_block_weight r L J P hP h hb
  rwa [rothAux_weight_block] at hw

theorem total_coordinate_weight_le {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (L : Matrix (Fin 10) (Fin 10) K) (J : Vars10 m →₀ ℕ)
    (P : MvPolynomial (Vars10 m) ℤ) (hP : homogeneous10 r P)
    (b : Vars10 m →₀ ℕ) (hb : (expansion L J P).coeff b ≠ 0) :
    (∑ i : Fin 10, coordinateWeight r i b) ≤ (m : ℝ) := by
  unfold coordinateWeight
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ h : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [← Finset.sum_div]
      have hrh : (0 : ℝ) < r h := by exact_mod_cast hr h
      apply (div_le_one hrh).mpr
      have hdeg := expansion_block_degree r L J P hP b hb h
      exact_mod_cast (show (∑ i : Fin 10, b (h,i)) ≤ r h by omega)
    _ = _ := by simp




theorem balance_from_weights (m : ℕ) (eta : ℝ) (heta : 0 ≤ eta)
    (x : Fin 10 → ℝ) (hsum : (∑ i, x i) ≤ m)
    (hlower : ∀ i, (m : ℝ)/10 - 3*eta*m ≤ x i) :
    ∀ i, |x i - (m : ℝ)/10| ≤ 54*eta*m := by
  intro i
  have hc : (Finset.univ.erase i : Finset (Fin 10)).card = 9 := by simp
  have ho := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ => hlower j)
  have ho' : 9*((m : ℝ)/10 - 3*eta*m) ≤ ∑ j ∈ Finset.univ.erase i, x j := by
    simpa only [Finset.sum_const, hc, nsmul_eq_mul] using ho
  have ht : (∑ j ∈ Finset.univ.erase i, x j) + x i ≤ m := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact hsum
  have hn : 0 ≤ eta*(m : ℝ) := mul_nonneg heta (Nat.cast_nonneg _)
  exact abs_le.mpr ⟨by nlinarith [hlower i], by nlinarith⟩

theorem balanced_of_vanishing {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (A : Matrix (Fin 10) (Fin 10) K)
    (P : MvPolynomial (Vars10 m) ℤ) (hP : homogeneous10 r P)
    (hz : ∀ (i : Fin 10) (J b : Vars10 m →₀ ℕ),
      rothSourceDerivativeWeight r J + coordinateWeight r i b < (1/10-eta)*m →
      (expansion A J P).coeff b = 0)
    (J b : Vars10 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m)
    (hb : (expansion A J P).coeff b ≠ 0) :
    ∀ i, |coordinateWeight r i b - (m : ℝ)/10| ≤ 54*eta*m := by
  have hlower (i : Fin 10) : (m : ℝ)/10 - 3*eta*m ≤ coordinateWeight r i b := by
    have ht : (1/10-eta)*m ≤ rothSourceDerivativeWeight r J + coordinateWeight r i b := by
      by_contra! hbad
      exact hb (hz i J b hbad)
    nlinarith
  exact balance_from_weights m eta heta.le (fun i => coordinateWeight r i b)
    (total_coordinate_weight_le r hr A J P hP b hb) hlower

def Claims {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (A : Matrix (Fin 10) (Fin 10) K) (P : MvPolynomial (Vars10 m) ℤ) : Prop :=
  (∀ J, substitution A (expansion A J P) = derivative10 J (P.map (Int.castRingHom K))) ∧
  (∀ (i : Fin 10) (J b : Vars10 m →₀ ℕ),
    rothSourceDerivativeWeight r J + coordinateWeight r i b < (1/10-eta)*m →
    (expansion A J P).coeff b = 0) ∧
  (∀ (J b : Vars10 m →₀ ℕ), (expansion A J P).coeff b ≠ 0 →
    ∀ h, (∑ j : Fin 10, b (h,j)) = r h - ∑ j : Fin 10, J (h,j)) ∧
  (∀ (J b : Vars10 m →₀ ℕ), (expansion A J P).coeff b ≠ 0 →
    (∑ i : Fin 10, coordinateWeight r i b) ≤ m) ∧
  (∀ (J b : Vars10 m →₀ ℕ), rothSourceDerivativeWeight r J ≤ 2*eta*m →
    (expansion A J P).coeff b ≠ 0 →
    ∀ i, |coordinateWeight r i b - (m : ℝ)/10| ≤ 54*eta*m)

theorem claims_of_charts {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (A : Matrix (Fin 10) (Fin 10) K) (hA : A.det ≠ 0)
    (P : MvPolynomial (Vars10 m) ℤ) (hP : homogeneous10 r P)
    (hindex : ∀ (i : Fin 10) (J : Vars10 m →₀ ℕ),
      rothSourceDerivativeWeight r J < (1/10-eta)*m →
      ∀ p : Fin 10, A i p ≠ 0 → kernelRestriction10 (A i) (fun _ => p)
        (derivative10 J (P.map (Int.castRingHom K))) = 0) : Claims r eta A P := by
  have hz (i : Fin 10) (J b : Vars10 m →₀ ℕ)
      (hb : rothSourceDerivativeWeight r J + coordinateWeight r i b < (1/10-eta)*m) :
      (expansion A J P).coeff b = 0 := by
    have hn : ∃ p, A i p ≠ 0 := by
      by_contra! hh
      exact hA (Matrix.det_eq_zero_of_row_eq_zero i hh)
    obtain ⟨p,hp⟩ := hn
    apply coeff_zero_below_index r A hA i p hp ((1/10-eta)*m) P
    · intro D hD
      exact hindex i D hD p hp
    · exact hb
  exact ⟨fun J => reconstruct A hA J P, hz,
    fun J b hb h => expansion_block_degree r A J P hP b hb h,
    fun J b hb => total_coordinate_weight_le r hr A J P hP b hb,
    fun J b hJ hb => balanced_of_vanishing r hr eta heta A P hP hz J b hJ hb⟩



theorem claims_of_matrix_index10 {F : Type*} [Field F] [CharZero F]
    {m : ℕ} (B : Matrix (Fin 10) (Fin 10) F) (hB : B.det = 1)
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta)
    (P : MvPolynomial (Vars10 m) ℤ) (hhom : homogeneous10 r P)
    (hi : matrixIndex10 B r eta P) : Claims r eta B P := by
  apply claims_of_charts r hr eta heta B (by rw [hB]; exact one_ne_zero) P hhom
  intro i J hJ k hk
  exact hi i J hJ (fun _ => k) (fun _ => hk)

end CompoundFeasibility.Auxiliary10.SourceBalance10
