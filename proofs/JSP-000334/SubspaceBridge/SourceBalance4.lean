import SubspaceBridge.SourceSupport4
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary4.SourceBalance4
open SourceMultiblock4 SourceExpansion4 SourceSupport4

variable {K : Type*} [Field K] [CharZero K]
theorem chart_block_weight {m : ℕ} (B : Matrix (Fin 4) (Fin 4) K)
    (h : Fin m) (u : Vars4 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars4 m => if v.1 = h then 1 else 0)
      (linearChart B u) (if u.1 = h then 1 else 0) := by
  unfold linearChart
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro j hj
  simpa only [zero_add] using
    (MvPolynomial.isWeightedHomogeneous_C _ (B u.2 j)).mul
      (MvPolynomial.isWeightedHomogeneous_X K (fun v : Vars4 m => if v.1 = h then 1 else 0) (u.1,j))

theorem expansion_block_weight {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 4) (Fin 4) K) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars4 m => if v.1 = h then 1 else 0)
      (expansion L J P) (r h - ∑ j : Fin 4, J (h,j)) := by
  classical
  let Q := derivative4 J (P.map (Int.castRingHom K))
  let w := fun v : Vars4 m => if v.1 = h then 1 else 0
  have hdegree (d : Vars4 m →₀ ℕ) (hd : d ∈ Q.support) :
      (∑ j : Fin 4, d (h,j)) = r h - ∑ j : Fin 4, J (h,j) := by
    have hcoeff : P.coeff (d + J) ≠ 0 := by
      intro hz
      have hn := MvPolynomial.mem_support_iff.mp hd
      rw [derivative4_coeff, MvPolynomial.coeff_map, hz, map_zero, zero_mul] at hn
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
  have hw : (∑ u : Vars4 m, d u * w u) = ∑ j : Fin 4, d (h,j) := by
    have he := rothAux_weight_block d h
    rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun u (n : ℕ) => n • w u) (by intro u; simp)] at he
    simpa only [nsmul_eq_mul, Nat.cast_id, w] using he
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun u : Vars4 m => linearChart (L)⁻¹ u ^ d u)
    (fun u => d u * w u)
    (fun u _ => by simpa only [nsmul_eq_mul] using
      (chart_block_weight (L)⁻¹ h u).pow (d u))
  simpa only [zero_add, hw, hdegree d hd] using
    (MvPolynomial.isWeightedHomogeneous_C w (Q.coeff d)).mul hprod

theorem expansion_block_degree {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 4) (Fin 4) K) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (b : Vars4 m →₀ ℕ) (hb : (expansion L J P).coeff b ≠ 0) (h : Fin m) :
    (∑ j : Fin 4, b (h,j)) = r h - ∑ j : Fin 4, J (h,j) := by
  have hw := expansion_block_weight r L J P hP h hb
  rwa [rothAux_weight_block] at hw

theorem total_coordinate_weight_le {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (L : Matrix (Fin 4) (Fin 4) K) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (b : Vars4 m →₀ ℕ) (hb : (expansion L J P).coeff b ≠ 0) :
    (∑ i : Fin 4, coordinateWeight r i b) ≤ (m : ℝ) := by
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
      exact_mod_cast (show (∑ i : Fin 4, b (h,i)) ≤ r h by omega)
    _ = _ := by simp




theorem balance_from_weights (m : ℕ) (eta : ℝ) (heta : 0 ≤ eta)
    (x : Fin 4 → ℝ) (hsum : (∑ i, x i) ≤ m)
    (hlower : ∀ i, (m : ℝ)/4 - 3*eta*m ≤ x i) :
    ∀ i, |x i - (m : ℝ)/4| ≤ 18*eta*m := by
  intro i
  have hc : (Finset.univ.erase i : Finset (Fin 4)).card = 3 := by simp
  have ho := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ => hlower j)
  have ho' : 3*((m : ℝ)/4 - 3*eta*m) ≤ ∑ j ∈ Finset.univ.erase i, x j := by
    simpa only [Finset.sum_const, hc, nsmul_eq_mul] using ho
  have ht : (∑ j ∈ Finset.univ.erase i, x j) + x i ≤ m := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact hsum
  have hn : 0 ≤ eta*(m : ℝ) := mul_nonneg heta (Nat.cast_nonneg _)
  exact abs_le.mpr ⟨by nlinarith [hlower i], by nlinarith⟩

theorem balanced_of_vanishing {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (A : Matrix (Fin 4) (Fin 4) K)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (hz : ∀ (i : Fin 4) (J b : Vars4 m →₀ ℕ),
      rothSourceDerivativeWeight r J + coordinateWeight r i b < (1/4-eta)*m →
      (expansion A J P).coeff b = 0)
    (J b : Vars4 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m)
    (hb : (expansion A J P).coeff b ≠ 0) :
    ∀ i, |coordinateWeight r i b - (m : ℝ)/4| ≤ 18*eta*m := by
  have hlower (i : Fin 4) : (m : ℝ)/4 - 3*eta*m ≤ coordinateWeight r i b := by
    have ht : (1/4-eta)*m ≤ rothSourceDerivativeWeight r J + coordinateWeight r i b := by
      by_contra! hbad
      exact hb (hz i J b hbad)
    nlinarith
  exact balance_from_weights m eta heta.le (fun i => coordinateWeight r i b)
    (total_coordinate_weight_le r hr A J P hP b hb) hlower

def Claims {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (A : Matrix (Fin 4) (Fin 4) K) (P : MvPolynomial (Vars4 m) ℤ) : Prop :=
  (∀ J, substitution A (expansion A J P) = derivative4 J (P.map (Int.castRingHom K))) ∧
  (∀ (i : Fin 4) (J b : Vars4 m →₀ ℕ),
    rothSourceDerivativeWeight r J + coordinateWeight r i b < (1/4-eta)*m →
    (expansion A J P).coeff b = 0) ∧
  (∀ (J b : Vars4 m →₀ ℕ), (expansion A J P).coeff b ≠ 0 →
    ∀ h, (∑ j : Fin 4, b (h,j)) = r h - ∑ j : Fin 4, J (h,j)) ∧
  (∀ (J b : Vars4 m →₀ ℕ), (expansion A J P).coeff b ≠ 0 →
    (∑ i : Fin 4, coordinateWeight r i b) ≤ m) ∧
  (∀ (J b : Vars4 m →₀ ℕ), rothSourceDerivativeWeight r J ≤ 2*eta*m →
    (expansion A J P).coeff b ≠ 0 →
    ∀ i, |coordinateWeight r i b - (m : ℝ)/4| ≤ 18*eta*m)

theorem claims_of_charts {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (A : Matrix (Fin 4) (Fin 4) K) (hA : A.det ≠ 0)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (hindex : ∀ (i : Fin 4) (J : Vars4 m →₀ ℕ),
      rothSourceDerivativeWeight r J < (1/4-eta)*m →
      ∀ p : Fin 4, A i p ≠ 0 → kernelRestriction4 (A i) (fun _ => p)
        (derivative4 J (P.map (Int.castRingHom K))) = 0) : Claims r eta A P := by
  have hz (i : Fin 4) (J b : Vars4 m →₀ ℕ)
      (hb : rothSourceDerivativeWeight r J + coordinateWeight r i b < (1/4-eta)*m) :
      (expansion A J P).coeff b = 0 := by
    have hn : ∃ p, A i p ≠ 0 := by
      by_contra! hh
      exact hA (Matrix.det_eq_zero_of_row_eq_zero i hh)
    obtain ⟨p,hp⟩ := hn
    apply coeff_zero_below_index r A hA i p hp ((1/4-eta)*m) P
    · intro D hD
      exact hindex i D hD p hp
    · exact hb
  exact ⟨fun J => reconstruct A hA J P, hz,
    fun J b hb h => expansion_block_degree r A J P hP b hb h,
    fun J b hb => total_coordinate_weight_le r hr A J P hP b hb,
    fun J b hJ hb => balanced_of_vanishing r hr eta heta A P hP hz J b hJ hb⟩



theorem claims_of_matrix_index4 {F : Type*} [Field F] [CharZero F]
    {m : ℕ} (B : Matrix (Fin 4) (Fin 4) F) (hB : B.det = 1)
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta)
    (P : MvPolynomial (Vars4 m) ℤ) (hhom : homogeneous4 r P)
    (hi : matrixIndex4 B r eta P) : Claims r eta B P := by
  apply claims_of_charts r hr eta heta B (by rw [hB]; exact one_ne_zero) P hhom
  intro i J hJ k hk
  exact hi i J hJ (fun _ => k) (fun _ => hk)

theorem source_auxiliary4_balanced (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ hmem : ∀ tau i j, SourceForms4.forms4 A2 A3 L tau i j ∈ K,
      ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧ ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log (24*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars4 m) ℤ, P ≠ 0 ∧ homogeneous4 r P ∧
      (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
      (∀ tau, matrixIndex4 (fun i j => (⟨SourceForms4.forms4 A2 A3 L tau i j,hmem tau i j⟩ : K)) r eta P) ∧
      (∀ tau, matrixIndex4 (SourceForms4.forms4 A2 A3 L tau) r eta P) ∧
      matrixIndex4 (SourceForms4.finiteMatrix4 2 A2) r eta P ∧
      matrixIndex4 (SourceForms4.finiteMatrix4 3 A3) r eta P ∧
      (Claims r eta L P ∧ Claims r eta (SourceForms4.finiteMatrix4 2 A2) P ∧
        Claims r eta (SourceForms4.finiteMatrix4 3 A3) P) ∧
      (∀ J b : Vars4 m →₀ ℕ,
        ‖(expansion L J P).coeff b‖ ≤ E^(∑ h, r h) ∧
        ‖(expansion (SourceForms4.finiteMatrix4 2 A2) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
        ‖(expansion (SourceForms4.finiteMatrix4 3 A3) J P).coeff b‖ ≤ E^(∑ h, r h)) := by
  obtain ⟨K,hK,hmem,D,hD,hconstruction⟩ := source_auxiliary4_all_places A2 A3 L h2 h3 hL ha
  obtain ⟨E,hE,hbound⟩ := source_coefficient_bounds A2 A3 L D hD
  refine ⟨K,hK,hmem,D,E,hD,hE,?_⟩
  intro eta heta m hm r hr
  obtain ⟨P,hn,hhom,hheight,hfield,hreal,hp2,hp3⟩ := hconstruction eta heta m hm r hr
  refine ⟨P,hn,hhom,hheight,hfield,hreal,hp2,hp3,?_,hbound m r hr P hhom hheight⟩
  constructor
  · exact claims_of_matrix_index4 L hL r hr eta heta P hhom (hreal 0)
  · constructor
    · exact claims_of_matrix_index4 _ (SourceForms4.finite_det_one4 2 A2 h2) r hr eta heta P hhom hp2
    · exact claims_of_matrix_index4 _ (SourceForms4.finite_det_one4 3 A3 h3) r hr eta heta P hhom hp3

end CompoundFeasibility.Auxiliary4.SourceBalance4
