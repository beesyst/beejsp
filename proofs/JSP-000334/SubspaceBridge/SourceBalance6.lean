import SubspaceBridge.SourceSupport6
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary6.SourceBalance
open SourceExpansion SourceSupport

theorem mapped_inverse {n F E : Type*} [Fintype n] [DecidableEq n] [Field F] [Field E]
    (f : F →+* E) (B : Matrix n n F) (hB : B.det ≠ 0) :
    f.mapMatrix B⁻¹ * f.mapMatrix B = 1 ∧ f.mapMatrix B * f.mapMatrix B⁻¹ = 1 := by
  constructor
  · rw [← map_mul, Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB), map_one]
  · rw [← map_mul, Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB), map_one]

theorem mapped_nonsingular {n F E : Type*} [Fintype n] [DecidableEq n] [Field F] [Field E]
    (f : F →+* E) (B : Matrix n n F) (hB : B.det ≠ 0) :
    (B.map f).det ≠ 0 := by
  have hm := (mapped_inverse f B hB).1
  apply Matrix.det_ne_zero_of_left_inverse
  exact hm

theorem finiteMatrix_nonsingular (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) :
    (finiteMatrix p A).det ≠ 0 := by
  unfold finiteMatrix
  apply mapped_nonsingular
  have hB : (compound A).det = 1 := by
    apply compound42_det_one
    exact hA
  rw [hB]
  exact one_ne_zero



variable {K : Type*} [Field K] [CharZero K]
theorem chart_block_weight {m : ℕ} (B : Matrix (Fin 6) (Fin 6) K)
    (h : Fin m) (u : Vars6 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars6 m => if v.1 = h then 1 else 0)
      (linearChart B u) (if u.1 = h then 1 else 0) := by
  unfold linearChart
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro j hj
  simpa only [zero_add] using
    (MvPolynomial.isWeightedHomogeneous_C _ (B u.2 j)).mul
      (MvPolynomial.isWeightedHomogeneous_X K (fun v : Vars6 m => if v.1 = h then 1 else 0) (u.1,j))

theorem expansion_block_weight {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 6) (Fin 6) K) (J : Vars6 m →₀ ℕ)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars6 m => if v.1 = h then 1 else 0)
      (expansion L J P) (r h - ∑ j : Fin 6, J (h,j)) := by
  classical
  let Q := derivative6 J (P.map (Int.castRingHom K))
  let w := fun v : Vars6 m => if v.1 = h then 1 else 0
  have hdegree (d : Vars6 m →₀ ℕ) (hd : d ∈ Q.support) :
      (∑ j : Fin 6, d (h,j)) = r h - ∑ j : Fin 6, J (h,j) := by
    have hcoeff : P.coeff (d + J) ≠ 0 := by
      intro hz
      have hn := MvPolynomial.mem_support_iff.mp hd
      rw [derivative6_coeff, MvPolynomial.coeff_map, hz, map_zero, zero_mul] at hn
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
  have hw : (∑ u : Vars6 m, d u * w u) = ∑ j : Fin 6, d (h,j) := by
    have he := rothAux_weight_block d h
    rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun u (n : ℕ) => n • w u) (by intro u; simp)] at he
    simpa only [nsmul_eq_mul, Nat.cast_id, w] using he
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun u : Vars6 m => linearChart (L)⁻¹ u ^ d u)
    (fun u => d u * w u)
    (fun u _ => by simpa only [nsmul_eq_mul] using
      (chart_block_weight (L)⁻¹ h u).pow (d u))
  simpa only [zero_add, hw, hdegree d hd] using
    (MvPolynomial.isWeightedHomogeneous_C w (Q.coeff d)).mul hprod

theorem expansion_block_degree {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 6) (Fin 6) K) (J : Vars6 m →₀ ℕ)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P)
    (b : Vars6 m →₀ ℕ) (hb : (expansion L J P).coeff b ≠ 0) (h : Fin m) :
    (∑ j : Fin 6, b (h,j)) = r h - ∑ j : Fin 6, J (h,j) := by
  have hw := expansion_block_weight r L J P hP h hb
  rwa [rothAux_weight_block] at hw

theorem total_coordinate_weight_le {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (L : Matrix (Fin 6) (Fin 6) K) (J : Vars6 m →₀ ℕ)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P)
    (b : Vars6 m →₀ ℕ) (hb : (expansion L J P).coeff b ≠ 0) :
    (∑ i : Fin 6, coordinateWeight r i b) ≤ (m : ℝ) := by
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
      exact_mod_cast (show (∑ i : Fin 6, b (h,i)) ≤ r h by omega)
    _ = _ := by simp




theorem balance_from_weights (m : ℕ) (eta : ℝ) (heta : 0 ≤ eta)
    (x : Fin 6 → ℝ) (hsum : (∑ i, x i) ≤ m)
    (hlower : ∀ i, (m : ℝ)/6 - 3*eta*m ≤ x i) :
    ∀ i, |x i - (m : ℝ)/6| ≤ 18*eta*m := by
  intro i
  have hc : (Finset.univ.erase i : Finset (Fin 6)).card = 5 := by simp
  have ho := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ => hlower j)
  have ho' : 5*((m : ℝ)/6 - 3*eta*m) ≤ ∑ j ∈ Finset.univ.erase i, x j := by
    simpa only [Finset.sum_const, hc, nsmul_eq_mul] using ho
  have ht : (∑ j ∈ Finset.univ.erase i, x j) + x i ≤ m := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact hsum
  have hn : 0 ≤ eta*(m : ℝ) := mul_nonneg heta (Nat.cast_nonneg _)
  exact abs_le.mpr ⟨by nlinarith [hlower i], by nlinarith⟩

theorem balanced_of_vanishing {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (A : Matrix (Fin 6) (Fin 6) K)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P)
    (hz : ∀ (i : Fin 6) (J b : Vars6 m →₀ ℕ),
      rothSourceDerivativeWeight r J + coordinateWeight r i b < (1/6-eta)*m →
      (expansion A J P).coeff b = 0)
    (J b : Vars6 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m)
    (hb : (expansion A J P).coeff b ≠ 0) :
    ∀ i, |coordinateWeight r i b - (m : ℝ)/6| ≤ 18*eta*m := by
  have hlower (i : Fin 6) : (m : ℝ)/6 - 3*eta*m ≤ coordinateWeight r i b := by
    have ht : (1/6-eta)*m ≤ rothSourceDerivativeWeight r J + coordinateWeight r i b := by
      by_contra! hbad
      exact hb (hz i J b hbad)
    nlinarith
  exact balance_from_weights m eta heta.le (fun i => coordinateWeight r i b)
    (total_coordinate_weight_le r hr A J P hP b hb) hlower

def Claims {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (A : Matrix (Fin 6) (Fin 6) K) (P : MvPolynomial (Vars6 m) ℤ) : Prop :=
  (∀ J, substitution A (expansion A J P) = derivative6 J (P.map (Int.castRingHom K))) ∧
  (∀ (i : Fin 6) (J b : Vars6 m →₀ ℕ),
    rothSourceDerivativeWeight r J + coordinateWeight r i b < (1/6-eta)*m →
    (expansion A J P).coeff b = 0) ∧
  (∀ (J b : Vars6 m →₀ ℕ), (expansion A J P).coeff b ≠ 0 →
    ∀ h, (∑ j : Fin 6, b (h,j)) = r h - ∑ j : Fin 6, J (h,j)) ∧
  (∀ (J b : Vars6 m →₀ ℕ), (expansion A J P).coeff b ≠ 0 →
    (∑ i : Fin 6, coordinateWeight r i b) ≤ m) ∧
  (∀ (J b : Vars6 m →₀ ℕ), rothSourceDerivativeWeight r J ≤ 2*eta*m →
    (expansion A J P).coeff b ≠ 0 →
    ∀ i, |coordinateWeight r i b - (m : ℝ)/6| ≤ 18*eta*m)

theorem claims_of_charts {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (A : Matrix (Fin 6) (Fin 6) K) (hA : A.det ≠ 0)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P)
    (hindex : ∀ (i : Fin 6) (J : Vars6 m →₀ ℕ),
      rothSourceDerivativeWeight r J < (1/6-eta)*m →
      ∀ p : Fin 6, A i p ≠ 0 → kernelRestriction6 (A i) (fun _ => p)
        (derivative6 J (P.map (Int.castRingHom K))) = 0) : Claims r eta A P := by
  have hz (i : Fin 6) (J b : Vars6 m →₀ ℕ)
      (hb : rothSourceDerivativeWeight r J + coordinateWeight r i b < (1/6-eta)*m) :
      (expansion A J P).coeff b = 0 := by
    have hn : ∃ p, A i p ≠ 0 := by
      by_contra! hh
      exact hA (Matrix.det_eq_zero_of_row_eq_zero i hh)
    obtain ⟨p,hp⟩ := hn
    apply coeff_zero_below_index r A hA i p hp ((1/6-eta)*m) P
    · intro D hD
      exact hindex i D hD p hp
    · exact hb
  exact ⟨fun J => reconstruct A hA J P, hz,
    fun J b hb h => expansion_block_degree r A J P hP b hb h,
    fun J b hb => total_coordinate_weight_le r hr A J P hP b hb,
    fun J b hJ hb => balanced_of_vanishing r hr eta heta A P hP hz J b hJ hb⟩



def RealIndex (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) (P : MvPolynomial (Vars6 m) ℤ) : Prop :=
  ∀ tau s (J : Vars6 m →₀ ℕ), rothSourceDerivativeWeight r J < (1/6-eta)*m →
    ∀ k : Fin m → Fin 6, (∀ h, forms A2 A3 L tau s (k h) ≠ 0) →
    kernelRestriction6 (forms A2 A3 L tau s) k
      (derivative6 J (P.map (Int.castRingHom ℝ))) = 0

def FieldIndex (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (K : IntermediateField ℚ ℝ) (hmem : ∀ tau s j, forms A2 A3 L tau s j ∈ K)
    {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) (P : MvPolynomial (Vars6 m) ℤ) : Prop :=
  ∀ tau s (J : Vars6 m →₀ ℕ), rothSourceDerivativeWeight r J < (1/6-eta)*m →
    ∀ k : Fin m → Fin 6,
      (∀ h, (⟨forms A2 A3 L tau s (k h), hmem tau s (k h)⟩ : K) ≠ 0) →
    kernelRestriction6 (fun j => (⟨forms A2 A3 L tau s j, hmem tau s j⟩ : K)) k
      (derivative6 J (P.map (Int.castRingHom K))) = 0

theorem finite_claims (p : ℕ) [Fact p.Prime] {m : ℕ}
    (B : Matrix (Fin 4) (Fin 4) ℚ) (hB : B.det = 1)
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P)
    (hindex : ∀ (i : Fin 6) (J : Vars6 m →₀ ℕ),
      rothSourceDerivativeWeight r J < (1/6-eta)*m →
      ∀ k : Fin 6, compound B i k ≠ 0 →
      kernelRestriction6 (fun j => ((compound B i j : ℚ) : ℝ)) (fun _ => k)
        (derivative6 J (P.map (Int.castRingHom ℝ))) = 0) :
    Claims r eta (finiteMatrix p B) P := by
  apply claims_of_charts r hr eta heta (finiteMatrix p B)
  · apply finiteMatrix_nonsingular
    exact hB
  · exact hP
  · intro i J hJ k hk
    change kernelRestriction6 (fun j => (algebraMap ℚ ℚ_[p]) (compound B i j))
      (fun _ => k) (derivative6 J (P.map (Int.castRingHom ℚ_[p]))) = 0
    apply padic_restriction_zero p (compound B i) (fun _ => k) J P
    apply hindex i J hJ k
    intro hh
    apply hk
    change (algebraMap ℚ ℚ_[p]) (compound B i k) = 0
    rw [hh, map_zero]

theorem source_claims {m : ℕ} (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (P : MvPolynomial (Vars6 m) ℤ)
    (hP : homogeneous6 r P) (hsource : RealIndex A2 A3 L r eta P) :
    Claims r eta (compound L) P ∧ Claims r eta (finiteMatrix 2 A2) P ∧
      Claims r eta (finiteMatrix 3 A3) P := by
  constructor
  · apply claims_of_charts r hr eta heta (compound L)
    · have hd : (compound L).det = 1 := by
        apply compound42_det_one
        exact hL
      rw [hd]
      exact one_ne_zero
    · exact hP
    · intro i J hJ p hp
      have hz := hsource 0 i J hJ (fun _ => p) (fun _ => by simpa only [forms, if_pos rfl] using hp)
      simpa only [forms, if_pos rfl] using hz
  · constructor
    · apply finite_claims 2 A2 h2 r hr eta heta P hP
      intro i J hJ p hp
      have hrp : ((compound A2 i p : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hp
      have hz := hsource 1 i J hJ (fun _ => p) (fun _ => by simpa [forms] using hrp)
      simpa [forms] using hz
    · apply finite_claims 3 A3 h3 r hr eta heta P hP
      intro i J hJ p hp
      have hrp : ((compound A3 i p : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hp
      have hz := hsource 2 i J hJ (fun _ => p) (fun _ => by simpa [forms] using hrp)
      simpa [forms] using hz



theorem source_auxiliary6_balanced (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ hmem : ∀ tau s j, forms A2 A3 L tau s j ∈ K,
      ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log (36*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars6 m) ℤ,
        P ≠ 0 ∧ homogeneous6 r P ∧ (height6 P : ℝ) ≤ D^(∑ h, r h) ∧
        FieldIndex A2 A3 L K hmem r eta P ∧ RealIndex A2 A3 L r eta P ∧
        (Claims r eta (compound L) P ∧ Claims r eta (finiteMatrix 2 A2) P ∧
          Claims r eta (finiteMatrix 3 A3) P) ∧
        (∀ J b : Vars6 m →₀ ℕ,
          ‖(expansion (compound L) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
          ‖(expansion (finiteMatrix 2 A2) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
          ‖(expansion (finiteMatrix 3 A3) J P).coeff b‖ ≤ E^(∑ h, r h)) := by
  obtain ⟨K,hK,hmem,D,hD,hconstruction⟩ := source_auxiliary6_field A2 A3 L h2 h3 hL ha
  obtain ⟨E,hE,hbound⟩ := source_coefficient_bounds A2 A3 L D hD
  refine ⟨K,hK,hmem,D,E,hD,hE,?_⟩
  intro eta heta m hm r hr
  obtain ⟨P,hn,hhom,hheight,hfield,hreal⟩ := hconstruction eta heta m hm r hr
  refine ⟨P,hn,hhom,hheight,hfield,hreal,?_,?_⟩
  · exact source_claims A2 A3 L h2 h3 hL r hr eta heta P hhom hreal
  · exact hbound m r hr P hhom hheight

end CompoundFeasibility.Auxiliary6.SourceBalance
