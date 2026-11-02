import SubspaceBridge.AlgebraicLiouville6
open scoped BigOperators Matrix
noncomputable section
namespace CompoundFeasibility

theorem liouville4_common_field (a : Fin 4 → Fin 4 → ℝ)
    (ha : ∀ s i, IsAlgebraic ℚ (a s i)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∀ s i, a s i ∈ K := by
  let S : Set ℝ := Set.range (fun p : Fin 4 × Fin 4 => a p.1 p.2)
  let K := IntermediateField.adjoin ℚ S
  haveI : Finite S := Set.finite_range _
  have hfin : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin (by
    rintro x ⟨⟨s,i⟩,rfl⟩
    exact (ha s i).isIntegral)
  exact ⟨K,hfin,fun s i => IntermediateField.subset_adjoin ℚ S ⟨(s,i),rfl⟩⟩

theorem liouville4_common_denominator (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (b : Fin 4 → Fin 4 → K) :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ s i, IsIntegral ℤ ((M : K) * b s i) := by
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  haveI : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := K)).mpr inferInstance
  obtain ⟨M,hM,hi⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ
    (Finset.univ.image (fun p : Fin 4 × Fin 4 => b p.1 p.2))
  refine ⟨M,hM,fun s i => ?_⟩
  simpa only [Algebra.smul_def,eq_intCast] using hi (b s i) (Finset.mem_image.mpr ⟨(s,i),Finset.mem_univ _,rfl⟩)

theorem liouville4_conjugate_height (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (b : Fin 4 → Fin 4 → K) :
    ∃ B : ℝ, 0 < B ∧ ∀ (sigma : K →ₐ[ℚ] ℂ) s (z : Fin 4 → ℤ),
      ‖sigma (∑ i, b s i * (z i : K))‖ ≤
        B * max 1 ‖(fun i => (z i : ℝ))‖ := by
  classical
  let B := max 1 (∑ sigma : K →ₐ[ℚ] ℂ, ∑ s : Fin 4, ∑ i : Fin 4, ‖sigma (b s i)‖)
  refine ⟨B,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro sigma s z
  have hrow : (∑ i : Fin 4, ‖sigma (b s i)‖) ≤ B := by
    apply le_trans _ (le_max_right _ _)
    have hs : (∑ i : Fin 4, ‖sigma (b s i)‖) ≤ ∑ t : Fin 4, ∑ i : Fin 4, ‖sigma (b t i)‖ :=
      Finset.single_le_sum (s := Finset.univ) (f := fun t : Fin 4 => ∑ i : Fin 4, ‖sigma (b t i)‖) (fun t _ => Finset.sum_nonneg (fun i _ => norm_nonneg _)) (Finset.mem_univ s)
    have ht : (∑ t : Fin 4, ∑ i : Fin 4, ‖sigma (b t i)‖) ≤ ∑ tau : K →ₐ[ℚ] ℂ, ∑ t : Fin 4, ∑ i : Fin 4, ‖tau (b t i)‖ :=
      Finset.single_le_sum (s := Finset.univ) (f := fun tau : K →ₐ[ℚ] ℂ => ∑ t : Fin 4, ∑ i : Fin 4, ‖tau (b t i)‖) (fun t _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => norm_nonneg _))) (Finset.mem_univ sigma)
    exact hs.trans ht
  have hi (i : Fin 4) : |(z i : ℝ)| ≤ max 1 ‖(fun i => (z i : ℝ))‖ := by
    have hh : |(z i : ℝ)| ≤ ‖(fun i => (z i : ℝ))‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun i => (z i : ℝ)) i
    exact hh.trans (le_max_right _ _)
  calc
    ‖sigma (∑ i, b s i * (z i : K))‖ = ‖∑ i, sigma (b s i) * (z i : ℂ)‖ := by simp only [map_sum,map_mul,map_intCast]
    _ ≤ ∑ i : Fin 4, ‖sigma (b s i)‖ * |(z i : ℝ)| := by simpa only [norm_mul,Complex.norm_intCast] using norm_sum_le (s := Finset.univ) (f := fun i => sigma (b s i) * (z i : ℂ))
    _ ≤ ∑ i : Fin 4, ‖sigma (b s i)‖ * max 1 ‖(fun i => (z i : ℝ))‖ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi i) (norm_nonneg _)
    _ = (∑ i : Fin 4, ‖sigma (b s i)‖) * max 1 ‖(fun i => (z i : ℝ))‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ B * max 1 ‖(fun i => (z i : ℝ))‖ := mul_le_mul_of_nonneg_right hrow (le_trans zero_le_one (le_max_left _ _))

theorem liouville4_field_liouville (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (b : Fin 4 → Fin 4 → K) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ s (z : Fin 4 → ℤ),
      (∑ i, (b s i : ℝ) * (z i : ℝ)) ≠ 0 →
      C ≤ |∑ i, (b s i : ℝ) * (z i : ℝ)| * (max 1 ‖(fun i => (z i : ℝ))‖)^D := by
  classical
  obtain ⟨M,hM,hint⟩ := liouville4_common_denominator K b
  let c : Fin 4 → Fin 4 → K := fun s i => (M : K) * b s i
  obtain ⟨B,hB,hheight⟩ := liouville4_conjugate_height K c
  let sigma0 : K →ₐ[ℚ] ℂ := (IsScalarTower.toAlgHom ℚ ℝ ℂ).comp K.val
  let D := Fintype.card (K →ₐ[ℚ] ℂ) - 1
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have hden : 0 < |(M : ℝ)| * B^D := mul_pos (abs_pos.mpr hMr) (pow_pos hB _)
  refine ⟨(|(M : ℝ)| * B^D)⁻¹,inv_pos.mpr hden,D,?_⟩
  intro s z hz
  let beta : K := ∑ i, c s i * (z i : K)
  have hb : IsIntegral ℤ beta := IsIntegral.sum _ (fun i _ =>
    (hint s i).mul (isIntegral_algebraMap : IsIntegral ℤ ((algebraMap ℤ K) (z i))))
  have he : sigma0 beta = ((M : ℝ) * (∑ i, (b s i : ℝ) * (z i : ℝ)) : ℝ) := by
    simp [beta,c,sigma0,Finset.mul_sum,mul_assoc]
  have hb0 : beta ≠ 0 := by
    intro h
    have hh := he
    rw [h,map_zero] at hh
    have hh' : (M : ℝ) * (∑ i, (b s i : ℝ) * (z i : ℝ)) = 0 := by
      exact_mod_cast hh.symm
    exact (mul_ne_zero hMr hz) hh'
  have hp := liouville6_integral_norm_lower K beta hb hb0
  rw [liouville6_norm_product] at hp
  rw [← Finset.mul_prod_erase Finset.univ (fun sigma : K →ₐ[ℚ] ℂ => ‖sigma beta‖)
    (Finset.mem_univ sigma0)] at hp
  have hrest : (∏ sigma ∈ Finset.univ.erase sigma0, ‖sigma beta‖) ≤
      (B * max 1 ‖(fun i => (z i : ℝ))‖)^D := by
    calc
      _ ≤ ∏ _sigma ∈ Finset.univ.erase sigma0, B * max 1 ‖(fun i => (z i : ℝ))‖ :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun sigma _ => hheight sigma s z)
      _ = _ := by rw [Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ sigma0)]; rfl
  have htotal : 1 ≤ (|(M : ℝ)| * B^D) *
      (|∑ i, (b s i : ℝ) * (z i : ℝ)| * (max 1 ‖(fun i => (z i : ℝ))‖)^D) := by
    calc
      1 ≤ ‖sigma0 beta‖ * (∏ sigma ∈ Finset.univ.erase sigma0, ‖sigma beta‖) := hp
      _ ≤ ‖sigma0 beta‖ * (B * max 1 ‖(fun i => (z i : ℝ))‖)^D :=
        mul_le_mul_of_nonneg_left hrest (norm_nonneg _)
      _ = _ := by rw [he,Complex.norm_real,Real.norm_eq_abs,abs_mul,mul_pow]; ring
  rw [← one_div]
  exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using htotal)

theorem algebraic_fin4_liouville_lower
    (a : Fin 4 → Fin 4 → ℝ) (ha : ∀ s i, IsAlgebraic ℚ (a s i)) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ s : Fin 4, ∀ z : Fin 4 → ℤ,
      (∑ i, a s i * (z i : ℝ)) ≠ 0 →
      C ≤ |∑ i, a s i * (z i : ℝ)| * (max 1 ‖integerReal z‖)^D := by
  obtain ⟨K,hK,hmem⟩ := liouville4_common_field a ha
  letI : FiniteDimensional ℚ K := hK
  let b : Fin 4 → Fin 4 → K := fun s i => ⟨a s i,hmem s i⟩
  exact liouville4_field_liouville K b

end CompoundFeasibility
