import SubspaceBridge
open scoped BigOperators Matrix
namespace JSP000334

def weightedRetainedMatrix2 (B C : ℚ) (k : Fin 2) : Matrix (Fin 2) (Fin 2) ℚ :=
  if k = 0 then !![1, 0; B, C] else !![0, 1; B, C]

def weightedRetainedProduct2 (B C u v : ℚ) : ℚ :=
  ∏ tau : Fin 3, min (rationalPlaceNorm tau u) (rationalPlaceNorm tau v) *
    rationalPlaceNorm tau (B*u+C*v)

def weightedNormalizedProduct2 (B C u v : ℚ) : ℚ :=
  ∏ tau : Fin 3,
    (min (rationalPlaceNorm tau u) (rationalPlaceNorm tau v) / localPairHeight tau u v) *
    (rationalPlaceNorm tau (B*u+C*v) / localPairHeight tau u v)

theorem weighted_retained_det2 (B C : ℚ) (hB : B ≠ 0) (hC : C ≠ 0) (k : Fin 2) :
    (weightedRetainedMatrix2 B C k).det ≠ 0 := by
  fin_cases k <;> simp [weightedRetainedMatrix2, Matrix.det_fin_two, hB, hC]

theorem weighted_constant_pos2 (A : ℚ) (hA : A ≠ 0) : 0 < threePlaceProduct A := by
  rw [← rationalPlaceNorm_product]
  exact Finset.prod_pos (fun tau _ => rationalPlaceNorm_pos tau hA)

theorem weighted_full_product2 (A B C : ℚ) (u v : fixedSUnitGroup)
    (heq : A+B*((u : ℚˣ) : ℚ)+C*((v : ℚˣ) : ℚ) = 0) :
    (∏ tau : Fin 3, rationalPlaceNorm tau ((u : ℚˣ) : ℚ) *
      rationalPlaceNorm tau ((v : ℚˣ) : ℚ) *
      rationalPlaceNorm tau (B*((u : ℚˣ) : ℚ)+C*((v : ℚˣ) : ℚ))) =
        threePlaceProduct A := by
  have hs : B*((u : ℚˣ) : ℚ)+C*((v : ℚˣ) : ℚ) = -A := by linarith
  rw [hs]
  simp only [Finset.prod_mul_distrib, rationalPlaceNorm_product,
    fixed_sunit_product_formula, one_mul]
  simp [threePlaceProduct]

theorem weighted_normalized_product2 (A B C : ℚ) (u v : fixedSUnitGroup)
    (heq : A+B*((u : ℚˣ) : ℚ)+C*((v : ℚˣ) : ℚ) = 0) :
    weightedNormalizedProduct2 B C ((u : ℚˣ) : ℚ) ((v : ℚˣ) : ℚ) =
      threePlaceProduct A / pairHeight ((u : ℚˣ) : ℚ) ((v : ℚˣ) : ℚ)^3 := by
  let a : ℚ := ((u : ℚˣ) : ℚ)
  let b : ℚ := ((v : ℚˣ) : ℚ)
  have hH : 0 < pairHeight a b := pairHeight_pos (Units.ne_zero (u : ℚˣ))
  have hret : weightedRetainedProduct2 B C a b * pairHeight a b = threePlaceProduct A := by
    rw [weightedRetainedProduct2, pairHeight, ← Finset.prod_mul_distrib]
    have hlocal (tau : Fin 3) :
        min (rationalPlaceNorm tau a) (rationalPlaceNorm tau b) *
          rationalPlaceNorm tau (B*a+C*b) * localPairHeight tau a b =
        rationalPlaceNorm tau a * rationalPlaceNorm tau b * rationalPlaceNorm tau (B*a+C*b) := by
      dsimp [localPairHeight]
      rw [mul_right_comm, min_mul_max]
    simp_rw [hlocal]
    exact weighted_full_product2 A B C u v heq
  have hnorm : weightedNormalizedProduct2 B C a b =
      weightedRetainedProduct2 B C a b / pairHeight a b ^ 2 := by
    unfold weightedNormalizedProduct2 weightedRetainedProduct2 pairHeight
    simp_rw [div_mul_div_comm, ← pow_two]
    rw [Finset.prod_div_distrib, Finset.prod_pow]
  change weightedNormalizedProduct2 B C a b = _
  rw [hnorm]
  change weightedRetainedProduct2 B C a b / pairHeight a b ^ 2 =
    threePlaceProduct A / pairHeight a b ^ 3
  rw [← hret]
  field_simp [hH.ne']
  ring


theorem weighted_eight_patterns2 (B C u v : ℚ) :
    ∃ choice : Fin 3 → Fin 2,
      (∏ tau : Fin 3, ∏ j : Fin 2,
        rationalPlaceNorm tau ((weightedRetainedMatrix2 B C (choice tau) *ᵥ ![u,v]) j)) =
      weightedRetainedProduct2 B C u v := by
  choose choice hc using (fun tau => exists_retained_coordinate tau u v)
  refine ⟨choice, Finset.prod_congr rfl ?_⟩
  intro tau _
  have h := hc tau
  by_cases hk : choice tau = 0
  · simpa [weightedRetainedMatrix2, Fin.prod_univ_two, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, hk] using congrArg
        (fun t => t * rationalPlaceNorm tau (B*u+C*v)) h
  · have hk1 : choice tau = 1 := by omega
    simpa [weightedRetainedMatrix2, Fin.prod_univ_two, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, hk1] using congrArg
        (fun t => t * rationalPlaceNorm tau (B*u+C*v)) h

theorem weighted_large_height_scalar2 (K H : ℝ) (hK : 0 < K)
    (hH : max 1 (K^2) < H) : K / H^3 < H^(-(5 : ℝ)/2) := by
  have hH0 : 0 < H := lt_trans zero_lt_one (lt_of_le_of_lt (le_max_left _ _) hH)
  have hKH : K^2 < H := lt_of_le_of_lt (le_max_right _ _) hH
  have hs : (H^((1 : ℝ)/2))^2 = H := by
    rw [← Real.rpow_mul_natCast hH0.le]
    norm_num
  have hs0 : 0 < H^((1 : ℝ)/2) := Real.rpow_pos_of_pos hH0 _
  have hless : K < H^((1 : ℝ)/2) := by nlinarith
  apply (div_lt_iff₀ (pow_pos hH0 3)).mpr
  have he : H^(-(5 : ℝ)/2) * H^3 = H^((1 : ℝ)/2) := by
    have hp3 : H^(3 : ℕ) = H^(3 : ℝ) := (Real.rpow_natCast H 3).symm
    rw [hp3, ← Real.rpow_add hH0]
    norm_num
  rw [he]
  exact hless

theorem weighted_strict_product2 (A B C : ℚ) (hA : A ≠ 0) (u v : fixedSUnitGroup)
    (heq : A+B*((u : ℚˣ) : ℚ)+C*((v : ℚˣ) : ℚ) = 0)
    (hH : max 1 ((threePlaceProduct A : ℝ)^2) <
      (pairHeight ((u : ℚˣ) : ℚ) ((v : ℚˣ) : ℚ) : ℝ)) :
    (weightedNormalizedProduct2 B C ((u : ℚˣ) : ℚ) ((v : ℚˣ) : ℚ) : ℝ) <
      (pairHeight ((u : ℚˣ) : ℚ) ((v : ℚˣ) : ℚ) : ℝ)^(-(5 : ℝ)/2) := by
  rw [weighted_normalized_product2 A B C u v heq]
  push_cast
  exact weighted_large_height_scalar2 (threePlaceProduct A : ℝ) _
    (by exact_mod_cast weighted_constant_pos2 A hA) hH

theorem weighted_pattern_count2 : Fintype.card (Fin 3 → Fin 2) = 8 := by decide

end JSP000334
