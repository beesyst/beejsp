import SubspaceBridge.WeightedTernaryProduct2
namespace JSP000334

def weightedFixedSUnitPairs (A B C : ℚ) : Set (fixedSUnitGroup × fixedSUnitGroup) :=
  {p | A+B*((p.1 : ℚˣ) : ℚ)+C*((p.2 : ℚˣ) : ℚ)=0}

theorem weighted_pair_primitive_transport (u v : fixedSUnitGroup) :
    ∃ z : Fin 2 → ℤ, ∃ s : fixedSUnitGroup,
      z = integralPair ((((v/u : fixedSUnitGroup) : ℚˣ) : ℚ)) ∧
      PrimitivePair z ∧ z 0 ≠ 0 ∧ z 1 ≠ 0 ∧
      (z 0 : ℚ) = ((s : ℚˣ) : ℚ)*((u : ℚˣ) : ℚ) ∧
      (z 1 : ℚ) = ((s : ℚˣ) : ℚ)*((v : ℚˣ) : ℚ) ∧
      pairHeight ((u : ℚˣ) : ℚ) ((v : ℚˣ) : ℚ) = archPairHeight z := by
  let q : fixedSUnitGroup := v/u
  let a : ℚ := ((u : ℚˣ) : ℚ)
  let b : ℚ := ((v : ℚˣ) : ℚ)
  have ha : a ≠ 0 := Units.ne_zero _
  have hq : ((q : ℚˣ) : ℚ) = b/a := by simp [q, a, b]
  obtain ⟨d, hd⟩ := sunit_denominator q
  let s : fixedSUnitGroup := d/u
  let z := integralPair ((q : ℚˣ) : ℚ)
  have hs : ((s : ℚˣ) : ℚ) = ((d : ℚˣ) : ℚ)/a := by simp [s, a]
  have h0 : (z 0 : ℚ) = ((s : ℚˣ) : ℚ)*a := by
    rw [hs, div_mul_cancel₀ _ ha, hd]
    simpa only [Matrix.cons_val_zero, mul_one] using integralPair_scale ((q : ℚˣ) : ℚ) 0
  have h1 : (z 1 : ℚ) = ((s : ℚˣ) : ℚ)*b := by
    have hh := integralPair_scale ((q : ℚˣ) : ℚ) 1
    change (z 1 : ℚ) = _ at hh
    change (z 1 : ℚ) = (((q : ℚˣ) : ℚ).den : ℚ)*((q : ℚˣ) : ℚ) at hh
    rw [← hd, hq] at hh
    rw [hs, hh]
    ring
  have hz : PrimitivePair z := integralPair_primitive _
  have hz0 : z 0 ≠ 0 := by
    intro he
    have heq := h0
    rw [he, Int.cast_zero] at heq
    exact (mul_ne_zero (Units.ne_zero _) ha) heq.symm
  have hz1 : z 1 ≠ 0 := by
    intro he
    have heq := h1
    rw [he, Int.cast_zero] at heq
    exact (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) heq.symm
  refine ⟨z,s,rfl,hz,hz0,hz1,h0,h1,?_⟩
  have hh := primitive_pair_height z hz
  rw [h0,h1,pairHeight_sunit_scale] at hh
  exact hh

theorem weighted_normalized_sunit_scale2 (B C : ℚ) (s : fixedSUnitGroup) (u v : ℚ) :
    weightedNormalizedProduct2 B C (((s : ℚˣ) : ℚ)*u) (((s : ℚˣ) : ℚ)*v) =
      weightedNormalizedProduct2 B C u v := by
  let a : ℚ := ((s : ℚˣ) : ℚ)
  have hmul (tau : Fin 3) (q : ℚ) :
      rationalPlaceNorm tau (a*q) = rationalPlaceNorm tau a*rationalPlaceNorm tau q := by
    fin_cases tau <;> simp [rationalPlaceNorm, abs_mul]
  have hpos (tau : Fin 3) : 0 < rationalPlaceNorm tau a :=
    rationalPlaceNorm_pos tau (Units.ne_zero _)
  have hform : B*(a*u)+C*(a*v)=a*(B*u+C*v) := by ring
  unfold weightedNormalizedProduct2
  apply Finset.prod_congr rfl
  intro tau _
  change (min (rationalPlaceNorm tau (a*u)) (rationalPlaceNorm tau (a*v)) /
    localPairHeight tau (a*u) (a*v)) *
    (rationalPlaceNorm tau (B*(a*u)+C*(a*v)) / localPairHeight tau (a*u) (a*v)) = _
  rw [hform]
  simp only [localPairHeight, hmul]
  rw [← mul_min_of_nonneg _ _ (hpos tau).le, ← mul_max_of_nonneg _ _ (hpos tau).le]
  rw [mul_div_mul_left _ _ (hpos tau).ne', mul_div_mul_left _ _ (hpos tau).ne']

end JSP000334
