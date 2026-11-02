import SubspaceBridge.BinaryAuxRational2
import SubspaceBridge.BinaryAnalyticContradiction2
open scoped BigOperators Classical Matrix
namespace JSP000334

theorem binary_weighted_normalization (B C u v : ℚ) :
    weightedNormalizedProduct2 B C u v=weightedRetainedProduct2 B C u v/pairHeight u v^2 := by
  unfold weightedNormalizedProduct2 weightedRetainedProduct2 pairHeight
  simp_rw [div_mul_div_comm,← pow_two]
  rw [Finset.prod_div_distrib,Finset.prod_pow]

theorem binary_primitive_retained_bound (B C : ℚ) (z : Fin 2 → ℤ) (hz : PrimitivePair z)
    (hH : 1<(archPairHeight z : ℝ))
    (hp : (weightedNormalizedProduct2 B C (z 0 : ℚ) (z 1 : ℚ) : ℝ)<
      Real.rpow (archPairHeight z : ℝ) (-(5 : ℝ)/2)) :
    (weightedRetainedProduct2 B C (z 0 : ℚ) (z 1 : ℚ) : ℝ)<
      Real.rpow (archPairHeight z : ℝ) (-(1 : ℝ)/2) := by
  rw [binary_weighted_normalization,primitive_pair_height z hz] at hp
  push_cast at hp
  have hpos : 0<(archPairHeight z : ℝ) := lt_trans zero_lt_one hH
  have hh := (div_lt_iff₀ (pow_pos hpos 2)).mp hp
  have he : Real.rpow (archPairHeight z : ℝ) (-(5 : ℝ)/2)*(archPairHeight z : ℝ)^2=
      Real.rpow (archPairHeight z : ℝ) (-(1 : ℝ)/2) := by
    rw [Real.rpow_eq_pow,← Real.rpow_natCast,← Real.rpow_add hpos]
    norm_num
  rwa [he] at hh

theorem binary_denominator_tail_bound (K H : ℝ) (hK : 0<K) (hH : 1<H) (hcut : K^4<H) :
    K*Real.rpow H (-(1 : ℝ)/2)<Real.rpow (H^4) (-(1 : ℝ)/16) := by
  have hH0 : 0<H := lt_trans zero_lt_one hH
  have hklog := Real.log_lt_log (pow_pos hK 4) hcut
  rw [Real.log_pow] at hklog
  norm_num only [Nat.cast_ofNat] at hklog
  have hk : K<H^((1 : ℝ)/4) := by
    apply (Real.log_lt_log_iff hK (Real.rpow_pos_of_pos hH0 _)).mp
    rw [Real.log_rpow hH0]
    nlinarith
  have hh := mul_lt_mul_of_pos_right hk (Real.rpow_pos_of_pos hH0 (-(1 : ℝ)/2))
  convert hh using 1
  rw [Real.rpow_eq_pow,← Real.rpow_natCast,← Real.rpow_mul hH0.le,← Real.rpow_add hH0]
  norm_num

theorem binary_place_norm_cast (tau : Fin 3) (x : ℚ) :
    (rationalPlaceNorm tau x : ℝ)=rothLocalAbs tau x := by
  fin_cases tau <;> simp [rationalPlaceNorm,rothLocalAbs]

theorem binary_integer_pattern_value (B C : ℚ) (d : ℕ) (b c : ℤ)
    (hb : (b : ℚ)=(d : ℚ)*B) (hc : (c : ℚ)=(d : ℚ)*C) (k i : Fin 2) (z : Fin 2 → ℤ) :
    binaryLocalVectorValue (binaryIntegerRetained2 d b c k) z i=
      (d : ℚ)*((weightedRetainedMatrix2 B C k *ᵥ fun j => (z j : ℚ)) i) := by
  have hh := congrFun (binary_integer_form_identity B C d b c hb hc k (fun j => (z j : ℚ))) i
  simpa [binaryLocalVectorValue,Matrix.mulVec,dotProduct] using hh

theorem binary_integer_pattern_product (B C : ℚ) (d : ℕ) (b c : ℤ)
    (hb : (b : ℚ)=(d : ℚ)*B) (hc : (c : ℚ)=(d : ℚ)*C) (z : Fin 2 → ℤ) :
    ∃ k : Fin 3 → Fin 2,
    (∏ tau : Fin 3,∏ i : Fin 2,rothLocalAbs tau (binaryLocalVectorValue (binaryIntegerRetained2 d b c (k tau)) z i))=
      (threePlaceProduct (d : ℚ) : ℝ)^2*(weightedRetainedProduct2 B C (z 0 : ℚ) (z 1 : ℚ) : ℝ) := by
  obtain ⟨k,hk⟩ := weighted_eight_patterns2 B C (z 0 : ℚ) (z 1 : ℚ)
  refine ⟨k,?_⟩
  have hz : (![ (z 0 : ℚ),(z 1 : ℚ)] : Fin 2 → ℚ)=(fun j => (z j : ℚ)) := by
    ext j
    fin_cases j <;> rfl
  rw [hz] at hk
  simp_rw [binary_integer_pattern_value B C d b c hb hc,← binary_place_norm_cast]
  simp only [← Rat.cast_prod]
  have hh := binary_denominator_norm_factor (d : ℚ)
    (fun tau i => ((weightedRetainedMatrix2 B C (k tau) *ᵥ fun j => (z j : ℚ)) i))
  rw [hk] at hh
  exact_mod_cast hh

end JSP000334
