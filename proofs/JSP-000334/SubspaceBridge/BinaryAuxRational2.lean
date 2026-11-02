import SubspaceBridge.WeightedTernaryProduct2
open scoped BigOperators Matrix
namespace JSP000334

theorem binary_common_denominator (B C : ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ b c : ℤ, (b : ℚ)=(d : ℚ)*B ∧ (c : ℚ)=(d : ℚ)*C := by
  have hb : (B.num : ℚ)=(B.den : ℚ)*B := by simpa [integralPair] using integralPair_scale B (1 : Fin 2)
  have hc : (C.num : ℚ)=(C.den : ℚ)*C := by simpa [integralPair] using integralPair_scale C (1 : Fin 2)
  refine ⟨B.den*C.den,Nat.mul_pos B.pos C.pos,B.num*(C.den : ℤ),C.num*(B.den : ℤ),?_,?_⟩
  · push_cast
    rw [hb]
    ring
  · push_cast
    rw [hc]
    ring

def binaryIntegerRetained2 (d : ℕ) (b c : ℤ) (k : Fin 2) : Matrix (Fin 2) (Fin 2) ℤ :=
  if k=0 then !![(d : ℤ),0;b,c] else !![0,(d : ℤ);b,c]

theorem binary_integer_retained_cast (B C : ℚ) (d : ℕ) (b c : ℤ)
    (hb : (b : ℚ)=(d : ℚ)*B) (hc : (c : ℚ)=(d : ℚ)*C) (k : Fin 2) :
    (fun i j => (binaryIntegerRetained2 d b c k i j : ℚ)) = (d : ℚ) • weightedRetainedMatrix2 B C k := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [binaryIntegerRetained2,weightedRetainedMatrix2,hb,hc]

theorem binary_integer_retained_det (B C : ℚ) (hB : B ≠ 0) (hC : C ≠ 0)
    (d : ℕ) (hd : 0 < d) (b c : ℤ) (hb : (b : ℚ)=(d : ℚ)*B) (hc : (c : ℚ)=(d : ℚ)*C)
    (k : Fin 2) : Matrix.det (fun i j => (binaryIntegerRetained2 d b c k i j : ℚ)) ≠ 0 := by
  rw [binary_integer_retained_cast B C d b c hb hc k,Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (ne_of_gt hd)))
    (weighted_retained_det2 B C hB hC k)

theorem binary_integer_form_identity (B C : ℚ) (d : ℕ) (b c : ℤ)
    (hb : (b : ℚ)=(d : ℚ)*B) (hc : (c : ℚ)=(d : ℚ)*C) (k : Fin 2) (x : Fin 2 → ℚ) :
    (fun i j => (binaryIntegerRetained2 d b c k i j : ℚ))*ᵥ x =
      (d : ℚ) • (weightedRetainedMatrix2 B C k *ᵥ x) := by
  rw [binary_integer_retained_cast B C d b c hb hc k,Matrix.smul_mulVec_assoc]

theorem binary_denominator_norm_factor (d : ℚ) (y : Fin 3 → Fin 2 → ℚ) :
    (∏ tau : Fin 3, ∏ j : Fin 2, rationalPlaceNorm tau (d*y tau j)) =
      (threePlaceProduct d)^2*(∏ tau : Fin 3, ∏ j : Fin 2, rationalPlaceNorm tau (y tau j)) := by
  have hn (tau : Fin 3) (q : ℚ) : rationalPlaceNorm tau (d*q) =
      rationalPlaceNorm tau d*rationalPlaceNorm tau q := by
    fin_cases tau <;> simp [rationalPlaceNorm,abs_mul]
  simp_rw [hn,Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Finset.prod_pow,rationalPlaceNorm_product]

end JSP000334
