import SubspaceBridge.BinaryKernelPrimitive2
import SubspaceBridge.BinaryKernelDehom2
open scoped BigOperators Classical
namespace JSP000334

theorem binaryKernelRestriction_eval {m : ℕ} (V : Fin m → Fin 2 → ℤ)
    (k : Fin m → Fin 2) (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    MvPolynomial.eval₂ (RingHom.id ℚ) (fun _ => 1) (binaryKernelRestriction V k P) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ)
        (fun u => if u.2 = k u.1 then
          -(V u.1 (k u.1).rev : ℚ) / (V u.1 (k u.1) : ℚ) else 1) P := by
  let f := MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun _ : RothBlockVars2 m => (1 : ℚ))
  have hc : f.comp (Int.castRingHom (MvPolynomial (RothBlockVars2 m) ℚ)) = Int.castRingHom ℚ := by
    ext n
    simp [f]
  change f (MvPolynomial.eval₂Hom (Int.castRingHom _) (binaryKernelChart V k) P) = _
  rw [MvPolynomial.map_eval₂Hom, hc]
  change MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun u => f (binaryKernelChart V k u)) P = _
  congr 1
  funext u
  by_cases hp : u.2 = k u.1
  · simp only [binaryKernelChart, if_pos hp, map_neg, map_sum, map_mul]
    simp only [f, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, mul_one]
    generalize hk : k u.1 = l
    fin_cases l <;> simp [neg_div]
  · simp only [binaryKernelChart, if_neg hp, f, MvPolynomial.eval₂Hom_X']

theorem binary_kernel_omega65_nonvanishing_evaluation :
∀ (m : ℕ) (hm : 0 < m) (theta Gamma : ℝ),
    0 < theta → theta < 1/12 → 0 < Gamma → Gamma ≤ 1 →
    ∀ (r : Fin m → ℕ) (V : Fin m → Fin 2 → ℤ) (P : MvPolynomial (RothBlockVars2 m) ℤ),
    (∀ h, 0 < r h) →
    (∀ (h : Fin m) (hh : h.val+1 < m),
      (r ⟨h.val+1,hh⟩ : ℝ) ≤ rothInductionOmega m theta*(r h : ℝ)) →
    (∀ h, (∃ i, V h i ≠ 0) ∧ Ideal.span (Set.range (V h)) = ⊤) →
    (∀ h : Fin m, h.val ≠ 0 →
      Real.rpow (binaryNormalHeight (V ⟨0,hm⟩) : ℝ) ((r ⟨0,hm⟩ : ℝ)*Gamma) ≤
        (binaryNormalHeight (V h) : ℝ)^r h) →
    (∀ h, (2 : ℝ)^(3*m) ≤ Real.rpow (binaryNormalHeight (V h) : ℝ) (rothInductionOmega m theta*Gamma)) →
    P ≠ 0 → binaryBlockHomogeneous r P →
    (binaryPolynomialHeight P : ℝ) ≤ Real.rpow (binaryNormalHeight (V ⟨0,hm⟩) : ℝ)
      (rothInductionOmega m theta*(r ⟨0,hm⟩ : ℝ)*Gamma) →
    ∃ (J : RothBlockVars2 m →₀ ℕ) (k : Fin m → Fin 2),
      binarySourceDerivativeWeight r J ≤ theta ∧ (∀ h, V h (k h) ≠ 0) ∧
        MvPolynomial.eval₂ (Int.castRingHom ℚ)
          (fun u => if u.2 = k u.1 then
            -(V u.1 (k u.1).rev : ℚ)/(V u.1 (k u.1) : ℚ) else 1)
          (binaryDividedDerivative J P) ≠ 0 := by
  intro m hm theta Gamma ht ht' hG hG' r V P hr hsep hrow hgrowth hden hP hhom hheight
  classical
  choose k hk hcop hmax using
    (fun h => binary_primitive_parameters (V h) (hrow h).1 (hrow h).2)
  let p : Fin m → ℤ := fun h => -(V h (k h).rev)
  let q : Fin m → ℤ := fun h => V h (k h)
  have hQ (h) : |(q h : ℝ)| = (binaryNormalHeight (V h) : ℝ) := by
    rw [← hmax h]
    simp only [q, Int.cast_natAbs, Int.cast_abs]
  obtain ⟨hF,hHF,hdegF⟩ := binaryKernelDehom_nonzero_height_degree k P hP r hhom
  have hFH : (rothIntegerHeight (binaryKernelDehom k P) : ℝ) ≤
      Real.rpow |(q ⟨0,hm⟩ : ℝ)| (rothInductionOmega m theta*(r ⟨0,hm⟩ : ℝ)*Gamma) := by
    rw [hQ]
    exact (by exact_mod_cast hHF :
      (rothIntegerHeight (binaryKernelDehom k P) : ℝ) ≤ (binaryPolynomialHeight P : ℝ)).trans hheight
  obtain ⟨a,ha,hne⟩ := roth_scalar_omega65_nonvanishing m hm theta Gamma ht ht' hG hG'
    r p q (binaryKernelDehom k P) hr hsep (fun h => ⟨hk h,hcop h⟩)
    (by simpa only [hQ, Real.rpow_natCast] using hgrowth)
    (by simpa only [hQ] using hden) hF hdegF hFH
  refine ⟨binaryKernelPivotOrder k a,k,?_,hk,?_⟩
  · simpa only [binarySourceDerivativeWeight,binaryKernelPivotOrder_budget] using ha
  · rw [binaryKernelDehom_derivative,binaryKernelDehom_eval] at hne
    have hpq : (fun u : RothBlockVars2 m => if u.2=k u.1 then (p u.1 : ℚ)/(q u.1 : ℚ) else 1) =
        (fun u => if u.2=k u.1 then -(V u.1 (k u.1).rev : ℚ)/(V u.1 (k u.1) : ℚ) else 1) := by
      funext u
      simp only [p,q,Int.cast_neg]
    rw [hpq] at hne
    exact hne

theorem binary_kernel_omega65_nonvanishing :
∀ (m : ℕ) (hm : 0 < m) (theta Gamma : ℝ),
    0 < theta → theta < 1/12 → 0 < Gamma → Gamma ≤ 1 →
    ∀ (r : Fin m → ℕ) (V : Fin m → Fin 2 → ℤ) (P : MvPolynomial (RothBlockVars2 m) ℤ),
    (∀ h, 0 < r h) →
    (∀ (h : Fin m) (hh : h.val+1 < m),
      (r ⟨h.val+1,hh⟩ : ℝ) ≤ rothInductionOmega m theta*(r h : ℝ)) →
    (∀ h, (∃ i, V h i ≠ 0) ∧ Ideal.span (Set.range (V h)) = ⊤) →
    (∀ h : Fin m, h.val ≠ 0 →
      Real.rpow (binaryNormalHeight (V ⟨0,hm⟩) : ℝ) ((r ⟨0,hm⟩ : ℝ)*Gamma) ≤
        (binaryNormalHeight (V h) : ℝ)^r h) →
    (∀ h, (2 : ℝ)^(3*m) ≤ Real.rpow (binaryNormalHeight (V h) : ℝ) (rothInductionOmega m theta*Gamma)) →
    P ≠ 0 → binaryBlockHomogeneous r P →
    (binaryPolynomialHeight P : ℝ) ≤ Real.rpow (binaryNormalHeight (V ⟨0,hm⟩) : ℝ)
      (rothInductionOmega m theta*(r ⟨0,hm⟩ : ℝ)*Gamma) →
    ∃ (J : RothBlockVars2 m →₀ ℕ) (k : Fin m → Fin 2),
      binarySourceDerivativeWeight r J ≤ theta ∧ (∀ h, V h (k h) ≠ 0) ∧
        binaryKernelRestriction V k (binaryDividedDerivative J P) ≠ 0 := by
  intro m hm theta Gamma ht ht' hG hG' r V P hr hsep hrow hgrowth hden hP hhom hheight
  obtain ⟨J,k,hJ,hk,hne⟩ := binary_kernel_omega65_nonvanishing_evaluation
    m hm theta Gamma ht ht' hG hG' r V P hr hsep hrow hgrowth hden hP hhom hheight
  refine ⟨J,k,hJ,hk,?_⟩
  intro he
  apply hne
  rw [← binaryKernelRestriction_eval,he]
  simp
end JSP000334
