import SubspaceBridge.BinaryKernelVector2
open scoped BigOperators Classical
namespace JSP000334

noncomputable def binaryVectorRecovery {m : ℕ} (V : Fin m → Fin 2 → ℤ)
    (k : Fin m → Fin 2) (h : Fin m) : MvPolynomial (RothBlockVars2 m) ℚ :=
  MvPolynomial.C ((binaryKernelVector (V h) (k h).rev : ℚ)⁻¹)*MvPolynomial.X (h,(k h).rev)

theorem binary_vector_chart_recovery {m : ℕ} (V : Fin m → Fin 2 → ℤ)
    (k : Fin m → Fin 2) (hk : ∀ h,V h (k h) ≠ 0) (u : RothBlockVars2 m) :
    MvPolynomial.C (binaryKernelVector (V u.1) u.2 : ℚ)*binaryVectorRecovery V k u.1 =
      binaryKernelChart V k u := by
  rcases u with ⟨h,i⟩
  have hf : (binaryKernelVector (V h) (k h).rev : ℚ) ≠ 0 := by
    exact_mod_cast binary_kernel_vector_free (V h) (k h) (hk h)
  let a : ℚ := if i=k h then -(V h (k h).rev : ℚ)/(V h (k h) : ℚ) else 1
  have hs : (binaryKernelVector (V h) i : ℚ)*(binaryKernelVector (V h) (k h).rev : ℚ)⁻¹ = a := by
    rw [binary_kernel_vector_normalized (V h) (k h) i (hk h)]
    change ((binaryKernelVector (V h) (k h).rev : ℚ)*a)*_ = a
    rw [mul_comm _ a,mul_assoc,mul_inv_cancel₀ hf,mul_one]
  unfold binaryVectorRecovery
  rw [← mul_assoc,← MvPolynomial.C_mul,hs]
  dsimp only [a]
  generalize he : k h = l
  fin_cases l <;> fin_cases i <;> simp [binaryKernelChart,he,neg_div,map_neg,neg_mul]

theorem binary_kernel_integer_factor {m : ℕ} (V : Fin m → Fin 2 → ℤ)
    (k : Fin m → Fin 2) (hk : ∀ h,V h (k h) ≠ 0)
    (J : RothBlockVars2 m →₀ ℕ) (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    MvPolynomial.eval₂Hom (Int.castRingHom _) (binaryVectorRecovery V k)
      (binaryIntegerVectorRestriction (fun h => binaryKernelVector (V h)) J P) =
        binaryKernelRestriction V k (binaryDividedDerivative J P) := by
  have he : (MvPolynomial.eval₂Hom (Int.castRingHom _) (binaryVectorRecovery V k)).comp
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (fun u => MvPolynomial.C (binaryKernelVector (V u.1) u.2)*MvPolynomial.X u.1)) =
      MvPolynomial.eval₂Hom (Int.castRingHom _) (binaryKernelChart V k) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro u
      simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_X',map_mul,MvPolynomial.eval₂Hom_C]
      exact binary_vector_chart_recovery V k hk u
  exact congrArg (fun f => f (binaryDividedDerivative J P)) he

theorem binary_nonzero_integer_coefficient {m : ℕ} (r : Fin m → ℕ)
    (V : Fin m → Fin 2 → ℤ) (P : MvPolynomial (RothBlockVars2 m) ℤ)
    (hP : binaryBlockHomogeneous r P) (J : RothBlockVars2 m →₀ ℕ)
    (k : Fin m → Fin 2) (hk : ∀ h,V h (k h) ≠ 0)
    (hn : binaryKernelRestriction V k (binaryDividedDerivative J P) ≠ 0) :
    ∃ (e : Fin m →₀ ℕ) (z : ℤ), z ≠ 0 ∧
      (binaryIntegerVectorRestriction (fun h => binaryKernelVector (V h)) J P).coeff e = z ∧
      z = MvPolynomial.eval (fun u => binaryKernelVector (V u.1) u.2) (binaryDividedDerivative J P) := by
  let z := MvPolynomial.eval (fun u => binaryKernelVector (V u.1) u.2) (binaryDividedDerivative J P)
  let e : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun h => r h-∑ i : Fin 2,J (h,i))
  have hr := binary_integer_restriction_coefficient r P hP (fun h => binaryKernelVector (V h)) J
  refine ⟨e,z,?_,?_,rfl⟩
  · intro hz
    apply hn
    rw [← binary_kernel_integer_factor V k hk J P,hr]
    change MvPolynomial.eval₂Hom (Int.castRingHom _) (binaryVectorRecovery V k)
      (MvPolynomial.monomial e z) = 0
    rw [hz,MvPolynomial.monomial_zero,map_zero]
  · rw [hr]
    simp [MvPolynomial.coeff_monomial,e,z]

theorem binary_integer_eval_cast {m : ℕ} (w : Fin m → Fin 2 → ℤ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    ((MvPolynomial.eval (fun u : RothBlockVars2 m => w u.1 u.2) P : ℤ) : ℚ) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun u : RothBlockVars2 m => (w u.1 u.2 : ℚ)) P := by
  have he : (Int.castRingHom ℚ).comp (MvPolynomial.eval (fun u : RothBlockVars2 m => w u.1 u.2)) =
      MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (fun u : RothBlockVars2 m => (w u.1 u.2 : ℚ)) := by
    apply MvPolynomial.ringHom_ext <;> intro u <;> simp
  exact congrArg (fun f => f P) he

theorem binary_integer_normalized_scale {m : ℕ} (r : Fin m → ℕ)
    (V : Fin m → Fin 2 → ℤ) (P : MvPolynomial (RothBlockVars2 m) ℤ)
    (hP : binaryBlockHomogeneous r P) (J : RothBlockVars2 m →₀ ℕ)
    (k : Fin m → Fin 2) (hk : ∀ h,V h (k h) ≠ 0) :
    ((MvPolynomial.eval (fun u => binaryKernelVector (V u.1) u.2)
      (binaryDividedDerivative J P) : ℤ) : ℚ) =
      (∏ h,(binaryKernelVector (V h) (k h).rev : ℚ)^(r h-∑ i : Fin 2,J (h,i)))*
        MvPolynomial.eval₂ (RingHom.id ℚ) (fun _ => 1)
          (binaryKernelRestriction V k (binaryDividedDerivative J P)) := by
  rw [binary_integer_eval_cast (fun h => binaryKernelVector (V h)),binaryKernelRestriction_eval]
  rw [← binary_homogeneous_scale_eval _ _ (binary_derivative_homogeneous r P hP J)]
  congr 1
  funext u
  exact binary_kernel_vector_normalized (V u.1) (k u.1) u.2 (hk u.1)

theorem binary_integer_block_scales_nonzero {m : ℕ} (r : Fin m → ℕ)
    (V : Fin m → Fin 2 → ℤ) (J : RothBlockVars2 m →₀ ℕ)
    (k : Fin m → Fin 2) (hk : ∀ h,V h (k h) ≠ 0) :
    (∏ h,(binaryKernelVector (V h) (k h).rev : ℚ)^(r h-∑ i : Fin 2,J (h,i))) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro h _
  apply pow_ne_zero
  exact_mod_cast binary_kernel_vector_free (V h) (k h) (hk h)

end JSP000334
