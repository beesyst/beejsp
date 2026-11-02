import SubspaceBridge.BinaryLocalMass2
import SubspaceBridge.AuxiliaryProductFormula
open scoped BigOperators Classical
namespace JSP000334

theorem binary_derivative_homogeneous {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P)
    (J : RothBlockVars2 m →₀ ℕ) :
    binaryBlockHomogeneous (fun h => r h - ∑ i : Fin 2, J (h,i)) (binaryDividedDerivative J P) := by
  intro d hd h
  change (∑ i : Fin 2, d (h,i)) = r h-∑ i : Fin 2, J (h,i)
  have hn := MvPolynomial.mem_support_iff.mp hd
  have hc : P.coeff (d+J) ≠ 0 := by
    intro hz
    rw [binary_derivative_coeff,hz,zero_mul] at hn
    exact hn rfl
  have hh := hP (d+J) (MvPolynomial.mem_support_iff.mpr hc) h
  simp only [Finsupp.add_apply,Finset.sum_add_distrib] at hh
  omega

theorem binary_homogeneous_scale_eval {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P)
    (s : Fin m → ℚ) (x : RothBlockVars2 m → ℚ) :
    MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun u => s u.1*x u) P =
      (∏ h, s h^r h)*MvPolynomial.eval₂ (Int.castRingHom ℚ) x P := by
  classical
  conv_lhs => arg 3; rw [MvPolynomial.as_sum P]
  conv_rhs => arg 2; arg 3; rw [MvPolynomial.as_sum P]
  rw [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [MvPolynomial.eval₂_monomial,MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_fintype b (fun n e => (s n.1*x n)^e) (fun _ => pow_zero _),
    Finsupp.prod_fintype b (fun n e => x n^e) (fun _ => pow_zero _)]
  simp only [mul_pow,Finset.prod_mul_distrib]
  have hs : (∏ u : RothBlockVars2 m, s u.1^b u) = ∏ h, s h^r h := by
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro h _
    change (∏ i : Fin 2, s h^b (h,i)) = s h^r h
    rw [Finset.prod_pow_eq_pow_sum,hP b hb h]
  rw [hs]
  ring

noncomputable def binaryIntegerVectorRestriction {m : ℕ} (w : Fin m → Fin 2 → ℤ)
    (J : RothBlockVars2 m →₀ ℕ) (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    MvPolynomial (Fin m) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => MvPolynomial.C (w u.1 u.2)*MvPolynomial.X u.1)
    (binaryDividedDerivative J P)

theorem binary_monomial_product {σ ι : Type*} (s : Finset ι)
    (b : ι → σ →₀ ℕ) (c : ι → ℤ) :
    (∏ i ∈ s, MvPolynomial.monomial (b i) (c i)) =
      MvPolynomial.monomial (∑ i ∈ s,b i) (∏ i ∈ s,c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ih,MvPolynomial.monomial_mul]

theorem binary_integer_restriction_coefficient {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P)
    (w : Fin m → Fin 2 → ℤ) (J : RothBlockVars2 m →₀ ℕ) :
    binaryIntegerVectorRestriction w J P =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun h => r h-∑ i : Fin 2,J (h,i)))
        (MvPolynomial.eval (fun u => w u.1 u.2) (binaryDividedDerivative J P)) := by
  classical
  let Q := binaryDividedDerivative J P
  have hQ := binary_derivative_homogeneous r P hP J
  change MvPolynomial.eval₂Hom MvPolynomial.C _ Q =
    MvPolynomial.monomial _ (MvPolynomial.eval (fun u => w u.1 u.2) Q)
  conv_lhs => arg 2; rw [MvPolynomial.as_sum Q]
  rw [map_sum]
  conv_rhs => arg 2; arg 2; rw [MvPolynomial.as_sum Q]
  rw [MvPolynomial.eval_sum, map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [MvPolynomial.eval₂Hom_monomial,MvPolynomial.eval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp only [mul_pow, ← map_pow,MvPolynomial.X_pow_eq_monomial,Finset.prod_mul_distrib,
    ← map_prod,MvPolynomial.C_mul_monomial]
  have he : (∑ u : RothBlockVars2 m, Finsupp.single u.1 (b u)) =
      Finsupp.equivFunOnFinite.symm (fun h => r h-∑ i : Fin 2,J (h,i)) := by
    ext h
    rw [Finsupp.finset_sum_apply,Fintype.sum_prod_type]
    simp only [Finsupp.single_apply,Finsupp.equivFunOnFinite]
    calc
      _ = ∑ i : Fin 2,b (h,i) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        simp [eq_comm]
      _ = _ := hQ b hb h
  rw [binary_monomial_product,he]
  change MvPolynomial.C (Q.coeff b) * _ = _
  rw [MvPolynomial.C_mul_monomial]
  congr 1
  rw [Finsupp.prod_fintype b (fun u n => w u.1 u.2^n) (fun _ => pow_zero _)]
  simp only [mul_one]

end JSP000334
