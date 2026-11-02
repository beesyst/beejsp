import SubspaceBridge.BinaryVectorEvaluation2
open scoped BigOperators Classical
namespace JSP000334

theorem binary_abs_sum {ι : Type*} (tau : Fin 3) (s : Finset ι) (x : ι → ℚ) :
    rothLocalAbs tau (∑ i ∈ s,x i) ≤ ∑ i ∈ s,rothLocalAbs tau (x i) := by
  induction s using Finset.induction_on with
  | empty => simp [rothLocalAbs_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (rothLocalAbs_add tau _ _).trans (add_le_add_left ih _)

theorem binary_local_value_product_bound {m : ℕ} (tau : Fin 3)
    (Q : Fin m → ℝ) (hQ : ∀ h,0<Q h) (c : Fin 3 → Fin 2 → ℝ) (delta : ℝ)
    (y : RothBlockVars2 m → ℚ)
    (hy : ∀ u,rothLocalAbs tau (y u) ≤ Real.rpow (Q u.1) (c tau u.2-if tau=0 then delta else 0))
    (b : RothBlockVars2 m →₀ ℕ) :
    rothLocalAbs tau (∏ u : RothBlockVars2 m,y u^b u) ≤
      Real.exp (binaryNormalLocalExponent tau Q c delta b) := by
  rw [rothNormalAbs_prod]
  simp only [rothNormalAbs_pow]
  calc
    _ ≤ ∏ u : RothBlockVars2 m,
        Real.rpow (Q u.1) (c tau u.2-if tau=0 then delta else 0)^b u := by
      apply Finset.prod_le_prod
      · intro u _; exact pow_nonneg (rothLocalAbs_nonneg _ _) _
      · intro u _
        exact pow_le_pow_left₀ (rothLocalAbs_nonneg _ _) (hy u) _
    _ = Real.exp (∑ u : RothBlockVars2 m,
        (b u : ℝ)*((c tau u.2-if tau=0 then delta else 0)*Real.log (Q u.1))) := by
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro u _
      rw [Real.rpow_eq_pow,Real.rpow_def_of_pos (hQ u.1),← Real.exp_nat_mul]
      congr 1
      ring
    _ = _ := by
      congr 1
      unfold binaryNormalLocalExponent binaryNormalLogWeight
      rw [Fintype.sum_prod_type,Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring

theorem binary_integer_local_bound {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h,0<r h)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P)
    (D : ℝ) (hD : 1≤D) (hH : (binaryPolynomialHeight P : ℝ)≤D^(∑ h,r h))
    (tau : Fin 3) (L : Matrix (Fin 2) (Fin 2) ℤ) (hL : (binaryLocalRationalMatrix L).det ≠ 0)
    (G : ℝ) (hG : 1≤G) (hentry : ∀ i j,rothLocalAbs tau ((binaryLocalRationalMatrix L)⁻¹ i j)≤G)
    (eta delta A : ℝ) (heta : 0<eta) (hdelta : 40*eta<delta) (hdelta1 : delta<1) (hA : 0≤A)
    (Q : Fin m → ℝ) (hQ : ∀ h,1<Q h)
    (hlog : ∀ h,A≤(r h : ℝ)*Real.log (Q h) ∧ (r h : ℝ)*Real.log (Q h)≤(1+eta)*A)
    (c : Fin 3 → Fin 2 → ℝ) (hc : ∀ tau i,|c tau i|≤1)
    (hindex : ∀ i,binarySourceHighIndex r (fun _ => L i) ((1/2-eta)*m) P)
    (w : Fin m → Fin 2 → ℤ)
    (hw : ∀ h i,rothLocalAbs tau (binaryLocalVectorValue L (w h) i)≤
      Real.rpow (Q h) (c tau i-if tau=0 then delta else 0))
    (J : RothBlockVars2 m →₀ ℕ) (hJ : binarySourceDerivativeWeight r J≤2*eta*m) :
    rothLocalAbs tau ((MvPolynomial.eval (fun u => w u.1 u.2) (binaryDividedDerivative J P) : ℤ) : ℚ) ≤
      (2*(8*D*G))^(∑ h,r h)*Real.exp (A*m*((∑ i : Fin 2,c tau i)/2+if tau=0 then -30*eta else 8*eta)) := by
  let F := binaryLocalExpansion L J P
  let R := ∑ h,r h
  let E := 8*D*G
  let X := A*m*((∑ i : Fin 2,c tau i)/2+if tau=0 then -30*eta else 8*eta)
  have hterm (b : RothBlockVars2 m →₀ ℕ) (hb : b ∈ F.support) :
      rothLocalAbs tau (F.coeff b*∏ u : RothBlockVars2 m,binaryLocalVectorValue L (w u.1) u.2^b u) ≤
        E^R*Real.exp X := by
    have hn : F.coeff b ≠ 0 := MvPolynomial.mem_support_iff.mp hb
    have hbal := binaryLocal_coefficient_balance r hr eta heta L hL P hP hindex J b hJ hn
    have hex := binaryNormal_source_exponent r hr Q eta delta A heta hdelta hdelta1 hA hlog c hc
      tau L J b P hP hn hJ hbal
    have hp := binary_local_value_product_bound tau Q (fun h => lt_trans zero_lt_one (hQ h)) c delta
      (fun u => binaryLocalVectorValue L (w u.1) u.2) (fun u => hw u.1 u.2) b
    rw [rothLocalAbs_mul]
    exact mul_le_mul (binaryLocal_expansion_coeff_bound r P hP D hD hH tau L G hG hentry J b)
      (hp.trans (Real.exp_le_exp.mpr hex)) (rothLocalAbs_nonneg _ _) (by dsimp [E,R]; positivity)
  rw [binary_vector_local_evaluation L hL w J P,MvPolynomial.eval₂_eq']
  change rothLocalAbs tau (∑ b ∈ F.support,F.coeff b*∏ u : RothBlockVars2 m,
    binaryLocalVectorValue L (w u.1) u.2^b u) ≤ _
  calc
    _ ≤ ∑ b ∈ F.support,rothLocalAbs tau (F.coeff b*∏ u : RothBlockVars2 m,
        binaryLocalVectorValue L (w u.1) u.2^b u) := binary_abs_sum _ _ _
    _ ≤ ∑ _b ∈ F.support,E^R*Real.exp X := Finset.sum_le_sum (fun b hb => hterm b hb)
    _ = (F.support.card : ℝ)*(E^R*Real.exp X) := by simp
    _ ≤ (2 : ℝ)^R*(E^R*Real.exp X) := by
      have hs : (F.support.card : ℝ)≤(2 : ℝ)^R := by exact_mod_cast binary_expansion_support_card r P hP L J
      exact mul_le_mul_of_nonneg_right hs (by dsimp [E,R]; positivity)
    _ = _ := by rw [← mul_assoc,← mul_pow]

end JSP000334
