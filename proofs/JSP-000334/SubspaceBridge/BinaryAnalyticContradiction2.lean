import SubspaceBridge.BinaryIntegerProduct2
open scoped BigOperators Classical
namespace JSP000334

theorem binary_auxiliary_integer_analytic_contradiction
    (L : Fin 3 → Matrix (Fin 2) (Fin 2) ℤ)
    (hL : ∀ tau,(binaryLocalRationalMatrix (L tau)).det ≠ 0) :
    ∃ D E : ℝ,1≤D ∧ 1≤E ∧
    ∀ eta : ℝ,0<eta → eta<1/2 →
    ∀ m : ℕ,∀ hm : 0<m,4*(eta^2)⁻¹*Real.log 12≤(m : ℝ) →
    ∀ r : Fin m → ℕ,(∀ h,0<r h) →
    ∀ theta Gamma : ℝ,0<theta → theta<1/12 → theta≤2*eta*m → 0<Gamma → Gamma≤1 →
    (∀ (h : Fin m) (hh : h.val+1<m),
      (r ⟨h.val+1,hh⟩ : ℝ)≤rothInductionOmega m theta*(r h : ℝ)) →
    ∀ delta : ℝ,40*eta<delta → delta<1 →
    ∀ c : Fin 3 → Fin 2 → ℝ,(∑ tau : Fin 3,∑ i : Fin 2,c tau i)=0 → (∀ tau i,|c tau i|≤1) →
    ∀ Q : Fin m → ℝ,(∀ h,1<Q h) → (∀ h,2*E<Real.rpow (Q h) eta) →
    (∀ h,(r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩)≤(r h : ℝ)*Real.log (Q h) ∧
      (r h : ℝ)*Real.log (Q h)≤(1+eta)*(r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩)) →
    ∀ V : Fin m → Fin 2 → ℤ,
    (∀ h,(∃ i,V h i ≠ 0) ∧ Ideal.span (Set.range (V h))=⊤) →
    (∀ h : Fin m,h.val ≠ 0 →
      Real.rpow (binaryNormalHeight (V ⟨0,hm⟩) : ℝ) ((r ⟨0,hm⟩ : ℝ)*Gamma)≤
        (binaryNormalHeight (V h) : ℝ)^r h) →
    (∀ h,(2 : ℝ)^(3*m)≤Real.rpow (binaryNormalHeight (V h) : ℝ) (rothInductionOmega m theta*Gamma)) →
    D^(∑ h,r h)≤Real.rpow (binaryNormalHeight (V ⟨0,hm⟩) : ℝ)
      (rothInductionOmega m theta*(r ⟨0,hm⟩ : ℝ)*Gamma) →
    (∀ tau h i,rothLocalAbs tau (binaryLocalVectorValue (L tau) (binaryKernelVector (V h)) i)≤
      Real.rpow (Q h) (c tau i-if tau=0 then delta else 0)) → False := by
  obtain ⟨D,hD,hconstruction⟩ := binary_auxiliary_integer_three_place L hL
  let G := binaryLocalInverseBound L
  let E := 8*D*G
  have hG : 1≤G := binaryLocalInverseBound_one_le L
  have hE : 1≤E := by dsimp [E];nlinarith
  refine ⟨D,E,hD,hE,?_⟩
  intro eta heta heta1 m hm hms r hr theta Gamma ht ht1 htbudget hGamma hGamma1 hsep
  intro delta hdelta hdelta1 c hcsum hc Q hQ hcutoff hlog V hrow hgrowth hden hheight hlocal
  obtain ⟨P,hnP,hP,hHP,hindex⟩ := hconstruction eta heta heta1 m hms r hr
  obtain ⟨J,k,hJ,hk,hn⟩ := binary_kernel_omega65_nonvanishing m hm theta Gamma ht ht1 hGamma hGamma1
    r V P hr hsep hrow hgrowth hden hnP hP (hHP.trans hheight)
  obtain ⟨e,z,hnz,hzcoeff,hzeval⟩ := binary_nonzero_integer_coefficient r V P hP J k hk hn
  let A := (r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩)
  have hA : 0≤A := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (hQ _).le)
  have hlogA : ∀ h,A≤(r h : ℝ)*Real.log (Q h) ∧ (r h : ℝ)*Real.log (Q h)≤(1+eta)*A := by
    simpa only [A,mul_assoc] using hlog
  have hbound (tau : Fin 3) : rothLocalAbs tau (z : ℚ)≤binarySourceBound tau E eta A r c := by
    rw [hzeval]
    exact binary_integer_local_bound r hr P hP D hD hHP tau (L tau) (hL tau) G hG
      (binaryLocalInverseBound_entry L tau) eta delta A heta hdelta hdelta1 hA Q hQ hlogA c hc
      (hindex tau) (fun h => binaryKernelVector (V h)) (hlocal tau) J (hJ.trans htbudget)
  have hlo := rothInteger_three_place_lower z hnz
  have hhi := binary_integer_three_place_upper z E eta A (by linarith) r c hcsum hbound
  have hstrict := binary_product_bound_lt_one r hr Q ⟨0,hm⟩ E eta delta hE heta hdelta hdelta1 hQ
    hcutoff (fun h => (hlog h).2)
  exact (not_lt_of_ge hlo) (lt_of_le_of_lt hhi hstrict)

end JSP000334
