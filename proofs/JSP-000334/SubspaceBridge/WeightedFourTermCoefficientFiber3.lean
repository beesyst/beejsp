import SubspaceBridge.WeightedFourTermProjection3
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_four_term_fiber_all_nonzero3 (A B C D b0 b1 b2 : ℚ)
    (hA : A≠0) (h0 : b0≠0) (h1 : b1≠0) (h2 : b2≠0) :
    (weightedFourTermCoefficientFiber3 A B C D b0 b1 b2).Finite := by
  apply weighted_four_term_projection_finite3 _ b0 b1 b2 h0 h1 h2
    (fun p => (p.2.1/p.1,p.2.2/p.1))
    (fun r q => ![-A/(B+C*r+D*q),r*(-A/(B+C*r+D*q)),q*(-A/(B+C*r+D*q))])
  · intro p hp
    simp only [Subgroup.coe_div,Units.val_div_eq_div_val]
    have hu : ((p.1 : ℚˣ) : ℚ)≠0 := Units.ne_zero _
    field_simp
    linear_combination hp.2
  · intro p hp
    simp only [Subgroup.coe_div,Units.val_div_eq_div_val]
    obtain ⟨hd,hu,hv,hw⟩ := weighted_four_term_ratio_values3 A B C D
      ((p.1 : ℚˣ) : ℚ) ((p.2.1 : ℚˣ) : ℚ) ((p.2.2 : ℚˣ) : ℚ) hA (Units.ne_zero _) hp.1.1
    ext i
    fin_cases i
    · exact hu.symm
    · change (((p.2.1 : ℚˣ) : ℚ)/((p.1 : ℚˣ) : ℚ))*(-A/(B+C*(((p.2.1 : ℚˣ) : ℚ)/((p.1 : ℚˣ) : ℚ))+D*(((p.2.2 : ℚˣ) : ℚ)/((p.1 : ℚˣ) : ℚ))))=((p.2.1 : ℚˣ) : ℚ)
      rw [← hu]
      exact hv.symm
    · change (((p.2.2 : ℚˣ) : ℚ)/((p.1 : ℚˣ) : ℚ))*(-A/(B+C*(((p.2.1 : ℚˣ) : ℚ)/((p.1 : ℚˣ) : ℚ))+D*(((p.2.2 : ℚˣ) : ℚ)/((p.1 : ℚˣ) : ℚ))))=((p.2.2 : ℚˣ) : ℚ)
      rw [← hu]
      exact hw.symm

theorem weighted_four_term_fiber_zero_last3 (A B C D b0 b1 : ℚ)
    (hA : A≠0) (hD : D≠0) (hb : b1≠0) :
    (weightedFourTermCoefficientFiber3 A B C D b0 b1 0).Finite := by
  let k : ℚ := -b0/b1
  have hc : ∀ p∈weightedFourTermCoefficientFiber3 A B C D b0 b1 0,((p.2.1 : ℚˣ) : ℚ)=k*((p.1 : ℚˣ) : ℚ) := by
    intro p hp
    change ((p.2.1 : ℚˣ) : ℚ)=(-b0/b1)*((p.1 : ℚˣ) : ℚ)
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hb).mpr
    have he := hp.2
    nlinarith only [he]
  by_cases hk : B+C*k=0
  · apply Set.finite_empty.subset
    intro p hp
    have hn := (weighted_four_term_pair_sums3 hp.1).1
    have he : B*((p.1 : ℚˣ) : ℚ)+C*((p.2.1 : ℚˣ) : ℚ)=(B+C*k)*((p.1 : ℚˣ) : ℚ) := by rw [hc p hp];ring
    rw [hk,zero_mul] at he
    exact False.elim (hn he)
  · apply weighted_four_term_projection_finite3 _ A (B+C*k) D hA hk hD
      (fun p => (p.1,p.2.2)) (fun u w => ![u,k*u,w])
    · intro p hp
      have hs := hp.1.1
      rw [hc p hp] at hs
      nlinarith only [hs]
    · intro p hp
      ext i
      fin_cases i
      · rfl
      · exact (hc p hp).symm
      · rfl

theorem weighted_four_term_fiber_zero_middle3 (A B C D b0 b2 : ℚ)
    (hA : A≠0) (hC : C≠0) (hb : b2≠0) :
    (weightedFourTermCoefficientFiber3 A B C D b0 0 b2).Finite := by
  let k : ℚ := -b0/b2
  have hc : ∀ p∈weightedFourTermCoefficientFiber3 A B C D b0 0 b2,((p.2.2 : ℚˣ) : ℚ)=k*((p.1 : ℚˣ) : ℚ) := by
    intro p hp
    change ((p.2.2 : ℚˣ) : ℚ)=(-b0/b2)*((p.1 : ℚˣ) : ℚ)
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hb).mpr
    have he := hp.2
    nlinarith only [he]
  by_cases hk : B+D*k=0
  · apply Set.finite_empty.subset
    intro p hp
    have hn := (weighted_four_term_pair_sums3 hp.1).2.1
    have he : B*((p.1 : ℚˣ) : ℚ)+D*((p.2.2 : ℚˣ) : ℚ)=(B+D*k)*((p.1 : ℚˣ) : ℚ) := by rw [hc p hp];ring
    rw [hk,zero_mul] at he
    exact False.elim (hn he)
  · apply weighted_four_term_projection_finite3 _ A (B+D*k) C hA hk hC
      (fun p => (p.1,p.2.1)) (fun u v => ![u,v,k*u])
    · intro p hp
      have hs := hp.1.1
      rw [hc p hp] at hs
      nlinarith only [hs]
    · intro p hp
      ext i
      fin_cases i
      · rfl
      · rfl
      · exact (hc p hp).symm

theorem weighted_four_term_fiber_zero_first3 (A B C D b1 b2 : ℚ)
    (hA : A≠0) (hB : B≠0) (hb : b2≠0) :
    (weightedFourTermCoefficientFiber3 A B C D 0 b1 b2).Finite := by
  let k : ℚ := -b1/b2
  have hc : ∀ p∈weightedFourTermCoefficientFiber3 A B C D 0 b1 b2,((p.2.2 : ℚˣ) : ℚ)=k*((p.2.1 : ℚˣ) : ℚ) := by
    intro p hp
    change ((p.2.2 : ℚˣ) : ℚ)=(-b1/b2)*((p.2.1 : ℚˣ) : ℚ)
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hb).mpr
    have he := hp.2
    nlinarith only [he]
  by_cases hk : C+D*k=0
  · apply Set.finite_empty.subset
    intro p hp
    have hn := (weighted_four_term_pair_sums3 hp.1).2.2
    have he : C*((p.2.1 : ℚˣ) : ℚ)+D*((p.2.2 : ℚˣ) : ℚ)=(C+D*k)*((p.2.1 : ℚˣ) : ℚ) := by rw [hc p hp];ring
    rw [hk,zero_mul] at he
    exact False.elim (hn he)
  · apply weighted_four_term_projection_finite3 _ A B (C+D*k) hA hB hk
      (fun p => (p.1,p.2.1)) (fun u v => ![u,v,k*v])
    · intro p hp
      have hs := hp.1.1
      rw [hc p hp] at hs
      nlinarith only [hs]
    · intro p hp
      ext i
      fin_cases i
      · rfl
      · rfl
      · exact (hc p hp).symm

theorem weighted_four_term_coefficient_fiber_finite3 (A B C D b0 b1 b2 : ℚ)
    (hA : A≠0) (hB : B≠0) (hC : C≠0) (hD : D≠0)
    (hb : b0≠0 ∨ b1≠0 ∨ b2≠0) :
    (weightedFourTermCoefficientFiber3 A B C D b0 b1 b2).Finite := by
  by_cases h0 : b0=0
  · subst b0
    by_cases h1 : b1=0
    · subst b1
      have h2 : b2≠0 := by simpa using hb
      apply Set.finite_empty.subset
      intro p hp
      have he : b2*((p.2.2 : ℚˣ) : ℚ)=0 := by simpa using hp.2
      exact False.elim ((mul_ne_zero h2 (Units.ne_zero (p.2.2 : ℚˣ))) he)
    · by_cases h2 : b2=0
      · subst b2
        apply Set.finite_empty.subset
        intro p hp
        have he : b1*((p.2.1 : ℚˣ) : ℚ)=0 := by simpa using hp.2
        exact False.elim ((mul_ne_zero h1 (Units.ne_zero (p.2.1 : ℚˣ))) he)
      · exact weighted_four_term_fiber_zero_first3 A B C D b1 b2 hA hB h2
  · by_cases h1 : b1=0
    · subst b1
      by_cases h2 : b2=0
      · subst b2
        apply Set.finite_empty.subset
        intro p hp
        have he : b0*((p.1 : ℚˣ) : ℚ)=0 := by simpa using hp.2
        exact False.elim ((mul_ne_zero h0 (Units.ne_zero (p.1 : ℚˣ))) he)
      · exact weighted_four_term_fiber_zero_middle3 A B C D b0 b2 hA hC h2
    · by_cases h2 : b2=0
      · subst b2
        exact weighted_four_term_fiber_zero_last3 A B C D b0 b1 hA hD h1
      · exact weighted_four_term_fiber_all_nonzero3 A B C D b0 b1 b2 hA h0 h1 h2

end JSP000334
