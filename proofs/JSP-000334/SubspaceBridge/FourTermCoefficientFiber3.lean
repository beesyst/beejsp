import SubspaceBridge.FourTermProjection3
import SubspaceBridge.FourTermSource3
namespace JSP000334

theorem four_term_fiber_all_nonzero (a0 a1 a2 : ℚ) (h0 : a0≠0) (h1 : a1≠0) (h2 : a2≠0) :
    (fourTermCoefficientFiber a0 a1 a2).Finite := by
  apply four_term_weighted_projection_finite _ (fun _ hx => hx.1) a0 a1 a2 h0 h1 h2 1 2
    (fun u v => ![1,u,v,-1-u-v])
  · intro x hx
    simpa only [hx.1.1,mul_one] using hx.2
  · intro x hx
    exact four_term_coordinate_reconstruction x hx.1.1 (four_term_relation_facts hx.1).2.1

theorem four_term_fiber_fixed_first (a0 a1 : ℚ) (h1 : a1≠0) :
    (fourTermCoefficientFiber a0 a1 0).Finite := by
  let k : ℚ := -a0/a1
  have hc : ∀ x∈fourTermCoefficientFiber a0 a1 0,x 1=k := by
    intro x hx
    apply (eq_div_iff h1).mpr
    have he := hx.2
    rw [hx.1.1] at he
    nlinarith only [he]
  by_cases hk : 1+k=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := (four_term_relation_facts hx.1).2.2.1
    exact False.elim (hn (by rw [hx.1.1,hc x hx]; exact hk))
  · apply four_term_weighted_projection_finite _ (fun _ hx => hx.1) (1+k) 1 1 hk
      one_ne_zero one_ne_zero 2 3 (fun v t => ![1,k,v,t])
    · intro x hx
      have hs := (four_term_relation_facts hx.1).2.1
      rw [hx.1.1,hc x hx] at hs
      simpa only [one_mul] using hs
    · intro x hx
      ext i
      fin_cases i
      · exact hx.1.1.symm
      · exact (hc x hx).symm
      · rfl
      · rfl

theorem four_term_fiber_fixed_second (a0 a2 : ℚ) (h2 : a2≠0) :
    (fourTermCoefficientFiber a0 0 a2).Finite := by
  let k : ℚ := -a0/a2
  have hc : ∀ x∈fourTermCoefficientFiber a0 0 a2,x 2=k := by
    intro x hx
    apply (eq_div_iff h2).mpr
    have he := hx.2
    rw [hx.1.1] at he
    nlinarith only [he]
  by_cases hk : 1+k=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := (four_term_relation_facts hx.1).2.2.2.1
    exact False.elim (hn (by rw [hx.1.1,hc x hx]; exact hk))
  · apply four_term_weighted_projection_finite _ (fun _ hx => hx.1) (1+k) 1 1 hk
      one_ne_zero one_ne_zero 1 3 (fun u t => ![1,u,k,t])
    · intro x hx
      have hs := (four_term_relation_facts hx.1).2.1
      rw [hx.1.1,hc x hx] at hs
      simp only [one_mul]
      linarith only [hs]
    · intro x hx
      ext i
      fin_cases i
      · exact hx.1.1.symm
      · rfl
      · exact (hc x hx).symm
      · rfl

theorem four_term_fiber_ratio (a1 a2 : ℚ) (h2 : a2≠0) :
    (fourTermCoefficientFiber 0 a1 a2).Finite := by
  let k : ℚ := -a1/a2
  have hc : ∀ x∈fourTermCoefficientFiber 0 a1 a2,x 2=k*x 1 := by
    intro x hx
    change x 2=(-a1/a2)*x 1
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff h2).mpr
    have he := hx.2
    nlinarith only [he]
  by_cases hk : 1+k=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := (four_term_relation_facts hx.1).2.2.2.2.1
    have he : x 1+x 2=(1+k)*x 1 := by rw [hc x hx]; ring
    rw [hk,zero_mul] at he
    exact False.elim (hn he)
  · apply four_term_weighted_projection_finite _ (fun _ hx => hx.1) 1 (1+k) 1
      one_ne_zero hk one_ne_zero 1 3 (fun u t => ![1,u,k*u,t])
    · intro x hx
      have hs := (four_term_relation_facts hx.1).2.1
      rw [hx.1.1,hc x hx] at hs
      simp only [one_mul]
      nlinarith only [hs]
    · intro x hx
      ext i
      fin_cases i
      · exact hx.1.1.symm
      · rfl
      · exact (hc x hx).symm
      · rfl

theorem four_term_coefficient_fiber_finite (a0 a1 a2 : ℚ)
    (ha : a0≠0 ∨ a1≠0 ∨ a2≠0) : (fourTermCoefficientFiber a0 a1 a2).Finite := by
  by_cases h0 : a0=0
  · subst a0
    by_cases h1 : a1=0
    · subst a1
      have h2 : a2≠0 := by simpa using ha
      apply Set.finite_empty.subset
      intro x hx
      have hn := (four_term_relation_facts hx.1).2.2.2.2.2 2
      have he : a2*x 2=0 := by simpa using hx.2
      exact False.elim ((mul_ne_zero h2 hn) he)
    · by_cases h2 : a2=0
      · subst a2
        apply Set.finite_empty.subset
        intro x hx
        have hn := (four_term_relation_facts hx.1).2.2.2.2.2 1
        have he : a1*x 1=0 := by simpa using hx.2
        exact False.elim ((mul_ne_zero h1 hn) he)
      · exact four_term_fiber_ratio a1 a2 h2
  · by_cases h1 : a1=0
    · subst a1
      by_cases h2 : a2=0
      · subst a2
        apply Set.finite_empty.subset
        intro x hx
        have he : a0=0 := by simpa [hx.1.1] using hx.2
        exact False.elim (h0 he)
      · exact four_term_fiber_fixed_second a0 a2 h2
    · by_cases h2 : a2=0
      · subst a2
        exact four_term_fiber_fixed_first a0 a1 h1
      · exact four_term_fiber_all_nonzero a0 a1 a2 h0 h1 h2

end JSP000334
