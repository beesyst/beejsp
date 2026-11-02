import SubspaceBridge.FiveTermUnits4
namespace JSP000334
open scoped BigOperators Matrix

theorem five_term_fixed_pair_124 (a b : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 4 | x 1=a ∧ x 2=b}.Finite := by
  by_cases hab : 1+a+b=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,1,2} : Finset (Fin 5)) (by decide) (by decide)
    have he : x 0+x 1+x 2=0 := by rw [hx.1.1,hx.2.1,hx.2.2];exact hab
    exact False.elim (hn (by simpa [add_assoc] using he))
  · apply five_term_weighted_pair_projection4 _ (fun _ hx => hx.1) (1+a+b) 1 1 hab
      one_ne_zero one_ne_zero 3 4 (fun u v => ![1,a,b,u,v])
    · intro x hx
      have hs := (five_term_relation_facts4 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2] at hs
      simp only [one_mul]
      linarith only [hs]
    · intro x hx
      ext n
      fin_cases n
      · exact hx.1.1.symm
      · exact hx.2.1.symm
      · exact hx.2.2.symm
      · rfl
      · rfl

theorem five_term_fiber_three_constant_124 (b0 b c : ℚ)
    (h0 : b0≠0) (hb : b≠0) (hc : c≠0) : (fiveTermCoefficientFiber4 b0 b c 0).Finite := by
  let S := fiveTermCoefficientFiber4 b0 b c 0
  have hS : S⊆normalizedRelations fixedSUnitGroup 4 := fun _ hx => hx.1
  apply five_term_finite_over_pairs4 S (fun x => (fiveTermUnit4 x 1,fiveTermUnit4 x 2)) b0 b c h0 hb hc
  · intro x hx
    rw [five_term_unit_value4 hx.1 1,five_term_unit_value4 hx.1 2]
    have he := hx.2
    rw [hx.1.1] at he
    simpa using he
  · intro p hp
    apply (five_term_fixed_pair_124 ((p.1 : ℚˣ) : ℚ) ((p.2 : ℚˣ) : ℚ)).subset
    intro x hx
    exact ⟨hx.1.1,five_term_pair_fiber_values4 S hS 1 2 p x hx⟩

theorem five_term_fixed_pair_134 (a b : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 4 | x 1=a ∧ x 3=b}.Finite := by
  by_cases hab : 1+a+b=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,1,3} : Finset (Fin 5)) (by decide) (by decide)
    have he : x 0+x 1+x 3=0 := by rw [hx.1.1,hx.2.1,hx.2.2];exact hab
    exact False.elim (hn (by simpa [add_assoc] using he))
  · apply five_term_weighted_pair_projection4 _ (fun _ hx => hx.1) (1+a+b) 1 1 hab
      one_ne_zero one_ne_zero 2 4 (fun u v => ![1,a,u,b,v])
    · intro x hx
      have hs := (five_term_relation_facts4 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2] at hs
      simp only [one_mul]
      linarith only [hs]
    · intro x hx
      ext n
      fin_cases n
      · exact hx.1.1.symm
      · exact hx.2.1.symm
      · rfl
      · exact hx.2.2.symm
      · rfl

theorem five_term_fiber_three_constant_134 (b0 b c : ℚ)
    (h0 : b0≠0) (hb : b≠0) (hc : c≠0) : (fiveTermCoefficientFiber4 b0 b 0 c).Finite := by
  let S := fiveTermCoefficientFiber4 b0 b 0 c
  have hS : S⊆normalizedRelations fixedSUnitGroup 4 := fun _ hx => hx.1
  apply five_term_finite_over_pairs4 S (fun x => (fiveTermUnit4 x 1,fiveTermUnit4 x 3)) b0 b c h0 hb hc
  · intro x hx
    rw [five_term_unit_value4 hx.1 1,five_term_unit_value4 hx.1 3]
    have he := hx.2
    rw [hx.1.1] at he
    simpa using he
  · intro p hp
    apply (five_term_fixed_pair_134 ((p.1 : ℚˣ) : ℚ) ((p.2 : ℚˣ) : ℚ)).subset
    intro x hx
    exact ⟨hx.1.1,five_term_pair_fiber_values4 S hS 1 3 p x hx⟩

theorem five_term_fixed_pair_234 (a b : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 4 | x 2=a ∧ x 3=b}.Finite := by
  by_cases hab : 1+a+b=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,2,3} : Finset (Fin 5)) (by decide) (by decide)
    have he : x 0+x 2+x 3=0 := by rw [hx.1.1,hx.2.1,hx.2.2];exact hab
    exact False.elim (hn (by simpa [add_assoc] using he))
  · apply five_term_weighted_pair_projection4 _ (fun _ hx => hx.1) (1+a+b) 1 1 hab
      one_ne_zero one_ne_zero 1 4 (fun u v => ![1,u,a,b,v])
    · intro x hx
      have hs := (five_term_relation_facts4 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2] at hs
      simp only [one_mul]
      linarith only [hs]
    · intro x hx
      ext n
      fin_cases n
      · exact hx.1.1.symm
      · rfl
      · exact hx.2.1.symm
      · exact hx.2.2.symm
      · rfl

theorem five_term_fiber_three_constant_234 (b0 b c : ℚ)
    (h0 : b0≠0) (hb : b≠0) (hc : c≠0) : (fiveTermCoefficientFiber4 b0 0 b c).Finite := by
  let S := fiveTermCoefficientFiber4 b0 0 b c
  have hS : S⊆normalizedRelations fixedSUnitGroup 4 := fun _ hx => hx.1
  apply five_term_finite_over_pairs4 S (fun x => (fiveTermUnit4 x 2,fiveTermUnit4 x 3)) b0 b c h0 hb hc
  · intro x hx
    rw [five_term_unit_value4 hx.1 2,five_term_unit_value4 hx.1 3]
    have he := hx.2
    rw [hx.1.1] at he
    simpa using he
  · intro p hp
    apply (five_term_fixed_pair_234 ((p.1 : ℚˣ) : ℚ) ((p.2 : ℚˣ) : ℚ)).subset
    intro x hx
    exact ⟨hx.1.1,five_term_pair_fiber_values4 S hS 2 3 p x hx⟩

theorem five_term_fixed_ratios4 (r s : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 4 | x 2=r*x 1 ∧ x 3=s*x 1}.Finite := by
  by_cases hrs : 1+r+s=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({1,2,3} : Finset (Fin 5)) (by decide) (by decide)
    have he : x 1+x 2+x 3=(1+r+s)*x 1 := by rw [hx.2.1,hx.2.2];ring
    rw [hrs,zero_mul] at he
    exact False.elim (hn (by simpa [add_assoc] using he))
  · apply five_term_weighted_pair_projection4 _ (fun _ hx => hx.1) 1 (1+r+s) 1
      one_ne_zero hrs one_ne_zero 1 4 (fun u v => ![1,u,r*u,s*u,v])
    · intro x hx
      have hs := (five_term_relation_facts4 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2] at hs
      simp only [one_mul]
      nlinarith only [hs]
    · intro x hx
      ext i
      fin_cases i
      · exact hx.1.1.symm
      · rfl
      · exact hx.2.1.symm
      · exact hx.2.2.symm
      · rfl

theorem five_term_fiber_three_ratios4 (b1 b2 b3 : ℚ)
    (h1 : b1≠0) (h2 : b2≠0) (h3 : b3≠0) :
    (fiveTermCoefficientFiber4 0 b1 b2 b3).Finite := by
  let S := fiveTermCoefficientFiber4 0 b1 b2 b3
  let f (x : Fin 5 → ℚ) := (fiveTermUnit4 x 2/fiveTermUnit4 x 1,fiveTermUnit4 x 3/fiveTermUnit4 x 1)
  apply five_term_finite_over_pairs4 S f b1 b2 b3 h1 h2 h3
  · intro x hx
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,five_term_unit_value4 hx.1]
    have hn := (five_term_relation_facts4 hx.1).2.2.1 1
    field_simp
    have he := hx.2
    nlinarith only [he]
  · intro p hp
    apply (five_term_fixed_ratios4 ((p.1 : ℚˣ) : ℚ) ((p.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he1 := congrArg (fun q : fixedSUnitGroup × fixedSUnitGroup => ((q.1 : ℚˣ) : ℚ)) hx.2
    have he2 := congrArg (fun q : fixedSUnitGroup × fixedSUnitGroup => ((q.2 : ℚˣ) : ℚ)) hx.2
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,five_term_unit_value4 hx.1.1] at he1 he2
    have hn := (five_term_relation_facts4 hx.1.1).2.2.1 1
    refine ⟨hx.1.1,?_,?_⟩
    · rw [← he1]
      exact (div_mul_cancel₀ _ hn).symm
    · rw [← he2]
      exact (div_mul_cancel₀ _ hn).symm

end JSP000334
