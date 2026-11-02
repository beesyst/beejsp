import SubspaceBridge.SixTermSmallCoefficientFibers5
namespace JSP000334
open scoped BigOperators Matrix

theorem six_term_homogeneous_four_good5 (a b c d : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a*x 1+b*x 2+c*x 3+d*x 4=0 ∧
      Nondegenerate (![a*x 1,b*x 2,c*x 3,d*x 4] : Fin 4 → ℚ)}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a*x 1+b*x 2+c*x 3+d*x 4=0 ∧
      Nondegenerate (![a*x 1,b*x 2,c*x 3,d*x 4] : Fin 4 → ℚ)}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 2/sixTermUnit5 x 1,
    sixTermUnit5 x 3/sixTermUnit5 x 1,sixTermUnit5 x 4/sixTermUnit5 x 1)
  have hU : (⋃ q∈WeightedFourTermSolutions a b c d,{x∈S | f x=q}).Finite := by
    apply (weighted_four_term_finite a b c d ha hb hc hd).biUnion
    intro q hq
    apply (six_term_ratios_1234_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2.1 : ℚˣ) : ℚ) ((q.2.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he0 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup × fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1.1] at he0
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup × fixedSUnitGroup => ((p.2.1 : ℚˣ) : ℚ)) hx.2
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1.1] at he1
    have he2 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup × fixedSUnitGroup => ((p.2.2 : ℚˣ) : ℚ)) hx.2
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1.1] at he2
    have hn := (six_term_relation_facts5 hx.1.1).2.2 1
    refine ⟨hx.1.1,?_,?_,?_⟩
    · rw [← he0]
      exact (div_mul_cancel₀ _ hn).symm
    · rw [← he1]
      exact (div_mul_cancel₀ _ hn).symm
    · rw [← he2]
      exact (div_mul_cancel₀ _ hn).symm
  apply hU.subset
  intro x hx
  refine Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨?_,hx,rfl⟩⟩
  change a+b*(((sixTermUnit5 x 2/sixTermUnit5 x 1 : fixedSUnitGroup) : ℚˣ) : ℚ)+
    c*(((sixTermUnit5 x 3/sixTermUnit5 x 1 : fixedSUnitGroup) : ℚˣ) : ℚ)+
    d*(((sixTermUnit5 x 4/sixTermUnit5 x 1 : fixedSUnitGroup) : ℚˣ) : ℚ)=0 ∧ _
  simp only [Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
  have hn := (six_term_relation_facts5 hx.1).2.2 1
  constructor
  · field_simp
    nlinarith only [hx.2.1]
  · simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
    change Nondegenerate (![a,b*(x 2/x 1),c*(x 3/x 1),d*(x 4/x 1)] : Fin 4 → ℚ)
    have hh := weighted_nondegenerate_scale4 _ hx.2.2 (x 1)⁻¹ (inv_ne_zero hn)
    convert hh using 1
    ext i
    fin_cases i <;> simp [div_eq_mul_inv] <;> field_simp

theorem six_term_homogeneous_four_finite5 (a b c d : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a*x 1+b*x 2+c*x 3+d*x 4=0}.Finite := by
  have hg := six_term_homogeneous_four_good5 a b c d ha hb hc hd
  have hU := ((hg.union (six_term_ratios_12_finite5 (-a/b))).union
    (six_term_ratios_13_finite5 (-a/c))).union (six_term_ratios_14_finite5 (-a/d))
  apply hU.subset
  intro x hx
  by_cases hn : Nondegenerate (![a*x 1,b*x 2,c*x 3,d*x 4] : Fin 4 → ℚ)
  · exact Or.inl (Or.inl (Or.inl ⟨hx.1,hx.2,hn⟩))
  · have hxn := (six_term_relation_facts5 hx.1).2.2
    obtain hp|hp|hp := five_term_weighted_degenerate_pair4 _ _ _ _
      (mul_ne_zero ha (hxn 1)) (mul_ne_zero hb (hxn 2))
      (mul_ne_zero hc (hxn 3)) (mul_ne_zero hd (hxn 4)) hx.2 hn
    · refine Or.inl (Or.inl (Or.inr ?_))
      refine ⟨hx.1,?_⟩
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hb).mpr
      nlinarith only [hp]
    · refine Or.inl (Or.inr ?_)
      refine ⟨hx.1,?_⟩
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hc).mpr
      nlinarith only [hp]
    · refine Or.inr ?_
      refine ⟨hx.1,?_⟩
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hd).mpr
      nlinarith only [hp]

theorem six_term_five_good_finite5 (b : Fin 5 → ℚ) (hb : ∀ i,b i≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 |
      b 0+b 1*x 1+b 2*x 2+b 3*x 3+b 4*x 4=0 ∧
      Nondegenerate (![b 0,b 1*x 1,b 2*x 2,b 3*x 3,b 4*x 4] : Fin 5 → ℚ)}.Finite := by
  apply six_term_weighted_quad_projection5 _ (fun _ hx => hx.1) (b 0) (fun i => b i.succ) (hb 0)
    (fun i => hb i.succ) ![1,2,3,4]
    (fun u => ![1,u 0,u 1,u 2,u 3,-(1+u 0+u 1+u 2+u 3)])
  · intro x hx
    simpa [Fin.sum_univ_succ,add_assoc] using hx.2.1
  · intro x hx
    convert hx.2.2 using 1
    ext i
    fin_cases i <;> rfl
  · intro x hx
    ext i
    fin_cases i
    · exact hx.1.1.symm
    · rfl
    · rfl
    · rfl
    · rfl
    · have he := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1] at he
      dsimp
      linarith only [he]

theorem six_term_five_coefficients_finite5 (b : Fin 5 → ℚ) (hb : ∀ i,b i≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | b 0+b 1*x 1+b 2*x 2+b 3*x 3+b 4*x 4=0}.Finite := by
  have hg := six_term_five_good_finite5 b hb
  have hU := ((((((((((hg.union (six_term_fixed_1_finite5 (-b 0/b 1))).union (six_term_fixed_2_finite5 (-b 0/b 2))).union (six_term_fixed_3_finite5 (-b 0/b 3))).union (six_term_fixed_4_finite5 (-b 0/b 4))).union (six_term_constant_12_good5 (b 0) (b 1) (b 2) (hb 0) (hb 1) (hb 2))).union (six_term_constant_13_good5 (b 0) (b 1) (b 3) (hb 0) (hb 1) (hb 3))).union (six_term_constant_14_good5 (b 0) (b 1) (b 4) (hb 0) (hb 1) (hb 4))).union (six_term_constant_23_good5 (b 0) (b 2) (b 3) (hb 0) (hb 2) (hb 3))).union (six_term_constant_24_good5 (b 0) (b 2) (b 4) (hb 0) (hb 2) (hb 4))).union (six_term_constant_34_good5 (b 0) (b 3) (b 4) (hb 0) (hb 3) (hb 4)))
  apply hU.subset
  intro x hx
  by_cases hn : Nondegenerate (![b 0,b 1*x 1,b 2*x 2,b 3*x 3,b 4*x 4] : Fin 5 → ℚ)
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨hx.1,hx.2,hn⟩))))))))))
  · have hxn := (six_term_relation_facts5 hx.1).2.2
    have hne (i : Fin 5) : (![b 0,b 1*x 1,b 2*x 2,b 3*x 3,b 4*x 4] : Fin 5 → ℚ) i≠0 := by
      fin_cases i
      · exact hb 0
      · exact mul_ne_zero (hb 1) (hxn 1)
      · exact mul_ne_zero (hb 2) (hxn 2)
      · exact mul_ne_zero (hb 3) (hxn 3)
      · exact mul_ne_zero (hb 4) (hxn 4)
    have hs : ∑ i : Fin 5,(![b 0,b 1*x 1,b 2*x 2,b 3*x 3,b 4*x 4] : Fin 5 → ℚ) i=0 := by
      simpa [Fin.sum_univ_succ,add_assoc] using hx.2
    obtain hp|hp|hp|hp|hp|hp|hp|hp|hp|hp := six_term_annihilator_degenerate5 _ hne hs hn
    · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))))))
      change b 0+b 1*x 1=0 at hp
      exact ⟨hx.1,(eq_div_iff (hb 1)).mpr (by simpa using (show x 1*b 1 = -b 0 by nlinarith only [hp]))⟩
    · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))))))
      change b 0+b 2*x 2=0 at hp
      exact ⟨hx.1,(eq_div_iff (hb 2)).mpr (by simpa using (show x 2*b 2 = -b 0 by nlinarith only [hp]))⟩
    · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))))
      change b 0+b 3*x 3=0 at hp
      exact ⟨hx.1,(eq_div_iff (hb 3)).mpr (by simpa using (show x 3*b 3 = -b 0 by nlinarith only [hp]))⟩
    · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))))
      change b 0+b 4*x 4=0 at hp
      exact ⟨hx.1,(eq_div_iff (hb 4)).mpr (by simpa using (show x 4*b 4 = -b 0 by nlinarith only [hp]))⟩
    · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))
      exact ⟨hx.1,by simpa using hp⟩
    · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))
      exact ⟨hx.1,by simpa using hp⟩
    · refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
      exact ⟨hx.1,by simpa using hp⟩
    · refine Or.inl (Or.inl (Or.inr ?_))
      exact ⟨hx.1,by simpa using hp⟩
    · refine Or.inl (Or.inr ?_)
      exact ⟨hx.1,by simpa using hp⟩
    · refine Or.inr ?_
      exact ⟨hx.1,by simpa using hp⟩

end JSP000334
