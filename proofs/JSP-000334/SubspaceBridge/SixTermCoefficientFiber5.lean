import SubspaceBridge.SixTermLargeCoefficientFibers5
namespace JSP000334
open scoped BigOperators Matrix

theorem six_term_coefficient_fiber_finite5 (b : Fin 5 → ℚ) (hb : ∃ i,b i≠0) :
    (sixTermCoefficientFiber5 b).Finite := by
  by_cases h0 : b 0=0
  ·
    by_cases h1 : b 1=0
    ·
      by_cases h2 : b 2=0
      ·
        by_cases h3 : b 3=0
        ·
          by_cases h4 : b 4=0
          ·
            obtain ⟨i,hi⟩ := hb
            fin_cases i <;> contradiction
          ·
            apply Set.finite_empty.subset
            intro x hx
            have he : b 4*x 4=0 := by simpa [Fin.sum_univ_succ,h0,h1,h2,h3,hx.1.1,add_assoc] using hx.2
            exact False.elim ((mul_ne_zero h4 ((six_term_relation_facts5 hx.1).2.2 4)) he)
        ·
          by_cases h4 : b 4=0
          ·
            apply Set.finite_empty.subset
            intro x hx
            have he : b 3*x 3=0 := by simpa [Fin.sum_univ_succ,h0,h1,h2,h4,hx.1.1,add_assoc] using hx.2
            exact False.elim ((mul_ne_zero h3 ((six_term_relation_facts5 hx.1).2.2 3)) he)
          ·
            apply (six_term_ratios_34_finite5 (-b 3/b 4)).subset
            intro x hx
            refine ⟨hx.1,?_⟩
            rw [div_mul_eq_mul_div]
            apply (eq_div_iff h4).mpr
            have he : b 3*x 3+b 4*x 4=0 := by simpa [Fin.sum_univ_succ,h0,h1,h2,hx.1.1,add_assoc] using hx.2
            nlinarith only [he]
      ·
        by_cases h3 : b 3=0
        ·
          by_cases h4 : b 4=0
          ·
            apply Set.finite_empty.subset
            intro x hx
            have he : b 2*x 2=0 := by simpa [Fin.sum_univ_succ,h0,h1,h3,h4,hx.1.1,add_assoc] using hx.2
            exact False.elim ((mul_ne_zero h2 ((six_term_relation_facts5 hx.1).2.2 2)) he)
          ·
            apply (six_term_ratios_24_finite5 (-b 2/b 4)).subset
            intro x hx
            refine ⟨hx.1,?_⟩
            rw [div_mul_eq_mul_div]
            apply (eq_div_iff h4).mpr
            have he : b 2*x 2+b 4*x 4=0 := by simpa [Fin.sum_univ_succ,h0,h1,h3,hx.1.1,add_assoc] using hx.2
            nlinarith only [he]
        ·
          by_cases h4 : b 4=0
          ·
            apply (six_term_ratios_23_finite5 (-b 2/b 3)).subset
            intro x hx
            refine ⟨hx.1,?_⟩
            rw [div_mul_eq_mul_div]
            apply (eq_div_iff h3).mpr
            have he : b 2*x 2+b 3*x 3=0 := by simpa [Fin.sum_univ_succ,h0,h1,h4,hx.1.1,add_assoc] using hx.2
            nlinarith only [he]
          ·
            apply (six_term_homogeneous_234_finite5 (b 2) (b 3) (b 4) h2 h3 h4).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h0,h1,hx.1.1,add_assoc] using hx.2⟩
    ·
      by_cases h2 : b 2=0
      ·
        by_cases h3 : b 3=0
        ·
          by_cases h4 : b 4=0
          ·
            apply Set.finite_empty.subset
            intro x hx
            have he : b 1*x 1=0 := by simpa [Fin.sum_univ_succ,h0,h2,h3,h4,hx.1.1,add_assoc] using hx.2
            exact False.elim ((mul_ne_zero h1 ((six_term_relation_facts5 hx.1).2.2 1)) he)
          ·
            apply (six_term_ratios_14_finite5 (-b 1/b 4)).subset
            intro x hx
            refine ⟨hx.1,?_⟩
            rw [div_mul_eq_mul_div]
            apply (eq_div_iff h4).mpr
            have he : b 1*x 1+b 4*x 4=0 := by simpa [Fin.sum_univ_succ,h0,h2,h3,hx.1.1,add_assoc] using hx.2
            nlinarith only [he]
        ·
          by_cases h4 : b 4=0
          ·
            apply (six_term_ratios_13_finite5 (-b 1/b 3)).subset
            intro x hx
            refine ⟨hx.1,?_⟩
            rw [div_mul_eq_mul_div]
            apply (eq_div_iff h3).mpr
            have he : b 1*x 1+b 3*x 3=0 := by simpa [Fin.sum_univ_succ,h0,h2,h4,hx.1.1,add_assoc] using hx.2
            nlinarith only [he]
          ·
            apply (six_term_homogeneous_134_finite5 (b 1) (b 3) (b 4) h1 h3 h4).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h0,h2,hx.1.1,add_assoc] using hx.2⟩
      ·
        by_cases h3 : b 3=0
        ·
          by_cases h4 : b 4=0
          ·
            apply (six_term_ratios_12_finite5 (-b 1/b 2)).subset
            intro x hx
            refine ⟨hx.1,?_⟩
            rw [div_mul_eq_mul_div]
            apply (eq_div_iff h2).mpr
            have he : b 1*x 1+b 2*x 2=0 := by simpa [Fin.sum_univ_succ,h0,h3,h4,hx.1.1,add_assoc] using hx.2
            nlinarith only [he]
          ·
            apply (six_term_homogeneous_124_finite5 (b 1) (b 2) (b 4) h1 h2 h4).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h0,h3,hx.1.1,add_assoc] using hx.2⟩
        ·
          by_cases h4 : b 4=0
          ·
            apply (six_term_homogeneous_123_finite5 (b 1) (b 2) (b 3) h1 h2 h3).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h0,h4,hx.1.1,add_assoc] using hx.2⟩
          ·
            apply (six_term_homogeneous_four_finite5 (b 1) (b 2) (b 3) (b 4) h1 h2 h3 h4).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h0,hx.1.1,add_assoc] using hx.2⟩
  ·
    by_cases h1 : b 1=0
    ·
      by_cases h2 : b 2=0
      ·
        by_cases h3 : b 3=0
        ·
          by_cases h4 : b 4=0
          ·
            apply Set.finite_empty.subset
            intro x hx
            have he : b 0*x 0=0 := by simpa [Fin.sum_univ_succ,h1,h2,h3,h4,hx.1.1,add_assoc] using hx.2
            exact False.elim ((mul_ne_zero h0 ((six_term_relation_facts5 hx.1).2.2 0)) he)
          ·
            apply (six_term_fixed_4_finite5 (-b 0/b 4)).subset
            intro x hx
            refine ⟨hx.1,(eq_div_iff h4).mpr ?_⟩
            have he : b 0+b 4*x 4=0 := by simpa [Fin.sum_univ_succ,h1,h2,h3,hx.1.1,add_assoc] using hx.2
            nlinarith only [he]
        ·
          by_cases h4 : b 4=0
          ·
            apply (six_term_fixed_3_finite5 (-b 0/b 3)).subset
            intro x hx
            refine ⟨hx.1,(eq_div_iff h3).mpr ?_⟩
            have he : b 0+b 3*x 3=0 := by simpa [Fin.sum_univ_succ,h1,h2,h4,hx.1.1,add_assoc] using hx.2
            nlinarith only [he]
          ·
            apply (six_term_constant_34_good5 (b 0) (b 3) (b 4) h0 h3 h4).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h1,h2,hx.1.1,add_assoc] using hx.2⟩
      ·
        by_cases h3 : b 3=0
        ·
          by_cases h4 : b 4=0
          ·
            apply (six_term_fixed_2_finite5 (-b 0/b 2)).subset
            intro x hx
            refine ⟨hx.1,(eq_div_iff h2).mpr ?_⟩
            have he : b 0+b 2*x 2=0 := by simpa [Fin.sum_univ_succ,h1,h3,h4,hx.1.1,add_assoc] using hx.2
            nlinarith only [he]
          ·
            apply (six_term_constant_24_good5 (b 0) (b 2) (b 4) h0 h2 h4).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h1,h3,hx.1.1,add_assoc] using hx.2⟩
        ·
          by_cases h4 : b 4=0
          ·
            apply (six_term_constant_23_good5 (b 0) (b 2) (b 3) h0 h2 h3).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h1,h4,hx.1.1,add_assoc] using hx.2⟩
          ·
            apply (six_term_constant_234_finite5 (b 0) (b 2) (b 3) (b 4) h0 h2 h3 h4).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h1,hx.1.1,add_assoc] using hx.2⟩
    ·
      by_cases h2 : b 2=0
      ·
        by_cases h3 : b 3=0
        ·
          by_cases h4 : b 4=0
          ·
            apply (six_term_fixed_1_finite5 (-b 0/b 1)).subset
            intro x hx
            refine ⟨hx.1,(eq_div_iff h1).mpr ?_⟩
            have he : b 0+b 1*x 1=0 := by simpa [Fin.sum_univ_succ,h2,h3,h4,hx.1.1,add_assoc] using hx.2
            nlinarith only [he]
          ·
            apply (six_term_constant_14_good5 (b 0) (b 1) (b 4) h0 h1 h4).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h2,h3,hx.1.1,add_assoc] using hx.2⟩
        ·
          by_cases h4 : b 4=0
          ·
            apply (six_term_constant_13_good5 (b 0) (b 1) (b 3) h0 h1 h3).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h2,h4,hx.1.1,add_assoc] using hx.2⟩
          ·
            apply (six_term_constant_134_finite5 (b 0) (b 1) (b 3) (b 4) h0 h1 h3 h4).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h2,hx.1.1,add_assoc] using hx.2⟩
      ·
        by_cases h3 : b 3=0
        ·
          by_cases h4 : b 4=0
          ·
            apply (six_term_constant_12_good5 (b 0) (b 1) (b 2) h0 h1 h2).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h3,h4,hx.1.1,add_assoc] using hx.2⟩
          ·
            apply (six_term_constant_124_finite5 (b 0) (b 1) (b 2) (b 4) h0 h1 h2 h4).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h3,hx.1.1,add_assoc] using hx.2⟩
        ·
          by_cases h4 : b 4=0
          ·
            apply (six_term_constant_123_finite5 (b 0) (b 1) (b 2) (b 3) h0 h1 h2 h3).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,h4,hx.1.1,add_assoc] using hx.2⟩
          ·
            apply (six_term_five_coefficients_finite5 b (by intro i;fin_cases i <;> assumption)).subset
            intro x hx
            exact ⟨hx.1,by simpa [Fin.sum_univ_succ,hx.1.1,add_assoc] using hx.2⟩

end JSP000334
