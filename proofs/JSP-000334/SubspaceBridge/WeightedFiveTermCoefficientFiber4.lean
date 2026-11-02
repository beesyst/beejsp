import SubspaceBridge.WeightedFiveTermFourFibers4
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_five_coefficient_finite4 (A : ℚ) (B b : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (hb : ∃ i,b i≠0) :
    (weightedFiveCoefficientFiber4 A B b).Finite := by
  by_cases h0 : b 0=0
  ·
    by_cases h1 : b 1=0
    ·
      by_cases h2 : b 2=0
      ·
        by_cases h3 : b 3=0
        ·
          obtain ⟨i,hi⟩ := hb
          fin_cases i <;> contradiction
        ·
          apply Set.finite_empty.subset
          intro u hu
          have he : b 3*((u 3 : ℚˣ) : ℚ)=0 := by simpa only [Fin.sum_univ_four,h0,h1,h2,zero_mul,zero_add,add_zero] using hu.2
          exact False.elim ((mul_ne_zero h3 (Units.ne_zero _)) he)
      ·
        by_cases h3 : b 3=0
        ·
          apply Set.finite_empty.subset
          intro u hu
          have he : b 2*((u 2 : ℚˣ) : ℚ)=0 := by simpa only [Fin.sum_univ_four,h0,h1,h3,zero_mul,zero_add,add_zero] using hu.2
          exact False.elim ((mul_ne_zero h2 (Units.ne_zero _)) he)
        ·
          apply (weighted_five_pair_23_finite4 A B hA hB (-b 2/b 3)).subset
          intro u hu
          refine ⟨hu.1,?_⟩
          rw [div_mul_eq_mul_div]
          apply (eq_div_iff h3).mpr
          have he : b 2*((u 2 : ℚˣ) : ℚ)+b 3*((u 3 : ℚˣ) : ℚ)=0 := by
            simpa only [Fin.sum_univ_four,h0,h1,zero_mul,zero_add,add_zero] using hu.2
          nlinarith only [he]
    ·
      by_cases h2 : b 2=0
      ·
        by_cases h3 : b 3=0
        ·
          apply Set.finite_empty.subset
          intro u hu
          have he : b 1*((u 1 : ℚˣ) : ℚ)=0 := by simpa only [Fin.sum_univ_four,h0,h2,h3,zero_mul,zero_add,add_zero] using hu.2
          exact False.elim ((mul_ne_zero h1 (Units.ne_zero _)) he)
        ·
          apply (weighted_five_pair_13_finite4 A B hA hB (-b 1/b 3)).subset
          intro u hu
          refine ⟨hu.1,?_⟩
          rw [div_mul_eq_mul_div]
          apply (eq_div_iff h3).mpr
          have he : b 1*((u 1 : ℚˣ) : ℚ)+b 3*((u 3 : ℚˣ) : ℚ)=0 := by
            simpa only [Fin.sum_univ_four,h0,h2,zero_mul,zero_add,add_zero] using hu.2
          nlinarith only [he]
      ·
        by_cases h3 : b 3=0
        ·
          apply (weighted_five_pair_12_finite4 A B hA hB (-b 1/b 2)).subset
          intro u hu
          refine ⟨hu.1,?_⟩
          rw [div_mul_eq_mul_div]
          apply (eq_div_iff h2).mpr
          have he : b 1*((u 1 : ℚˣ) : ℚ)+b 2*((u 2 : ℚˣ) : ℚ)=0 := by
            simpa only [Fin.sum_univ_four,h0,h3,zero_mul,zero_add,add_zero] using hu.2
          nlinarith only [he]
        ·
          apply (weighted_five_three_123_finite4 A B hA hB (b 1) (b 2) (b 3) h1 h2 h3).subset
          intro u hu
          exact ⟨hu.1,by simpa only [Fin.sum_univ_four,h0,zero_mul,zero_add,add_zero] using hu.2⟩
  ·
    by_cases h1 : b 1=0
    ·
      by_cases h2 : b 2=0
      ·
        by_cases h3 : b 3=0
        ·
          apply Set.finite_empty.subset
          intro u hu
          have he : b 0*((u 0 : ℚˣ) : ℚ)=0 := by simpa only [Fin.sum_univ_four,h1,h2,h3,zero_mul,zero_add,add_zero] using hu.2
          exact False.elim ((mul_ne_zero h0 (Units.ne_zero _)) he)
        ·
          apply (weighted_five_pair_03_finite4 A B hA hB (-b 0/b 3)).subset
          intro u hu
          refine ⟨hu.1,?_⟩
          rw [div_mul_eq_mul_div]
          apply (eq_div_iff h3).mpr
          have he : b 0*((u 0 : ℚˣ) : ℚ)+b 3*((u 3 : ℚˣ) : ℚ)=0 := by
            simpa only [Fin.sum_univ_four,h1,h2,zero_mul,zero_add,add_zero] using hu.2
          nlinarith only [he]
      ·
        by_cases h3 : b 3=0
        ·
          apply (weighted_five_pair_02_finite4 A B hA hB (-b 0/b 2)).subset
          intro u hu
          refine ⟨hu.1,?_⟩
          rw [div_mul_eq_mul_div]
          apply (eq_div_iff h2).mpr
          have he : b 0*((u 0 : ℚˣ) : ℚ)+b 2*((u 2 : ℚˣ) : ℚ)=0 := by
            simpa only [Fin.sum_univ_four,h1,h3,zero_mul,zero_add,add_zero] using hu.2
          nlinarith only [he]
        ·
          apply (weighted_five_three_023_finite4 A B hA hB (b 0) (b 2) (b 3) h0 h2 h3).subset
          intro u hu
          exact ⟨hu.1,by simpa only [Fin.sum_univ_four,h1,zero_mul,zero_add,add_zero] using hu.2⟩
    ·
      by_cases h2 : b 2=0
      ·
        by_cases h3 : b 3=0
        ·
          apply (weighted_five_pair_01_finite4 A B hA hB (-b 0/b 1)).subset
          intro u hu
          refine ⟨hu.1,?_⟩
          rw [div_mul_eq_mul_div]
          apply (eq_div_iff h1).mpr
          have he : b 0*((u 0 : ℚˣ) : ℚ)+b 1*((u 1 : ℚˣ) : ℚ)=0 := by
            simpa only [Fin.sum_univ_four,h2,h3,zero_mul,zero_add,add_zero] using hu.2
          nlinarith only [he]
        ·
          apply (weighted_five_three_013_finite4 A B hA hB (b 0) (b 1) (b 3) h0 h1 h3).subset
          intro u hu
          exact ⟨hu.1,by simpa only [Fin.sum_univ_four,h2,zero_mul,zero_add,add_zero] using hu.2⟩
      ·
        by_cases h3 : b 3=0
        ·
          apply (weighted_five_three_012_finite4 A B hA hB (b 0) (b 1) (b 2) h0 h1 h2).subset
          intro u hu
          exact ⟨hu.1,by simpa only [Fin.sum_univ_four,h3,zero_mul,zero_add,add_zero] using hu.2⟩
        ·
          apply weighted_five_four_finite4 A B b hA hB
          intro i
          fin_cases i <;> assumption

end JSP000334
