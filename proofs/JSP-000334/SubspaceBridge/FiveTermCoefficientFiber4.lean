import SubspaceBridge.FiveTermThreeFibers4
import SubspaceBridge.FiveTermFourFibers4
namespace JSP000334
open scoped BigOperators Matrix

theorem five_term_coefficient_fiber_finite4 (b0 b1 b2 b3 : ℚ)
    (hb : b0≠0 ∨ b1≠0 ∨ b2≠0 ∨ b3≠0) :
    (fiveTermCoefficientFiber4 b0 b1 b2 b3).Finite := by
  by_cases h0 : b0=0
  · subst b0
    by_cases h1 : b1=0
    · subst b1
      by_cases h2 : b2=0
      · subst b2
        by_cases h3 : b3=0
        · subst b3
          simp only [ne_eq,not_true_eq_false,false_or] at hb
        ·
          apply Set.finite_empty.subset
          intro x hx
          have he : b3*x 3=0 := by simpa using hx.2
          have hn := (five_term_relation_facts4 hx.1).2.2.1 3
          exact False.elim ((mul_ne_zero h3 hn) he)
      ·
        by_cases h3 : b3=0
        · subst b3
          apply Set.finite_empty.subset
          intro x hx
          have he : b2*x 2=0 := by simpa using hx.2
          have hn := (five_term_relation_facts4 hx.1).2.2.1 2
          exact False.elim ((mul_ne_zero h2 hn) he)
        ·
          apply (five_term_ratio_coordinate_234 (-b2/b3)).subset
          intro x hx
          refine ⟨hx.1,?_⟩
          change x 3=(-b2/b3)*x 2
          rw [div_mul_eq_mul_div]
          apply (eq_div_iff h3).mpr
          have he := hx.2
          nlinarith only [he]
    ·
      by_cases h2 : b2=0
      · subst b2
        by_cases h3 : b3=0
        · subst b3
          apply Set.finite_empty.subset
          intro x hx
          have he : b1*x 1=0 := by simpa using hx.2
          have hn := (five_term_relation_facts4 hx.1).2.2.1 1
          exact False.elim ((mul_ne_zero h1 hn) he)
        ·
          apply (five_term_ratio_coordinate_134 (-b1/b3)).subset
          intro x hx
          refine ⟨hx.1,?_⟩
          change x 3=(-b1/b3)*x 1
          rw [div_mul_eq_mul_div]
          apply (eq_div_iff h3).mpr
          have he := hx.2
          nlinarith only [he]
      ·
        by_cases h3 : b3=0
        · subst b3
          apply (five_term_ratio_coordinate_124 (-b1/b2)).subset
          intro x hx
          refine ⟨hx.1,?_⟩
          change x 2=(-b1/b2)*x 1
          rw [div_mul_eq_mul_div]
          apply (eq_div_iff h2).mpr
          have he := hx.2
          nlinarith only [he]
        ·
          exact five_term_fiber_three_ratios4 b1 b2 b3 h1 h2 h3
  ·
    by_cases h1 : b1=0
    · subst b1
      by_cases h2 : b2=0
      · subst b2
        by_cases h3 : b3=0
        · subst b3
          apply Set.finite_empty.subset
          intro x hx
          have he : b0=0 := by simpa [hx.1.1] using hx.2
          exact False.elim (h0 he)
        ·
          apply (five_term_fixed_coordinate_34 (-b0/b3)).subset
          intro x hx
          refine ⟨hx.1,?_⟩
          apply (eq_div_iff h3).mpr
          have he := hx.2
          rw [hx.1.1] at he
          nlinarith only [he]
      ·
        by_cases h3 : b3=0
        · subst b3
          apply (five_term_fixed_coordinate_24 (-b0/b2)).subset
          intro x hx
          refine ⟨hx.1,?_⟩
          apply (eq_div_iff h2).mpr
          have he := hx.2
          rw [hx.1.1] at he
          nlinarith only [he]
        ·
          exact five_term_fiber_three_constant_234 b0 b2 b3 h0 h2 h3
    ·
      by_cases h2 : b2=0
      · subst b2
        by_cases h3 : b3=0
        · subst b3
          apply (five_term_fixed_coordinate_14 (-b0/b1)).subset
          intro x hx
          refine ⟨hx.1,?_⟩
          apply (eq_div_iff h1).mpr
          have he := hx.2
          rw [hx.1.1] at he
          nlinarith only [he]
        ·
          exact five_term_fiber_three_constant_134 b0 b1 b3 h0 h1 h3
      ·
        by_cases h3 : b3=0
        · subst b3
          exact five_term_fiber_three_constant_124 b0 b1 b2 h0 h1 h2
        ·
          exact five_term_fiber_four_nonzero4 b0 b1 b2 b3 h0 h1 h2 h3

end JSP000334
