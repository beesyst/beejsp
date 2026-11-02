import SubspaceBridge.FiveTermSmallFibers4
namespace JSP000334
open scoped BigOperators Matrix

theorem five_term_fiber_four_nonzero4 (b0 b1 b2 b3 : ℚ)
    (h0 : b0≠0) (h1 : b1≠0) (h2 : b2≠0) (h3 : b3≠0) :
    (fiveTermCoefficientFiber4 b0 b1 b2 b3).Finite := by
  let S := fiveTermCoefficientFiber4 b0 b1 b2 b3
  let good : Set (Fin 5 → ℚ) := {x∈S | Nondegenerate (![b0,b1*x 1,b2*x 2,b3*x 3] : Fin 4 → ℚ)}
  have hgood : good.Finite := by
    apply five_term_weighted_triple_projection4 _ (fun _ hx => hx.1.1) b0 b1 b2 b3 h0 h1 h2 h3 1 2 3
      (fun u v w => ![1,u,v,w,-(1+u+v+w)])
    · intro x hx
      have he := hx.1.2
      rw [hx.1.1.1] at he
      simpa using he
    · intro x hx
      exact hx.2
    · intro x hx
      ext i
      fin_cases i
      · exact hx.1.1.1.symm
      · rfl
      · rfl
      · rfl
      · have he := (five_term_relation_facts4 hx.1.1).2.2.2
        rw [hx.1.1.1] at he
        exact he.symm
  have hU := ((hgood.union (five_term_fixed_coordinate_14 (-b0/b1))).union
    (five_term_fixed_coordinate_24 (-b0/b2))).union (five_term_fixed_coordinate_34 (-b0/b3))
  apply hU.subset
  intro x hx
  by_cases hn : Nondegenerate (![b0,b1*x 1,b2*x 2,b3*x 3] : Fin 4 → ℚ)
  · exact Or.inl (Or.inl (Or.inl ⟨hx,hn⟩))
  · have he := hx.2
    rw [hx.1.1] at he
    have hxn := (five_term_relation_facts4 hx.1).2.2.1
    obtain hp|hp|hp := five_term_weighted_degenerate_pair4 b0 (b1*x 1) (b2*x 2) (b3*x 3)
      h0 (mul_ne_zero h1 (hxn 1)) (mul_ne_zero h2 (hxn 2)) (mul_ne_zero h3 (hxn 3)) (by simpa using he) hn
    · exact Or.inl (Or.inl (Or.inr ⟨hx.1,(eq_div_iff h1).mpr (by nlinarith only [hp])⟩))
    · exact Or.inl (Or.inr ⟨hx.1,(eq_div_iff h2).mpr (by nlinarith only [hp])⟩)
    · exact Or.inr ⟨hx.1,(eq_div_iff h3).mpr (by nlinarith only [hp])⟩

end JSP000334
