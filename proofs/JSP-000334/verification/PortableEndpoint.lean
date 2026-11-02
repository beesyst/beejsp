import SubspaceBridge.NewmanCompletion
open JSP000334
example : (twoUnit : ℚ) = 2 := rfl
example : (threeUnit : ℚ) = 3 := rfl
example {m : ℕ} (x : Fin m → ℚ) :
    Nondegenerate x ↔ ∀ I : Finset (Fin m), I.Nonempty → I ≠ Finset.univ →
      ∑ i ∈ I, x i ≠ 0 := Iff.rfl
example (n : ℕ) :
    ({r : Exponents | 2 ^ r.a + 3 ^ r.b + 2 ^ r.c * 3 ^ r.d = n} : Set Exponents).Finite :=
  solutions_finite n
example (n : ℕ) :
    ({r : Exponents | 2 ^ r.a * 3 ^ r.b + 2 ^ r.c + 3 ^ r.d = n} : Set Exponents).ncard =
      ({r : Exponents | 2 ^ r.a + 3 ^ r.b + 2 ^ r.c * 3 ^ r.d = n} : Set Exponents).ncard :=
  source_parameterization_count n
example : ∃ C : ℕ, ∀ n : ℕ, 0 < n →
    ({r : Exponents | 2 ^ r.a + 3 ^ r.b + 2 ^ r.c * 3 ^ r.d = n} : Set Exponents).ncard ≤ C :=
  newman_conjecture_complete
example : ∀ m : Fin 5,
    (normalizedRelations (Subgroup.closure ({-1, twoUnit, threeUnit} : Set ℚˣ)) (m.val + 1)).Finite :=
  fixed_sunit_finiteness_complete
#check @source_parameterization_count
#check @solutions_finite
#check @counting_conventions_equivalent
#check @source_six_term_finite_cover5
#check @weighted_five_term_finite
#check @fixed_six_term_finite
#check @fixed_sunit_finiteness_complete
#check @newman_of_fixed_sunit_finiteness
#check @newman_conjecture_complete
#print JSP000334.Exponents
#print JSP000334.value
#print JSP000334.solutions
#print JSP000334.tupleCount
#print JSP000334.sourceValue
#print JSP000334.sourceEquiv
#print JSP000334.Nondegenerate
#print JSP000334.normalizedRelations
#print JSP000334.fixedSUnitGroup
#print JSP000334.twoUnit
#print JSP000334.threeUnit
#print JSP000334.FixedSUnitFiniteness
#print JSP000334.WeightedFiveTermSolutions
#print JSP000334.NewmanConjecture
#print axioms JSP000334.source_six_term_finite_cover5
#print axioms JSP000334.weighted_five_term_finite
#print axioms JSP000334.fixed_six_term_finite
#print axioms JSP000334.fixed_sunit_finiteness_complete
#print axioms JSP000334.newman_conjecture_complete
