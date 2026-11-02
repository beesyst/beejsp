import SubspaceBridge.SixTermFiniteness5
import SubspaceBridge.FourTermFiniteness3
namespace JSP000334

theorem fixed_sunit_finiteness_complete : FixedSUnitFiniteness := by
  intro m
  fin_cases m
  · exact normalized_two_term_finite fixedSUnitGroup
  · exact fixed_three_term_finite
  · exact fixed_four_term_finite
  · exact fixed_five_term_finite
  · exact fixed_six_term_finite

theorem newman_conjecture_complete : NewmanConjecture := by
  exact newman_of_fixed_sunit_finiteness fixed_sunit_finiteness_complete

end JSP000334
