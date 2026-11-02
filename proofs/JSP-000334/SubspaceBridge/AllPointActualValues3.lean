import ElementaryThreeTerm
import SubspaceBridge.CofactorOriginalRankOne3
open scoped BigOperators Matrix
namespace JSP000334

theorem allpoint_form_product3 {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3)
    (z : IntegerTriple) (s : fixedSUnitGroup)
    (hscale : ∀ i : Fin 3, (z i : ℚ) = ((s : ℚˣ) : ℚ)*x i.castSucc)
    (k i : Fin 3) :
    threePlaceProduct (threeCoordinateSumForms k i (fun j => (z j : ℚ))) = 1 := by
  have hu (j : Fin 4) : threePlaceProduct (x j) = 1 := by
    obtain ⟨u,he⟩ := hx.2.1 j
    rw [← he]
    exact fixed_sunit_product_formula u
  have hz (j : Fin 3) : threePlaceProduct (z j : ℚ) = 1 := by
    rw [hscale,threePlaceProduct_mul,fixed_sunit_product_formula,hu]
    norm_num
  have hsumx : x 0+x 1+x 2+x 3 = 0 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hx.2.2.1
  have hs : (z 0 : ℚ)+z 1+z 2 = -(((s : ℚˣ) : ℚ)*x 3) := by
    have h0 := hscale 0
    have h1 := hscale 1
    have h2 := hscale 2
    change (z 0 : ℚ) = ((s : ℚˣ) : ℚ)*x 0 at h0
    change (z 1 : ℚ) = ((s : ℚˣ) : ℚ)*x 1 at h1
    change (z 2 : ℚ) = ((s : ℚˣ) : ℚ)*x 2 at h2
    have hh : ((s : ℚˣ) : ℚ)*(x 0+x 1+x 2+x 3) = 0 := by rw [hsumx,mul_zero]
    nlinarith
  have hsum : threePlaceProduct ((z 0 : ℚ)+z 1+z 2) = 1 := by
    rw [hs]
    have hneg (q : ℚ) : threePlaceProduct (-q) = threePlaceProduct q := by simp [threePlaceProduct]
    rw [hneg,threePlaceProduct_mul,fixed_sunit_product_formula,hu]
    norm_num
  fin_cases i
  · simpa [threeCoordinateSumForms] using hz (k.succAbove 0)
  · simpa [threeCoordinateSumForms] using hz (k.succAbove 1)
  · simpa [threeCoordinateSumForms] using hsum

theorem allpoint_form_arch_bound3 (z : IntegerTriple) (k i : Fin 3) :
    |threeCoordinateSumForms k i (fun j => (z j : ℚ))| ≤ 3*archTripleHeight z := by
  have hcoord (j : Fin 3) : |(z j : ℚ)| ≤ archTripleHeight z := by
    fin_cases j
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hH : 0 ≤ archTripleHeight z := (abs_nonneg (z 0 : ℚ)).trans (hcoord 0)
  fin_cases i
  · simpa [threeCoordinateSumForms] using (hcoord (k.succAbove 0)).trans (by linarith : archTripleHeight z ≤ 3*archTripleHeight z)
  · simpa [threeCoordinateSumForms] using (hcoord (k.succAbove 1)).trans (by linarith : archTripleHeight z ≤ 3*archTripleHeight z)
  · change |(z 0 : ℚ)+z 1+z 2| ≤ _
    have hb := (abs_add ((z 0 : ℚ)+z 1) (z 2 : ℚ)).trans
      (add_le_add_right (abs_add (z 0 : ℚ) (z 1 : ℚ)) |(z 2 : ℚ)|)
    linarith [hcoord 0,hcoord 1,hcoord 2]


theorem allpoint_local_inverse3 (m : ℤ) (hprod : threePlaceProduct (m : ℚ) = 1) (tau : Fin 3) :
    0 < rationalPlaceNorm tau (m : ℚ) ∧
    (rationalPlaceNorm tau (m : ℚ))⁻¹ ≤ |(m : ℚ)| ∧
    (tau ≠ 0 → rationalPlaceNorm tau (m : ℚ) ≤ 1) := by
  have hn : (m : ℚ) ≠ 0 := by
    intro h
    simp [h,threePlaceProduct] at hprod
  have hpos := rationalPlaceNorm_pos tau hn
  have h2 := padicNorm.of_int (p := 2) m
  have h3 := padicNorm.of_int (p := 3) m
  have hp2 : 0 < padicNorm 2 (m : ℚ) := by simpa [rationalPlaceNorm] using rationalPlaceNorm_pos 1 hn
  have hp3 : 0 < padicNorm 3 (m : ℚ) := by simpa [rationalPlaceNorm] using rationalPlaceNorm_pos 2 hn
  have ha : 0 < |(m : ℚ)| := abs_pos.mpr hn
  change |(m : ℚ)| *padicNorm 2 (m : ℚ)*padicNorm 3 (m : ℚ) = 1 at hprod
  have h23 : padicNorm 2 (m : ℚ)*padicNorm 3 (m : ℚ) ≤ 1 := by
    nlinarith [mul_le_mul h2 h3 hp3.le (by norm_num : (0 : ℚ) ≤ 1)]
  have hA : 1 ≤ |(m : ℚ)| := by
    nlinarith [mul_le_mul_of_nonneg_left h23 ha.le]
  have hb2 : 1 ≤ |(m : ℚ)| *padicNorm 2 (m : ℚ) := by
    nlinarith [mul_le_mul_of_nonneg_left h3 (mul_pos ha hp2).le]
  have hb3 : 1 ≤ |(m : ℚ)| *padicNorm 3 (m : ℚ) := by
    nlinarith [mul_le_mul_of_nonneg_left h2 (mul_pos ha hp3).le]
  refine ⟨hpos,?_,?_⟩
  · fin_cases tau
    · change |(m : ℚ)|⁻¹ ≤ |(m : ℚ)|
      apply (inv_le_iff_one_le_mul₀ ha).mpr
      nlinarith
    · change (padicNorm 2 (m : ℚ))⁻¹ ≤ |(m : ℚ)|
      exact (inv_le_iff_one_le_mul₀ hp2).mpr hb2
    · change (padicNorm 3 (m : ℚ))⁻¹ ≤ |(m : ℚ)|
      exact (inv_le_iff_one_le_mul₀ hp3).mpr hb3
  · intro ht
    fin_cases tau
    · exact (ht rfl).elim
    · exact h2
    · exact h3

end JSP000334
