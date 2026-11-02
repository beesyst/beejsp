import SubspaceBridge.AllPointProduct5
namespace JSP000334
open scoped BigOperators Matrix

theorem retained_integer_cast5 (k i : Fin 5) (z : Fin 5 → ℤ) :
    ((retainedIntegerMatrix5 k *ᵥ z) i : ℚ)=fiveRetainedForm k i (fun j => (z j : ℚ)) := by
  rw [retained_integer_matrix_apply5]
  split_ifs <;> simp_all [fiveRetainedForm]

theorem six_term_integer_product5 {x : Fin 6 → ℚ}
    (hx : x∈normalizedRelations fixedSUnitGroup 5) (z : Fin 5 → ℤ) (s : fixedSUnitGroup)
    (hscale : ∀ i : Fin 5,(z i : ℚ)=((s : ℚˣ) : ℚ)*x i.castSucc) :
    (∀ i,threePlaceProduct (z i : ℚ)=1) ∧ threePlaceProduct (∑ i : Fin 5,(z i : ℚ))=1 := by
  have hu (i : Fin 6) : threePlaceProduct (x i)=1 := by
    obtain ⟨u,hu⟩ := hx.2.1 i
    rw [← hu]
    exact fixed_sunit_product_formula u
  have hz (i : Fin 5) : threePlaceProduct (z i : ℚ)=1 := by
    rw [hscale,threePlaceProduct_mul,fixed_sunit_product_formula,hu]
    norm_num
  refine ⟨hz,?_⟩
  have hs : (∑ i : Fin 5,(z i : ℚ))= -(((s : ℚˣ) : ℚ)*x 5) := by
    simp_rw [hscale]
    rw [← Finset.mul_sum]
    have hh : (∑ i : Fin 5,x i.castSucc)= -x 5 := by
      have h := hx.2.2.1
      rw [Fin.sum_univ_castSucc] at h
      exact eq_neg_of_add_eq_zero_left h
    rw [hh,mul_neg]
  rw [hs]
  have hn (q : ℚ) : threePlaceProduct (-q)=threePlaceProduct q := by simp [threePlaceProduct]
  rw [hn,threePlaceProduct_mul,fixed_sunit_product_formula,hu]
  norm_num

theorem allpoint_primitive_product5 {x : Fin 6 → ℚ}
    (hx : x∈normalizedRelations fixedSUnitGroup 5) (z : Fin 5 → ℤ) (s : fixedSUnitGroup)
    (hz : PrimitiveFive z) (hscale : ∀ i : Fin 5,(z i : ℚ)=((s : ℚˣ) : ℚ)*x i.castSucc) :
    ∃ choice : Fin 3 → Fin 5,fiveRetainedProduct choice (fun i => (z i : ℚ))*archFiveHeight z=1 := by
  choose choice hc using fun tau => exists_five_maximal_coordinate tau (fun i => (z i : ℚ))
  refine ⟨choice,?_⟩
  have h := five_retained_product_height choice (fun i => (z i : ℚ)) hc
  rw [primitive_five_height z hz] at h
  have hp := six_term_integer_product5 hx z s hscale
  simpa [hp.1,hp.2] using h

theorem allpoint_form_product5 {x : Fin 6 → ℚ}
    (hx : x∈normalizedRelations fixedSUnitGroup 5) (z : Fin 5 → ℤ) (s : fixedSUnitGroup)
    (hscale : ∀ i : Fin 5,(z i : ℚ)=((s : ℚˣ) : ℚ)*x i.castSucc) (k i : Fin 5) :
    threePlaceProduct (fiveRetainedForm k i (fun j => (z j : ℚ)))=1 := by
  have hp := six_term_integer_product5 hx z s hscale
  by_cases hi : i=k
  · simpa only [fiveRetainedForm,if_pos hi] using hp.2
  · simpa only [fiveRetainedForm,if_neg hi] using hp.1 i

theorem allpoint_form_arch_bound5 (z : Fin 5 → ℤ) (k i : Fin 5) :
    |fiveRetainedForm k i (fun j => (z j : ℚ))|≤5*archFiveHeight z := by
  have hc (j : Fin 5) : |(z j : ℚ)|≤archFiveHeight z := five_local_coordinate_le 0 (fun i => (z i : ℚ)) j
  have hH : 0≤archFiveHeight z := (abs_nonneg (z 0 : ℚ)).trans (hc 0)
  unfold fiveRetainedForm
  split_ifs
  · calc
      |∑ j : Fin 5,(z j : ℚ)|≤∑ j : Fin 5,|(z j : ℚ)| := Finset.abs_sum_le_sum_abs _ _
      _≤∑ _j : Fin 5,archFiveHeight z := Finset.sum_le_sum (fun j _ => hc j)
      _=5*archFiveHeight z := by simp [mul_comm]
  · exact (hc i).trans (by linarith)

end JSP000334
