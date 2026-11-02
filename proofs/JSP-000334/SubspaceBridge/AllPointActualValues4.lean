import SubspaceBridge.AllPointProduct4
namespace JSP000334
open scoped BigOperators Matrix

theorem retained_integer_cast4 (k i : Fin 4) (z : Fin 4 → ℤ) :
    ((retainedIntegerMatrix4 k *ᵥ z) i : ℚ)=fourRetainedForm k i (fun j => (z j : ℚ)) := by
  rw [retained_integer_matrix_apply4]
  split_ifs <;> simp_all [fourRetainedForm]

theorem five_term_integer_product4 {x : Fin 5 → ℚ}
    (hx : x∈normalizedRelations fixedSUnitGroup 4) (z : Fin 4 → ℤ) (s : fixedSUnitGroup)
    (hscale : ∀ i : Fin 4,(z i : ℚ)=((s : ℚˣ) : ℚ)*x i.castSucc) :
    (∀ i,threePlaceProduct (z i : ℚ)=1) ∧ threePlaceProduct (∑ i : Fin 4,(z i : ℚ))=1 := by
  have hu (i : Fin 5) : threePlaceProduct (x i)=1 := by
    obtain ⟨u,hu⟩ := hx.2.1 i
    rw [← hu]
    exact fixed_sunit_product_formula u
  have hz (i : Fin 4) : threePlaceProduct (z i : ℚ)=1 := by
    rw [hscale,threePlaceProduct_mul,fixed_sunit_product_formula,hu]
    norm_num
  refine ⟨hz,?_⟩
  have hs : (∑ i : Fin 4,(z i : ℚ))= -(((s : ℚˣ) : ℚ)*x 4) := by
    simp_rw [hscale]
    rw [← Finset.mul_sum]
    have hh : (∑ i : Fin 4,x i.castSucc)= -x 4 := by
      have h := hx.2.2.1
      rw [Fin.sum_univ_castSucc] at h
      exact eq_neg_of_add_eq_zero_left h
    rw [hh,mul_neg]
  rw [hs]
  have hn (q : ℚ) : threePlaceProduct (-q)=threePlaceProduct q := by simp [threePlaceProduct]
  rw [hn,threePlaceProduct_mul,fixed_sunit_product_formula,hu]
  norm_num

theorem allpoint_primitive_product4 {x : Fin 5 → ℚ}
    (hx : x∈normalizedRelations fixedSUnitGroup 4) (z : Fin 4 → ℤ) (s : fixedSUnitGroup)
    (hz : PrimitiveFour z) (hscale : ∀ i : Fin 4,(z i : ℚ)=((s : ℚˣ) : ℚ)*x i.castSucc) :
    ∃ choice : Fin 3 → Fin 4,fourRetainedProduct choice (fun i => (z i : ℚ))*archFourHeight z=1 := by
  choose choice hc using fun tau => exists_four_maximal_coordinate tau (fun i => (z i : ℚ))
  refine ⟨choice,?_⟩
  have h := four_retained_product_height choice (fun i => (z i : ℚ)) hc
  rw [primitive_four_height z hz] at h
  have hp := five_term_integer_product4 hx z s hscale
  simpa [hp.1,hp.2] using h

theorem allpoint_form_product4 {x : Fin 5 → ℚ}
    (hx : x∈normalizedRelations fixedSUnitGroup 4) (z : Fin 4 → ℤ) (s : fixedSUnitGroup)
    (hscale : ∀ i : Fin 4,(z i : ℚ)=((s : ℚˣ) : ℚ)*x i.castSucc) (k i : Fin 4) :
    threePlaceProduct (fourRetainedForm k i (fun j => (z j : ℚ)))=1 := by
  have hp := five_term_integer_product4 hx z s hscale
  by_cases hi : i=k
  · simpa only [fourRetainedForm,if_pos hi] using hp.2
  · simpa only [fourRetainedForm,if_neg hi] using hp.1 i

theorem allpoint_form_arch_bound4 (z : Fin 4 → ℤ) (k i : Fin 4) :
    |fourRetainedForm k i (fun j => (z j : ℚ))|≤4*archFourHeight z := by
  have hc (j : Fin 4) : |(z j : ℚ)|≤archFourHeight z := four_local_coordinate_le 0 (fun i => (z i : ℚ)) j
  have hH : 0≤archFourHeight z := (abs_nonneg (z 0 : ℚ)).trans (hc 0)
  unfold fourRetainedForm
  split_ifs
  · calc
      |∑ j : Fin 4,(z j : ℚ)|≤∑ j : Fin 4,|(z j : ℚ)| := Finset.abs_sum_le_sum_abs _ _
      _≤∑ _j : Fin 4,archFourHeight z := Finset.sum_le_sum (fun j _ => hc j)
      _=4*archFourHeight z := by simp [mul_comm]
  · exact (hc i).trans (by linarith)

end JSP000334
