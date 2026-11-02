import ElementaryThreeTerm
import SubspaceBridge.CofactorOriginalRankOne3
open scoped BigOperators Matrix
namespace JSP000334

theorem allpoint_primitive_product3 {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3)
    (z : IntegerTriple) (s : fixedSUnitGroup) (hz : PrimitiveTriple z)
    (hscale : ∀ i : Fin 3, (z i : ℚ) = ((s : ℚˣ) : ℚ)*x i.castSucc) :
    ∃ choice : Fin 3 → Fin 3,
      tripleChoiceFormsProduct choice (fun i => (z i : ℚ))*archTripleHeight z = 1 := by
  obtain ⟨choice,hret⟩ := four_term_retained_product_height hx
  have hvec : (fun i => (z i : ℚ)) = (fun i => ((s : ℚˣ) : ℚ)*x i.castSucc) := funext hscale
  have hH := primitive_triple_height z hz
  rw [hvec,tripleHeight_sunit_scale] at hH
  refine ⟨choice,?_⟩
  rw [← hH,hvec,tripleChoiceFormsProduct_sunit_scale]
  exact hret

theorem allpoint_primitive_input3 {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3) :
    ∃ w : Fin 4 → ℤ, ∃ s : fixedSUnitGroup,
      PrimitiveTriple (fun i => w i.castSucc) ∧ (∀ i, w i ≠ 0) ∧
      (∑ i, w i = 0) ∧ Nondegenerate (fun i => (w i : ℚ)) ∧
      (∀ i, (w i : ℚ) = ((s : ℚˣ) : ℚ)*x i) ∧
      ∃ choice : Fin 3 → Fin 3,
        tripleChoiceFormsProduct choice (fun i => (w i.castSucc : ℚ))*
          archTripleHeight (fun i => w i.castSucc) = 1 := by
  obtain ⟨w,s,hp,hn,hs,hd,he⟩ := exists_primitive_four_term_relation hx
  exact ⟨w,s,hp,hn,hs,hd,he,allpoint_primitive_product3 hx _ s hp (fun i => he i.castSucc)⟩

end JSP000334
