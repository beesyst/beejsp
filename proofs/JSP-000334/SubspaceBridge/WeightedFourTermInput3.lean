import SubspaceBridge.WeightedFixedProductCover3
import SubspaceBridge.WeightedDiagonalCoefficients3
import SubspaceBridge.WeightedDiagonalTransport3
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_original_product_input3 (A B C D : ℚ) (L : ℕ) (t : Fin 3 → ℤ)
    (ht : ∀ i,t i≠0) (hcoef : ∀ i,(t i : ℚ)=(L : ℚ)*(![B,C,D] i))
    (p : fixedSUnitGroup × fixedSUnitGroup × fixedSUnitGroup)
    (hp : p∈WeightedFourTermSolutions A B C D) :
    ∃ z : IntegerTriple,∃ s : fixedSUnitGroup,∃ g : ℕ,
      0<g ∧ (g : ℤ)∣t 0*t 1*t 2 ∧ ∃ y : IntegerTriple,
      (∀ i,(z i : ℚ)=((s : ℚˣ) : ℚ)*(((![p.1,p.2.1,p.2.2] i) : ℚˣ) : ℚ)) ∧
      (∀ i,t i*z i=(g : ℤ)*y i) ∧
      weightedFixedProductTriples3 (fun i => (t i : ℚ)/g) ((L : ℚ)*A/g) y := by
  let u : Fin 3 → fixedSUnitGroup := ![p.1,p.2.1,p.2.2]
  obtain ⟨z,s,hz,hzn,hscale⟩ := weighted_primitive_sunit_coordinates3 u
  obtain ⟨g,hg,hgd,y,hy,hyn,he⟩ := weighted_diagonal_primitive3 t z ht hz hzn
  have hgn : (g : ℚ)≠0 := by exact_mod_cast ne_of_gt hg
  have hcoord (i : Fin 3) : (y i : ℚ)=((t i : ℚ)/g)*((s : ℚˣ) : ℚ)*((u i : ℚˣ) : ℚ) := by
    have hc := congrArg ((↑) : ℤ → ℚ) (he i)
    push_cast at hc
    rw [hscale i] at hc
    field_simp
    nlinarith only [hc]
  have hrel : A+B*((u 0 : ℚˣ) : ℚ)+C*((u 1 : ℚˣ) : ℚ)+D*((u 2 : ℚˣ) : ℚ)=0 := hp.1
  have hsum : (y 0 : ℚ)+y 1+y 2=-((L : ℚ)*A/g)*((s : ℚˣ) : ℚ) := by
    rw [hcoord 0,hcoord 1,hcoord 2,hcoef 0,hcoef 1,hcoef 2]
    change ((L : ℚ)*B/g)*((s : ℚˣ) : ℚ)*((u 0 : ℚˣ) : ℚ)+
      ((L : ℚ)*C/g)*((s : ℚˣ) : ℚ)*((u 1 : ℚˣ) : ℚ)+
      ((L : ℚ)*D/g)*((s : ℚˣ) : ℚ)*((u 2 : ℚˣ) : ℚ)=-((L : ℚ)*A/g)*((s : ℚˣ) : ℚ)
    field_simp
    linear_combination (L : ℚ)*((s : ℚˣ) : ℚ)*hrel
  obtain ⟨hc,hs,_⟩ := weighted_diagonal_products3 t (L : ℚ) A g u s y hy hcoord hsum
  exact ⟨z,s,g,hg,hgd,y,hscale,he,hy,hc,hs⟩

end JSP000334
