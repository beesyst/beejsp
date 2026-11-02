import SubspaceBridge.WeightedDiagonalCoefficients4
import SubspaceBridge.WeightedDiagonalTransport4
import SubspaceBridge.FiveTermSource4
namespace JSP000334
open scoped BigOperators Matrix

def weightedFiveTerms4 (A : ℚ) (B : Fin 4 → ℚ) (u : Fin 4 → fixedSUnitGroup) : Fin 5 → ℚ :=
  Fin.cons A (fun i => B i*((u i : ℚˣ) : ℚ))

def WeightedFiveTermSolutions (A : ℚ) (B : Fin 4 → ℚ) : Set (Fin 4 → fixedSUnitGroup) :=
  {u | A+∑ i,B i*((u i : ℚˣ) : ℚ)=0 ∧ Nondegenerate (weightedFiveTerms4 A B u)}

theorem weighted_original_product_input4 (A : ℚ) (B : Fin 4 → ℚ) (L : ℕ) (t : Fin 4 → ℤ)
    (ht : ∀ i,t i≠0) (hcoef : ∀ i,(t i : ℚ)=(L : ℚ)*B i)
    (u : Fin 4 → fixedSUnitGroup) (hu : u∈WeightedFiveTermSolutions A B) :
    ∃ z : Fin 4 → ℤ,∃ s : fixedSUnitGroup,∃ g : ℕ,
      0<g ∧ (g : ℤ)∣(∏ i,t i) ∧ ∃ y : Fin 4 → ℤ,
      (∀ i,(z i : ℚ)=((s : ℚˣ) : ℚ)*((u i : ℚˣ) : ℚ)) ∧
      (∀ i,t i*z i=(g : ℤ)*y i) ∧
      weightedFixedProductQuadruples4 (fun i => (t i : ℚ)/g) ((L : ℚ)*A/g) y := by
  obtain ⟨z,s,hz,hzn,hscale⟩ := weighted_primitive_sunit_coordinates4 u
  obtain ⟨g,hg,hgd,y,hy,hyn,he⟩ := weighted_diagonal_primitive4 t z ht hz hzn
  have hgn : (g : ℚ)≠0 := by exact_mod_cast ne_of_gt hg
  have hcoord (i : Fin 4) : (y i : ℚ)=((t i : ℚ)/g)*((s : ℚˣ) : ℚ)*((u i : ℚˣ) : ℚ) := by
    have hc := congrArg ((↑) : ℤ → ℚ) (he i)
    push_cast at hc
    rw [hscale i] at hc
    field_simp
    nlinarith only [hc]
  have hsum : (∑ i : Fin 4,(y i : ℚ))=-((L : ℚ)*A/g)*((s : ℚˣ) : ℚ) := by
    calc
      _=((L : ℚ)/g)*((s : ℚˣ) : ℚ)*(∑ i,B i*((u i : ℚˣ) : ℚ)) := by
        simp_rw [hcoord,hcoef]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _=_ := by rw [show (∑ i,B i*((u i : ℚˣ) : ℚ))=-A by linarith [hu.1]];ring
  have hc (i : Fin 4) : threePlaceProduct (y i : ℚ)=threePlaceProduct ((t i : ℚ)/g) := by
    rw [hcoord]
    exact weighted_scaled_product3 _ _ _
  have hs : threePlaceProduct (∑ i : Fin 4,(y i : ℚ))=threePlaceProduct ((L : ℚ)*A/g) := by
    rw [hsum,threePlaceProduct_mul,fixed_sunit_product_formula,mul_one]
    simp [threePlaceProduct]
  exact ⟨z,s,g,hg,hgd,y,hscale,he,hy,hc,hs⟩

end JSP000334
