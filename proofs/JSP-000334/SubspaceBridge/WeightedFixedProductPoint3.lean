import SubspaceBridge.WeightedDiagonalFamily3
import SubspaceBridge.WeightedDiagonalProducts3
namespace JSP000334
open scoped BigOperators Matrix

def weightedProductConstant3 (k : Fin 3 → ℚ) (a : ℚ) : ℚ :=
  threePlaceProduct (k 0)*threePlaceProduct (k 1)*threePlaceProduct (k 2)*threePlaceProduct a

def weightedProductBound3 (k : Fin 3 → ℚ) (a : ℚ) : ℚ :=
  max 1 (max (threePlaceProduct (k 0))⁻¹
    (max (threePlaceProduct (k 1))⁻¹ (max (threePlaceProduct (k 2))⁻¹ (threePlaceProduct a)⁻¹)))

noncomputable def weightedProductCutoff3 (k : Fin 3 → ℚ) (a : ℚ) : ℝ :=
  max 3 (max (3*(weightedProductBound3 k a : ℝ))
    (max ((weightedProductConstant3 k a : ℝ)⁻¹) ((weightedProductConstant3 k a : ℝ)^4)))

theorem weighted_fixed_product_point3 (k : Fin 3 → ℚ) (a : ℚ)
    (hk : ∀ i,k i≠0) (ha : a≠0) (y : IntegerTriple) (hy : PrimitiveTriple y)
    (hc : ∀ i,threePlaceProduct (y i : ℚ)=threePlaceProduct (k i))
    (hs : threePlaceProduct ((y 0 : ℚ)+y 1+y 2)=threePlaceProduct a)
    (hH : weightedProductCutoff3 k a≤(archTripleHeight y : ℝ)) :
    let Q := (archTripleHeight y : ℝ)^4
    ∃ choice : Fin 3 → Fin 3,∃ d∈finiteWeightCandidates3 336,
      ∃ hQ : 1<Q,sourceWeightConditions3 d ∧
      y∈qSourceLattice3 (choice 1) (choice 2) Q (d 1) (d 2) ∧
      coordinateGauge3 (qSourceCoordinates3 (choice 0) Q (d 0) hQ) (integerTripleReal3 y)≤Q^(-(1 : ℝ)/24) := by
  intro Q
  let B := weightedProductBound3 k a
  have hB1 : (1 : ℚ)≤B := le_max_left _ _
  have hB0 : 0≤B := le_trans (by norm_num) hB1
  have hb (i : Fin 3) : (threePlaceProduct (k i))⁻¹≤B := by
    fin_cases i
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    · exact (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hba : (threePlaceProduct a)⁻¹≤B :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hco (i : Fin 3) : 0<threePlaceProduct (y i : ℚ) ∧ max 1 (threePlaceProduct (y i : ℚ))⁻¹≤B := by
    rw [hc]
    exact ⟨weighted_three_place_pos3 (hk i),max_le hB1 (hb i)⟩
  have hso : 0<threePlaceProduct ((y 0 : ℚ)+y 1+y 2) ∧ max 1 (threePlaceProduct ((y 0 : ℚ)+y 1+y 2))⁻¹≤B := by
    rw [hs]
    exact ⟨weighted_three_place_pos3 ha,max_le hB1 hba⟩
  have hform (l i : Fin 3) :
      0<threePlaceProduct (threeCoordinateSumForms l i (fun j => (y j : ℚ))) ∧
      max 1 (threePlaceProduct (threeCoordinateSumForms l i (fun j => (y j : ℚ))))⁻¹≤B := by
    fin_cases i
    · simpa [threeCoordinateSumForms] using hco (l.succAbove 0)
    · simpa [threeCoordinateSumForms] using hco (l.succAbove 1)
    · simpa [threeCoordinateSumForms] using hso
  obtain ⟨choice,hprod⟩ := weighted_fixed_product_height3 y hy k a hc hs
  have hlocal (tau i : Fin 3) :
      0<(rationalPlaceNorm tau (threeCoordinateSumForms (choice tau) i (fun j => (y j : ℚ))) : ℝ) ∧
      ((rationalPlaceNorm tau (threeCoordinateSumForms (choice tau) i (fun j => (y j : ℚ))) : ℝ))⁻¹≤
        (3*B : ℚ)*(archTripleHeight y : ℝ) := by
    let m := (retainedIntegerMatrix3 (choice tau) *ᵥ y) i
    have hm : (m : ℚ)=threeCoordinateSumForms (choice tau) i (fun j => (y j : ℚ)) := retainedIntegerMatrix3_apply _ _ _
    have hp : 0<threePlaceProduct (m : ℚ) := by rw [hm];exact (hform _ _).1
    have hh := weighted_integer_local_inverse3 m hp rfl tau
    rw [hm] at hh
    refine ⟨by exact_mod_cast hh.1,?_⟩
    have hbnd : (rationalPlaceNorm tau (threeCoordinateSumForms (choice tau) i (fun j => (y j : ℚ))))⁻¹≤3*B*archTripleHeight y := by
      calc
        _≤max 1 (threePlaceProduct (threeCoordinateSumForms (choice tau) i (fun j => (y j : ℚ))))⁻¹*
            |threeCoordinateSumForms (choice tau) i (fun j => (y j : ℚ))| := hh.2.1
        _≤B*(3*archTripleHeight y) := mul_le_mul (hform _ _).2 (allpoint_form_arch_bound3 y _ _) (abs_nonneg _) hB0
        _=_ := by ring
    exact_mod_cast hbnd
  have hK : 0<(weightedProductConstant3 k a : ℝ) := by
    have hpos := mul_pos (mul_pos (mul_pos (weighted_three_place_pos3 (hk 0)) (weighted_three_place_pos3 (hk 1)))
      (weighted_three_place_pos3 (hk 2))) (weighted_three_place_pos3 ha)
    exact_mod_cast hpos
  have hC3 : (3 : ℝ)≤3*(B : ℝ) := by exact_mod_cast (show (3 : ℚ)≤3*B by linarith)
  have hH3 : (3 : ℝ)≤(archTripleHeight y : ℝ) := (le_max_left _ _).trans hH
  have hC : 3*(B : ℝ)≤(archTripleHeight y : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hH
  have hKi : (weightedProductConstant3 k a : ℝ)⁻¹≤(archTripleHeight y : ℝ) :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hH
  have hK4 : (weightedProductConstant3 k a : ℝ)^4≤(archTripleHeight y : ℝ) :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hH
  obtain ⟨d,hd,hQ,hcond,hmem,hshort⟩ := weighted_integer_source_point3 y choice
    (3*(B : ℝ)) (weightedProductConstant3 k a : ℝ) hC3 hK hH3 hC hKi hK4
    (fun tau i => (hlocal tau i).1) (fun tau i => by simpa using (hlocal tau i).2)
    (by exact_mod_cast hprod)
  exact ⟨choice,d,hd,hQ,hcond,hmem,hshort⟩

end JSP000334
