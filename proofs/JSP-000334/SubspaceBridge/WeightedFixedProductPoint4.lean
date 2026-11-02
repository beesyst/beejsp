import SubspaceBridge.WeightedDiagonalPoint4
import SubspaceBridge.WeightedDiagonalProducts3
namespace JSP000334
open scoped BigOperators Matrix

def weightedProductBound4 (k : Fin 4 → ℚ) (a : ℚ) : ℚ :=
  max 1 (max (threePlaceProduct (k 0))⁻¹
    (max (threePlaceProduct (k 1))⁻¹ (max (threePlaceProduct (k 2))⁻¹ (max (threePlaceProduct (k 3))⁻¹ (threePlaceProduct a)⁻¹))))

noncomputable def weightedProductCutoff4 (k : Fin 4 → ℚ) (a : ℚ) : ℝ :=
  max 4 (max (4*(weightedProductBound4 k a : ℝ))
    (max ((weightedProductConstant4 k a : ℝ)⁻¹) ((weightedProductConstant4 k a : ℝ)^5)))

theorem weighted_fixed_product_point4 (k : Fin 4 → ℚ) (a : ℚ)
    (hk : ∀ i,k i≠0) (ha : a≠0) (y : Fin 4 → ℤ) (hy : PrimitiveFour y)
    (hc : ∀ i,threePlaceProduct (y i : ℚ)=threePlaceProduct (k i))
    (hs : threePlaceProduct (∑ i : Fin 4,(y i : ℚ))=threePlaceProduct a)
    (hH : weightedProductCutoff4 k a≤(archFourHeight y : ℝ)) :
    let Q := (archFourHeight y : ℝ)^8
    ∃ choice : Fin 3 → Fin 4,∃ d∈finiteWeightCandidates4 560,
      sourceWeightConditions4 d ∧
      CompoundFeasibility.OriginalVariableGap4.originalSourceSolution4
        (retainedRationalMatrix4 (choice 1)) (retainedRationalMatrix4 (choice 2))
        (retainedRealMatrix4 (choice 0)) (d 0) (d 1) (d 2) Q ((1 : ℝ)/80) y := by
  intro Q
  let B := weightedProductBound4 k a
  have hB1 : (1 : ℚ)≤B := le_max_left _ _
  have hB0 : 0≤B := le_trans (by norm_num) hB1
  have hb (i : Fin 4) : (threePlaceProduct (k i))⁻¹≤B := by
    fin_cases i
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    · exact (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
    · exact ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hba : (threePlaceProduct a)⁻¹≤B :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hco (i : Fin 4) : 0<threePlaceProduct (y i : ℚ) ∧ max 1 (threePlaceProduct (y i : ℚ))⁻¹≤B := by
    rw [hc]
    exact ⟨weighted_three_place_pos3 (hk i),max_le hB1 (hb i)⟩
  have hso : 0<threePlaceProduct (∑ i : Fin 4,(y i : ℚ)) ∧ max 1 (threePlaceProduct (∑ i : Fin 4,(y i : ℚ)))⁻¹≤B := by
    rw [hs]
    exact ⟨weighted_three_place_pos3 ha,max_le hB1 hba⟩
  have hform (l i : Fin 4) :
      0<threePlaceProduct (fourRetainedForm l i (fun j => (y j : ℚ))) ∧
      max 1 (threePlaceProduct (fourRetainedForm l i (fun j => (y j : ℚ))))⁻¹≤B := by
    by_cases hi : i=l
    · simpa only [fourRetainedForm,if_pos hi] using hso
    · simpa only [fourRetainedForm,if_neg hi] using hco i
  obtain ⟨choice,hprod⟩ := weighted_fixed_product_height4 y hy k a hc hs
  have hlocal (tau : Fin 3) (i : Fin 4) :
      0<(rationalPlaceNorm tau (fourRetainedForm (choice tau) i (fun j => (y j : ℚ))) : ℝ) ∧
      ((rationalPlaceNorm tau (fourRetainedForm (choice tau) i (fun j => (y j : ℚ))) : ℝ))⁻¹≤
        (4*B : ℚ)*(archFourHeight y : ℝ) := by
    let m := (retainedIntegerMatrix4 (choice tau) *ᵥ y) i
    have hm : (m : ℚ)=fourRetainedForm (choice tau) i (fun j => (y j : ℚ)) := retained_integer_cast4 _ _ _
    have hp : 0<threePlaceProduct (m : ℚ) := by rw [hm];exact (hform _ _).1
    have hh := weighted_integer_local_inverse3 m hp rfl tau
    rw [hm] at hh
    refine ⟨by exact_mod_cast hh.1,?_⟩
    have hbnd : (rationalPlaceNorm tau (fourRetainedForm (choice tau) i (fun j => (y j : ℚ))))⁻¹≤4*B*archFourHeight y := by
      calc
        _≤max 1 (threePlaceProduct (fourRetainedForm (choice tau) i (fun j => (y j : ℚ))))⁻¹*
            |fourRetainedForm (choice tau) i (fun j => (y j : ℚ))| := hh.2.1
        _≤B*(4*archFourHeight y) := mul_le_mul (hform _ _).2 (allpoint_form_arch_bound4 y _ _) (abs_nonneg _) hB0
        _=_ := by ring
    exact_mod_cast hbnd
  have hK : 0<(weightedProductConstant4 k a : ℝ) := by
    have hpos : 0<weightedProductConstant4 k a :=
      mul_pos (Finset.prod_pos (fun i _ => weighted_three_place_pos3 (hk i))) (weighted_three_place_pos3 ha)
    exact_mod_cast hpos
  have hC4 : (4 : ℝ)≤4*(B : ℝ) := by exact_mod_cast (show (4 : ℚ)≤4*B by linarith)
  have hH4 : (4 : ℝ)≤(archFourHeight y : ℝ) := (le_max_left _ _).trans hH
  have hC : 4*(B : ℝ)≤(archFourHeight y : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hH
  have hKi : (weightedProductConstant4 k a : ℝ)⁻¹≤(archFourHeight y : ℝ) :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hH
  have hK5 : (weightedProductConstant4 k a : ℝ)^5≤(archFourHeight y : ℝ) :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hH
  obtain ⟨d,hd,hcond,hsol⟩ := weighted_integer_source_point4 y hy choice
    (4*(B : ℝ)) (weightedProductConstant4 k a : ℝ) hC4 hK hH4 hC hKi hK5
    (fun tau i => (hlocal tau i).1) (fun tau i => by simpa using (hlocal tau i).2)
    (by exact_mod_cast hprod)
  exact ⟨choice,d,hd,hcond,hsol⟩

end JSP000334
