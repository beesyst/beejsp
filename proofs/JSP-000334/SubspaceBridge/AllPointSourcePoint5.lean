import SubspaceBridge.AllPointActualValues5
import SubspaceBridge.AllPointWeights5
import SubspaceBridge.AllPointActualValues3
namespace JSP000334
open scoped BigOperators Matrix

def retainedRationalMatrix5 (k : Fin 5) : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i j => (retainedIntegerMatrix5 k i j : ℚ)
def retainedRealMatrix5 (k : Fin 5) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => (retainedIntegerMatrix5 k i j : ℝ)

theorem retained_rational_det5 (k : Fin 5) : (retainedRationalMatrix5 k).det=1 := by
  have he : retainedRationalMatrix5 k =
      Matrix.updateRow (1 : Matrix (Fin 5) (Fin 5) ℚ) k
        (∑ j : Fin 5,(1 : ℚ) • (1 : Matrix (Fin 5) (Fin 5) ℚ) j) := by
    ext i j
    by_cases hi : i=k <;> simp [retainedRationalMatrix5,retainedIntegerMatrix5,Matrix.updateRow,hi,Matrix.one_apply]
  rw [he,Matrix.det_updateRow_sum]
  simp

theorem retained_real_det5 (k : Fin 5) : (retainedRealMatrix5 k).det=1 := by
  have he : retainedRealMatrix5 k =
      Matrix.updateRow (1 : Matrix (Fin 5) (Fin 5) ℝ) k
        (∑ j : Fin 5,(1 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ) j) := by
    ext i j
    by_cases hi : i=k <;> simp [retainedRealMatrix5,retainedIntegerMatrix5,Matrix.updateRow,hi,Matrix.one_apply]
  rw [he,Matrix.det_updateRow_sum]
  simp

theorem retained_rational_apply5 (k i : Fin 5) (z : Fin 5 → ℤ) :
    (retainedRationalMatrix5 k *ᵥ (fun j => (z j : ℚ))) i=
      fiveRetainedForm k i (fun j => (z j : ℚ)) := by
  rw [← retained_integer_cast5]
  simp [retainedRationalMatrix5,Matrix.mulVec,dotProduct]

theorem retained_real_apply5 (k i : Fin 5) (z : Fin 5 → ℤ) :
    (retainedRealMatrix5 k *ᵥ CompoundFeasibility.integerReal z) i=
      (fiveRetainedForm k i (fun j => (z j : ℚ)) : ℝ) := by
  rw [← retained_integer_cast5]
  simp [retainedRealMatrix5,CompoundFeasibility.integerReal,Matrix.mulVec,dotProduct]

noncomputable def allpoint_norms5 (choice : Fin 3 → Fin 5) (z : Fin 5 → ℤ) (tau : Fin 3) (i : Fin 5) : ℝ :=
  rationalPlaceNorm tau (fiveRetainedForm (choice tau) i (fun j => (z j : ℚ)))

theorem allpoint_fixed_source_point5 {x : Fin 6 → ℚ}
    (hx : x∈normalizedRelations fixedSUnitGroup 5) (z : Fin 5 → ℤ) (s : fixedSUnitGroup)
    (hz : PrimitiveFive z) (hscale : ∀ i : Fin 5,(z i : ℚ)=((s : ℚˣ) : ℚ)*x i.castSucc)
    (hH : 5≤(archFiveHeight z : ℝ)) :
    let Q := (archFiveHeight z : ℝ)^8
    ∃ choice : Fin 3 → Fin 5,∃ d∈finiteWeightCandidates5 560,
      sourceWeightConditions5 d ∧
      CompoundFeasibility.OriginalVariableGap5.originalSourceSolution5
        (retainedRationalMatrix5 (choice 1)) (retainedRationalMatrix5 (choice 2))
        (retainedRealMatrix5 (choice 0)) (d 0) (d 1) (d 2) Q ((1 : ℝ)/80) z := by
  intro Q
  obtain ⟨choice,hret⟩ := allpoint_primitive_product5 hx z s hz hscale
  let a := allpoint_norms5 choice z
  have hl (tau : Fin 3) (i : Fin 5) : 0<a tau i ∧ (a tau i)⁻¹≤5*(archFiveHeight z : ℝ) ∧
      (tau≠0 → a tau i≤1) := by
    let m := (retainedIntegerMatrix5 (choice tau) *ᵥ z) i
    have hp : threePlaceProduct (m : ℚ)=1 := by
      rw [retained_integer_cast5]
      exact allpoint_form_product5 hx z s hscale _ _
    have hh := allpoint_local_inverse3 m hp tau
    have hm : (m : ℚ)=fiveRetainedForm (choice tau) i (fun j => (z j : ℚ)) := retained_integer_cast5 _ _ _
    rw [hm] at hh
    dsimp only [a,allpoint_norms5]
    refine ⟨by exact_mod_cast hh.1,?_,?_⟩
    · exact_mod_cast hh.2.1.trans (allpoint_form_arch_bound5 z (choice tau) i)
    · intro ht
      exact_mod_cast hh.2.2 ht
  have hp : (∏ tau,∏ i,a tau i)*(archFiveHeight z : ℝ)=1 := by
    dsimp only [a,allpoint_norms5]
    unfold fiveRetainedProduct at hret
    exact_mod_cast hret
  obtain ⟨hQ,hc,_,hr,hf⟩ := allpoint_balanced_weights5 (archFiveHeight z : ℝ) hH a
    (fun tau i => (hl tau i).1)
    (fun i => by
      change ((|fiveRetainedForm (choice 0) i (fun j => (z j : ℚ))| : ℚ) : ℝ)≤_
      exact_mod_cast allpoint_form_arch_bound5 z (choice 0) i)
    (fun tau ht i => (hl tau i).2.2 ht) (fun tau i => (hl tau i).2.1) hp
  let c := sourceLogWeights5 Q (allpoint_balanced_values5 Q a)
  let d := finiteWeightApprox5 560 c
  obtain ⟨hd,hdreal,hdfin⟩ := finiteWeightApprox5_bounds 560 (by norm_num) c hc
  have hq0 := zero_lt_one.trans hQ
  have hnz : z≠0 := by
    intro he
    obtain ⟨b,hb⟩ := hz
    simp [he] at hb
  refine ⟨choice,d,finiteWeightApprox5_mem 560 (by norm_num) c hc,hd,
    hnz,hQ,by norm_num,?_,?_,?_⟩
  · intro i
    rw [retained_real_apply5]
    have heq : |(fiveRetainedForm (choice 0) i (fun j => (z j : ℚ)) : ℝ)|=a 0 i := by
      simp [a,allpoint_norms5,rationalPlaceNorm]
    rw [heq,hr]
    apply Real.rpow_le_rpow_of_exponent_le hQ.le
    have hh := hdreal i
    norm_num at hh
    linarith
  · intro i
    rw [retained_rational_apply5]
    change a 1 i≤Q^(d 1 i)
    rw [hf 1 (by decide) i]
    exact Real.rpow_le_rpow_of_exponent_le hQ.le (hdfin 1 (by decide) i)
  · intro i
    rw [retained_rational_apply5]
    change a 2 i≤Q^(d 2 i)
    rw [hf 2 (by decide) i]
    exact Real.rpow_le_rpow_of_exponent_le hQ.le (hdfin 2 (by decide) i)

end JSP000334
