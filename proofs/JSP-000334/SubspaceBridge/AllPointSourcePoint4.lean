import SubspaceBridge.AllPointActualValues4
import SubspaceBridge.AllPointWeights4
import SubspaceBridge.AllPointActualValues3
namespace JSP000334
open scoped BigOperators Matrix

def retainedRationalMatrix4 (k : Fin 4) : Matrix (Fin 4) (Fin 4) ℚ :=
  fun i j => (retainedIntegerMatrix4 k i j : ℚ)
def retainedRealMatrix4 (k : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (retainedIntegerMatrix4 k i j : ℝ)

theorem retained_rational_det4 (k : Fin 4) : (retainedRationalMatrix4 k).det=1 := by
  have hh : ((retainedIntegerMatrix4 k).map (Int.castRingHom ℚ)).det =
      ((retainedIntegerMatrix4 k).det : ℚ) := ((Int.castRingHom ℚ).map_det _).symm
  rw [retained_integer_matrix_det4] at hh
  simpa only [Int.cast_one] using hh

theorem retained_real_det4 (k : Fin 4) : (retainedRealMatrix4 k).det=1 := by
  have hh : ((retainedIntegerMatrix4 k).map (Int.castRingHom ℝ)).det =
      ((retainedIntegerMatrix4 k).det : ℝ) := ((Int.castRingHom ℝ).map_det _).symm
  rw [retained_integer_matrix_det4] at hh
  simpa only [Int.cast_one] using hh

theorem retained_rational_apply4 (k i : Fin 4) (z : Fin 4 → ℤ) :
    (retainedRationalMatrix4 k *ᵥ (fun j => (z j : ℚ))) i=
      fourRetainedForm k i (fun j => (z j : ℚ)) := by
  rw [← retained_integer_cast4]
  simp [retainedRationalMatrix4,Matrix.mulVec,dotProduct]

theorem retained_real_apply4 (k i : Fin 4) (z : Fin 4 → ℤ) :
    (retainedRealMatrix4 k *ᵥ CompoundFeasibility.integerReal z) i=
      (fourRetainedForm k i (fun j => (z j : ℚ)) : ℝ) := by
  rw [← retained_integer_cast4]
  simp [retainedRealMatrix4,CompoundFeasibility.integerReal,Matrix.mulVec,dotProduct]

noncomputable def allpoint_norms4 (choice : Fin 3 → Fin 4) (z : Fin 4 → ℤ) (tau : Fin 3) (i : Fin 4) : ℝ :=
  rationalPlaceNorm tau (fourRetainedForm (choice tau) i (fun j => (z j : ℚ)))

theorem allpoint_fixed_source_point4 {x : Fin 5 → ℚ}
    (hx : x∈normalizedRelations fixedSUnitGroup 4) (z : Fin 4 → ℤ) (s : fixedSUnitGroup)
    (hz : PrimitiveFour z) (hscale : ∀ i : Fin 4,(z i : ℚ)=((s : ℚˣ) : ℚ)*x i.castSucc)
    (hH : 4≤(archFourHeight z : ℝ)) :
    let Q := (archFourHeight z : ℝ)^8
    ∃ choice : Fin 3 → Fin 4,∃ d∈finiteWeightCandidates4 448,
      sourceWeightConditions4 d ∧
      CompoundFeasibility.OriginalVariableGap4.originalSourceSolution4
        (retainedRationalMatrix4 (choice 1)) (retainedRationalMatrix4 (choice 2))
        (retainedRealMatrix4 (choice 0)) (d 0) (d 1) (d 2) Q ((1 : ℝ)/64) z := by
  intro Q
  obtain ⟨choice,hret⟩ := allpoint_primitive_product4 hx z s hz hscale
  let a := allpoint_norms4 choice z
  have hl (tau : Fin 3) (i : Fin 4) : 0<a tau i ∧ (a tau i)⁻¹≤4*(archFourHeight z : ℝ) ∧
      (tau≠0 → a tau i≤1) := by
    let m := (retainedIntegerMatrix4 (choice tau) *ᵥ z) i
    have hp : threePlaceProduct (m : ℚ)=1 := by
      rw [retained_integer_cast4]
      exact allpoint_form_product4 hx z s hscale _ _
    have hh := allpoint_local_inverse3 m hp tau
    have hm : (m : ℚ)=fourRetainedForm (choice tau) i (fun j => (z j : ℚ)) := retained_integer_cast4 _ _ _
    rw [hm] at hh
    dsimp only [a,allpoint_norms4]
    refine ⟨by exact_mod_cast hh.1,?_,?_⟩
    · exact_mod_cast hh.2.1.trans (allpoint_form_arch_bound4 z (choice tau) i)
    · intro ht
      exact_mod_cast hh.2.2 ht
  have hp : (∏ tau,∏ i,a tau i)*(archFourHeight z : ℝ)=1 := by
    dsimp only [a,allpoint_norms4]
    unfold fourRetainedProduct at hret
    exact_mod_cast hret
  obtain ⟨hQ,hc,_,hr,hf⟩ := allpoint_balanced_weights4 (archFourHeight z : ℝ) hH a
    (fun tau i => (hl tau i).1)
    (fun i => by
      change ((|fourRetainedForm (choice 0) i (fun j => (z j : ℚ))| : ℚ) : ℝ)≤_
      exact_mod_cast allpoint_form_arch_bound4 z (choice 0) i)
    (fun tau ht i => (hl tau i).2.2 ht) (fun tau i => (hl tau i).2.1) hp
  let c := sourceLogWeights4 Q (allpoint_balanced_values4 Q a)
  let d := finiteWeightApprox4 448 c
  obtain ⟨hd,hdreal,hdfin⟩ := finiteWeightApprox4_bounds 448 (by norm_num) c hc
  have hq0 := zero_lt_one.trans hQ
  have hnz : z≠0 := by
    intro he
    obtain ⟨b,hb⟩ := hz
    simp [he] at hb
  refine ⟨choice,d,finiteWeightApprox4_mem 448 (by norm_num) c hc,hd,
    hnz,hQ,by norm_num,?_,?_,?_⟩
  · intro i
    rw [retained_real_apply4]
    have heq : |(fourRetainedForm (choice 0) i (fun j => (z j : ℚ)) : ℝ)|=a 0 i := by
      simp [a,allpoint_norms4,rationalPlaceNorm]
    rw [heq,hr]
    apply Real.rpow_le_rpow_of_exponent_le hQ.le
    have hh := hdreal i
    norm_num at hh
    linarith
  · intro i
    rw [retained_rational_apply4]
    change a 1 i≤Q^(d 1 i)
    rw [hf 1 (by decide) i]
    exact Real.rpow_le_rpow_of_exponent_le hQ.le (hdfin 1 (by decide) i)
  · intro i
    rw [retained_rational_apply4]
    change a 2 i≤Q^(d 2 i)
    rw [hf 2 (by decide) i]
    exact Real.rpow_le_rpow_of_exponent_le hQ.le (hdfin 2 (by decide) i)

end JSP000334
