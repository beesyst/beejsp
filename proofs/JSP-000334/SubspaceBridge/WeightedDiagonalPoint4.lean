import SubspaceBridge.WeightedDiagonalWeights4
import SubspaceBridge.AllPointSourcePoint4
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_integer_source_point4 (y : Fin 4 → ℤ) (hy : PrimitiveFour y)
    (choice : Fin 3 → Fin 4) (C K : ℝ) (hC4 : 4≤C) (hK : 0<K)
    (hH : 4≤(archFourHeight y : ℝ)) (hC : C≤(archFourHeight y : ℝ))
    (hKi : K⁻¹≤(archFourHeight y : ℝ)) (hK5 : K^5≤(archFourHeight y : ℝ))
    (ha : ∀ tau i,0<(rationalPlaceNorm tau (fourRetainedForm (choice tau) i (fun j => (y j : ℚ))) : ℝ))
    (hinv : ∀ tau i,((rationalPlaceNorm tau (fourRetainedForm (choice tau) i (fun j => (y j : ℚ))) : ℝ))⁻¹≤C*(archFourHeight y : ℝ))
    (hprod : (fourRetainedProduct choice (fun j => (y j : ℚ)) : ℝ)*(archFourHeight y : ℝ)=K) :
    let Q := (archFourHeight y : ℝ)^8
    ∃ d∈finiteWeightCandidates4 560,sourceWeightConditions4 d ∧
      CompoundFeasibility.OriginalVariableGap4.originalSourceSolution4
        (retainedRationalMatrix4 (choice 1)) (retainedRationalMatrix4 (choice 2))
        (retainedRealMatrix4 (choice 0)) (d 0) (d 1) (d 2) Q ((1 : ℝ)/80) y := by
  intro Q
  let a := allpoint_norms4 choice y
  have hf : ∀ tau,tau≠0 → ∀ i,a tau i≤1 := by
    intro tau ht i
    change (rationalPlaceNorm tau (fourRetainedForm (choice tau) i (fun j => (y j : ℚ))) : ℝ)≤1
    rw [← retained_integer_cast4]
    fin_cases tau
    · exact (ht rfl).elim
    · exact_mod_cast padicNorm.of_int (p:=2) ((retainedIntegerMatrix4 (choice 1) *ᵥ y) i)
    · exact_mod_cast padicNorm.of_int (p:=3) ((retainedIntegerMatrix4 (choice 2) *ᵥ y) i)
  have hp : (∏ tau,∏ i,a tau i)*(archFourHeight y : ℝ)=K := by
    dsimp [a,allpoint_norms4]
    unfold fourRetainedProduct at hprod
    exact_mod_cast hprod
  have hrb : ∀ i,a 0 i≤C*(archFourHeight y : ℝ) := by
    intro i
    have hh := allpoint_form_arch_bound4 y (choice 0) i
    have hcast : a 0 i≤4*(archFourHeight y : ℝ) := by
      change ((|fourRetainedForm (choice 0) i (fun j => (y j : ℚ))| : ℚ) : ℝ)≤4*(archFourHeight y : ℝ)
      exact_mod_cast hh
    exact hcast.trans (mul_le_mul_of_nonneg_right hC4 (by linarith))
  obtain ⟨hQ,hc,_,hr,hf⟩ := weighted_balanced_weights4 (archFourHeight y : ℝ) K C
    hH hK hC hKi hK5 a ha hrb hf hinv hp
  let c := sourceLogWeights4 Q (weightedBalancedValues4 (archFourHeight y : ℝ) K a)
  let d := finiteWeightApprox4 560 c
  obtain ⟨hd,hdreal,hdfin⟩ := finiteWeightApprox4_bounds 560 (by norm_num) c hc
  have hq0 := zero_lt_one.trans hQ
  have hnz : y≠0 := by
    intro he
    obtain ⟨b,hb⟩ := hy
    simp [he] at hb
  refine ⟨d,finiteWeightApprox4_mem 560 (by norm_num) c hc,hd,
    hnz,hQ,by norm_num,?_,?_,?_⟩
  · intro i
    rw [retained_real_apply4]
    have heq : |(fourRetainedForm (choice 0) i (fun j => (y j : ℚ)) : ℝ)|=a 0 i := by
      simp [a,allpoint_norms4,rationalPlaceNorm]
    rw [heq]
    apply (hr i).trans
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
