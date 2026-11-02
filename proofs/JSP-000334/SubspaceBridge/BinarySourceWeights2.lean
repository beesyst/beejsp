import SubspaceBridge.BinaryAnalyticContradiction2
open scoped BigOperators Classical
namespace JSP000334

noncomputable def binaryLogRaw (a : Fin 3 → Fin 2 → ℝ) (Q : ℝ) (tau : Fin 3) (i : Fin 2) : ℝ :=
  Real.log (a tau i)/Real.log Q
noncomputable def binaryLogAlpha (a : Fin 3 → Fin 2 → ℝ) (Q : ℝ) : ℝ :=
  -(∑ tau : Fin 3,∑ i : Fin 2,Real.log (a tau i))/(6*Real.log Q)
noncomputable def binaryLogWeights (a : Fin 3 → Fin 2 → ℝ) (Q : ℝ) (tau : Fin 3) (i : Fin 2) : ℝ :=
  binaryLogRaw a Q tau i+binaryLogAlpha a Q

theorem binary_log_balance (a : Fin 3 → Fin 2 → ℝ) (Q : ℝ) (hQ : 1<Q) :
    (∑ tau : Fin 3,∑ i : Fin 2,binaryLogWeights a Q tau i)=0 := by
  have hl : Real.log Q ≠ 0 := (Real.log_pos hQ).ne'
  simp only [binaryLogWeights,binaryLogRaw,binaryLogAlpha,Fin.sum_univ_three,Fin.sum_univ_two]
  field_simp
  ring

theorem binary_log_positive_margin (a : Fin 3 → Fin 2 → ℝ) (Q : ℝ) (hQ : 1<Q)
    (ha : ∀ tau i,0<a tau i)
    (hp : (∏ tau : Fin 3,∏ i : Fin 2,a tau i)<Real.rpow Q (-(1 : ℝ)/16)) :
    1/96<binaryLogAlpha a Q := by
  have hprod : 0<(∏ tau : Fin 3,∏ i : Fin 2,a tau i) :=
    Finset.prod_pos (fun tau _ => Finset.prod_pos (fun i _ => ha tau i))
  have hh := Real.log_lt_log hprod hp
  rw [Real.rpow_eq_pow,Real.log_rpow (lt_trans zero_lt_one hQ)] at hh
  rw [Real.log_prod _ _ (fun tau _ => ne_of_gt (Finset.prod_pos (fun i _ => ha tau i)))] at hh
  simp_rw [Real.log_prod _ _ (fun i _ => ne_of_gt (ha _ i))] at hh
  unfold binaryLogAlpha
  apply (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ)<6) (Real.log_pos hQ))).mpr
  linarith

theorem binary_log_source_bounds (a : Fin 3 → Fin 2 → ℝ) (Q : ℝ) (hQ : 1<Q)
    (ha : ∀ tau i,0<a tau i) (hd : (1 : ℝ)/192≤binaryLogAlpha a Q) :
    ∀ tau i,a tau i≤Real.rpow Q (binaryLogWeights a Q tau i-if tau=0 then (1 : ℝ)/192 else 0) := by
  intro tau i
  have he : a tau i=Real.rpow Q (binaryLogRaw a Q tau i) := by
    rw [Real.rpow_eq_pow,Real.rpow_def_of_pos (lt_trans zero_lt_one hQ)]
    unfold binaryLogRaw
    rw [mul_div_cancel₀ _ (Real.log_pos hQ).ne',Real.exp_log (ha tau i)]
  rw [he]
  apply Real.rpow_le_rpow_of_exponent_le hQ.le
  unfold binaryLogWeights
  by_cases ht : tau=0 <;> simp only [ht,ite_true,ite_false] <;> linarith

theorem binary_log_alpha_raw_sum (a : Fin 3 → Fin 2 → ℝ) (Q : ℝ) :
    binaryLogAlpha a Q=-(∑ tau : Fin 3,∑ i : Fin 2,binaryLogRaw a Q tau i)/6 := by
  unfold binaryLogAlpha binaryLogRaw
  simp only [← Finset.sum_div]
  ring

theorem binary_log_uniform_bound (a : Fin 3 → Fin 2 → ℝ) (Q : ℝ)
    (ha : 0≤binaryLogAlpha a Q)
    (hreal : ∀ i,0≤binaryLogRaw a Q 0 i ∧ binaryLogRaw a Q 0 i≤9/32)
    (hfinite : ∀ tau : Fin 3,tau ≠ 0 → ∀ i,-9/32≤binaryLogRaw a Q tau i ∧ binaryLogRaw a Q tau i≤0) :
    ∀ tau i,|binaryLogWeights a Q tau i|≤15/32 := by
  have hs := binary_log_alpha_raw_sum a Q
  rw [Fin.sum_univ_three] at hs
  simp only [Fin.sum_univ_two] at hs
  have h00 := hreal 0
  have h01 := hreal 1
  have h10 := hfinite 1 (by decide) 0
  have h11 := hfinite 1 (by decide) 1
  have h20 := hfinite 2 (by decide) 0
  have h21 := hfinite 2 (by decide) 1
  have halpha : binaryLogAlpha a Q≤3/16 := by linarith
  intro tau i
  have hr : -9/32≤binaryLogRaw a Q tau i ∧ binaryLogRaw a Q tau i≤9/32 := by
    by_cases ht : tau=0
    · subst tau
      have hh := hreal i
      constructor <;> linarith
    · have hh := hfinite tau ht i
      constructor <;> linarith
  unfold binaryLogWeights
  apply abs_le.mpr
  constructor <;> linarith

end JSP000334
