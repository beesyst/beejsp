import SubspaceBridge.BinaryIntegerSourceBounds2
open scoped BigOperators Classical
namespace JSP000334

theorem binary_log_tail_bounds (C H : ℝ) (hC : 1≤C) (hH : 1<H) (hcut : C^8<H)
    (a : Fin 3 → Fin 2 → ℝ) (ha : ∀ tau i,0<a tau i)
    (hinv : ∀ tau i,(a tau i)⁻¹≤C*H)
    (hreal : ∀ i,1≤a 0 i ∧ a 0 i≤C*H)
    (hfinite : ∀ tau : Fin 3,tau ≠ 0 → ∀ i,a tau i≤1) :
    (∀ i,0≤binaryLogRaw a (H^4) 0 i ∧ binaryLogRaw a (H^4) 0 i≤9/32) ∧
    (∀ tau : Fin 3,tau ≠ 0 → ∀ i,-9/32≤binaryLogRaw a (H^4) tau i ∧ binaryLogRaw a (H^4) tau i≤0) := by
  have hH0 : 0<H := lt_trans zero_lt_one hH
  have hC0 : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hlog : 0<Real.log H := Real.log_pos hH
  have hlog4 : Real.log (H^4)=4*Real.log H := by rw [Real.log_pow];norm_num
  have hlog4p : 0<Real.log (H^4) := by rw [hlog4];positivity
  have hc := Real.log_lt_log (pow_pos hC0 8) hcut
  rw [Real.log_pow] at hc
  norm_num only [Nat.cast_ofNat] at hc
  have hCH : Real.log (C*H)≤(9/32)*Real.log (H^4) := by
    rw [Real.log_mul hC0.ne' hH0.ne',hlog4]
    linarith
  have hlower (tau i) : -9/32≤binaryLogRaw a (H^4) tau i := by
    have hh := Real.log_le_log (inv_pos.mpr (ha tau i)) (hinv tau i)
    rw [Real.log_inv] at hh
    unfold binaryLogRaw
    apply (le_div_iff₀ hlog4p).mpr
    linarith
  constructor
  · intro i
    constructor
    · exact div_nonneg (Real.log_nonneg (hreal i).1) hlog4p.le
    · apply (div_le_iff₀ hlog4p).mpr
      exact (Real.log_le_log (ha 0 i) (hreal i).2).trans hCH
  · intro tau ht i
    refine ⟨hlower tau i,?_⟩
    exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (ha tau i).le (hfinite tau ht i)) hlog4p.le

end JSP000334
