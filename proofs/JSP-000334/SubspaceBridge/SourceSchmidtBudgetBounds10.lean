import SubspaceBridge.SourceSchmidtBudgetNumeric10
import SubspaceBridge.SourceSampleSchmidtParameters10
import SubspaceBridge.ParameterSelection3
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSchmidtBudget10
open SourceSampling10 SchmidtPolynomial10

theorem height_denominator_power_lower10 (Q alpha H b : ℝ) (hQ : 0 < Q)
    (hl : Q^alpha ≤ H) (hroot : H^(1/9 : ℝ) ≤ b) : Q^(alpha/9) ≤ b := by
  calc
    Q^(alpha/9) = (Q^alpha)^(1/9 : ℝ) := by rw [← Real.rpow_mul hQ.le]; congr 1; ring
    _ ≤ H^(1/9 : ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hQ.le _) hl (by norm_num)
    _ ≤ b := hroot

theorem original_sample_power_cutoff10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {c2 c3 : Fin 10 → ℝ} {V : Set ℝ} {v : V → Fin 10 → Fin 10 → ℤ}
    {c : Fin 3 → Fin 10 → ℝ} {epsilon eta D E B rho : ℝ} {m : ℕ} {hm : 0 < m}
    (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
    (T : ℝ) (hB : T ≤ B) (h : Fin m) : T < (S.data.t h).val^5 := by
  exact (hB.trans_lt (S.conditions.large h).1).trans_le
    (le_self_pow₀ (S.conditions.large h).2.1.le (by norm_num))

theorem original_sample_degree_sum10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {c2 c3 : Fin 10 → ℝ} {V : Set ℝ} {v : V → Fin 10 → Fin 10 → ℤ}
    {c : Fin 3 → Fin 10 → ℝ} {epsilon eta D E B rho : ℝ} {m : ℕ} {hm : 0 < m}
    (he : 0 < eta)
    (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm) :
    ((∑ h, S.data.r h : ℕ) : ℝ) ≤ (m : ℝ)*(1+eta)*(S.data.r ⟨0,hm⟩ : ℝ) := by
  have hmono : Monotone (fun h => (S.data.t h).val^5) := by
    intro h k hhk
    exact pow_le_pow_left₀ (zero_lt_one.trans (S.conditions.large h).2.1).le
      (S.conditions.increasing.monotone hhk) 5
  exact JSP000334.parameter_degree_sum m hm eta he (fun h => (S.data.t h).val^5)
    (fun h => (S.conditions.large h).2.2.1) hmono S.data.r
    (fun h => by simpa only [mul_assoc] using (S.conditions.logarithmic_balance h).2)

theorem original_sample_reduced_height10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {c2 c3 : Fin 10 → ℝ} {V : Set ℝ} {v : V → Fin 10 → Fin 10 → ℤ}
    {c : Fin 3 → Fin 10 → ℝ} {epsilon eta D E B rho : ℝ} {m : ℕ} {hm : 0 < m}
    (he : 0 < eta) (hD : 1 ≤ D)
    (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
    (G : MvPolynomial (Fin m) ℤ) (hGH : JSP000334.rothIntegerHeight G ≤ height10 S.data.P) :
    (JSP000334.rothIntegerHeight G : ℝ) ≤ D^((m : ℝ)*(1+eta)*(S.data.r ⟨0,hm⟩ : ℝ)) := by
  have hh : (JSP000334.rothIntegerHeight G : ℝ) ≤ (height10 S.data.P : ℝ) := by exact_mod_cast hGH
  calc
    _ ≤ D^(∑ h, S.data.r h) := hh.trans S.conditions.height
    _ = D^((∑ h, S.data.r h : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hD (original_sample_degree_sum10 he S)

end CompoundFeasibility.SourceSchmidtBudget10
