import SubspaceBridge.OriginalDual10
import SubspaceBridge.ParameterSelection3
import SubspaceBridge.SourceDeformation10
import SubspaceBridge.OriginalSpanTransport10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSampling10

theorem original_tail_parameters10 (U : Set ℝ) (hU : ¬ BddAbove U)
    (eta E rho B : ℝ) (he : 0 < eta) (hE : 1 ≤ E) (hp : 0 < rho)
    (m : ℕ) (hm : 0 < m) :
    ∃ (t : Fin m → U) (r : Fin m → ℕ),
      StrictMono (fun h => (t h).val) ∧
      (∀ h, B < (t h).val ∧ 1 < (t h).val ∧
        1060*E < (t h).val^eta ∧ 10*(eta⁻¹+1) < (t h).val^eta) ∧
      (∀ h, 0 < r h) ∧
      (∀ (h : Fin m) (hh : h.val+1 < m),
        (r ⟨h.val+1,hh⟩ : ℝ) ≤ rho*(r h : ℝ)) ∧
      ∀ h, (r ⟨0,hm⟩ : ℝ)*Real.log (t ⟨0,hm⟩).val ≤
        (r h : ℝ)*Real.log (t h).val ∧
        (r h : ℝ)*Real.log (t h).val ≤
          (1+eta)*((r ⟨0,hm⟩ : ℝ)*Real.log (t ⟨0,hm⟩).val) := by
  let X := max (Real.log (1060*E)/eta) (Real.log (10*(eta⁻¹+1))/eta)
  obtain ⟨Q,hQ,hmono,hsep⟩ := JSP000334.parameter_sparse_Q U hU
    (max B (Real.exp X)) ((1+eta)/rho) m
  have hlog (h) : X < Real.log (Q h) := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos X)
      ((le_max_right _ _).trans_lt (hQ h).2.1)
  have hsep' (h : Fin m) (hh : h.val+1 < m) :
      (1+eta)*Real.log (Q h) ≤ rho*Real.log (Q ⟨h.val+1,hh⟩) := by
    have hs := hsep h hh
    rw [div_mul_eq_mul_div] at hs
    simpa only [mul_comm] using ((div_lt_iff₀ hp).mp hs).le
  obtain ⟨r,hr,hrho,hbal⟩ := JSP000334.parameter_integer_degrees m hm eta rho he hp Q
    (fun h => (hQ h).2.2) hsep'
  refine ⟨fun h => ⟨Q h,(hQ h).1⟩,r,hmono,?_,hr,hrho,?_⟩
  · intro h
    refine ⟨(le_max_left _ _).trans_lt (hQ h).2.1,(hQ h).2.2,?_,?_⟩
    · exact JSP000334.parameter_rpow_threshold _ eta _ (hQ h).2.2 he (by linarith)
        ((le_max_left _ _).trans_lt (hlog h))
    · exact JSP000334.parameter_rpow_threshold _ eta _ (hQ h).2.2 he (by positivity)
        ((le_max_right _ _).trans_lt (hlog h))
  · intro h
    simpa only [mul_assoc] using hbal h

end CompoundFeasibility.SourceSampling10
