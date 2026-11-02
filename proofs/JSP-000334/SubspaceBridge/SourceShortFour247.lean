import SubspaceBridge.SourceAdjugateRecovery247
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag247
open Exterior54_246

theorem short_four_cutoff247 (kappa delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ Q : ℝ, T < Q → 24/kappa < Q^delta := by
  obtain ⟨T,hT,h⟩ := compound_gap_cutoff42 (24/kappa) (2*delta) (by positivity)
  refine ⟨T,hT,?_⟩
  intro Q hQ
  simpa only [show 2*delta/2 = delta by ring] using h Q hQ

theorem short_four_bound247 (a : Fin 5 → ℝ) (ha : ∀ i, 0 < a i) (hm : Monotone a)
    (nu : Fin 5 → ℝ) (kappa Q delta : ℝ) (hk : 0 < kappa) (hQ : 1 < Q)
    (hcomp : kappa * fourProducts246 a 4 ≤ nu 4)
    (hsource : a 0 < a 1 * Q^(-delta)) (hcut : 24/kappa < Q^delta) :
    ∀ j : Fin 4, 24 * fourProducts246 a j.castSucc < nu 4 := by
  have hp := Real.rpow_pos_of_pos (zero_lt_one.trans hQ) delta
  have he : Q^(-delta)*Q^delta = 1 := by
    rw [← Real.rpow_add (zero_lt_one.trans hQ), neg_add_cancel, Real.rpow_zero]
  have hg := mul_lt_mul_of_pos_right (fourProducts_gap246 a ha Q delta hsource) hp
  rw [mul_assoc,he,mul_one] at hg
  have hc : 24 < Q^delta*kappa := (div_lt_iff₀ hk).mp hcut
  have htop : 24 * fourProducts246 a 3 < nu 4 := by
    calc
      _ < (Q^delta*kappa)*fourProducts246 a 3 :=
        mul_lt_mul_of_pos_right hc (fourProducts_pos246 a ha 3)
      _ = kappa * (fourProducts246 a 3 * Q^delta) := by ring
      _ < kappa * fourProducts246 a 4 := mul_lt_mul_of_pos_left hg hk
      _ ≤ nu 4 := hcomp
  intro j
  exact (mul_le_mul_of_nonneg_left
    (fourProducts_mono246 a ha hm (show j.castSucc ≤ (3 : Fin 5) by change j.val ≤ 3; omega))
    (by norm_num)).trans_lt htop

end CompoundFeasibility.SourceFlag247
