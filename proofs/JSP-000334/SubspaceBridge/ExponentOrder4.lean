import SubspaceBridge.NonrothOppositeGrowth4
open Filter
namespace CompoundFeasibility.ExponentOrder4

theorem unbounded_rpow_gt (U : Set ℝ) (hU : ¬ BddAbove U) (beta : ℝ)
    (hbeta : 0 < beta) (M : ℝ) : ∃ Q ∈ U, M < Q^beta := by
  obtain ⟨B,hB⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hbeta).eventually (eventually_gt_atTop M))
  obtain ⟨Q,hQU,hBQ⟩ := not_bddAbove_iff.mp hU B
  exact ⟨Q,hQU,hB Q hBQ.le⟩

theorem power_gap_bound (Q c K eta alpha : ℝ) (hQ : 0 < Q) (hc : 0 < c)
    (h : c*Q^eta ≤ K*Q^alpha) : Q^(eta-alpha) ≤ K/c := by
  apply (le_div_iff₀ hc).mpr
  rw [Real.rpow_sub hQ,div_mul_eq_mul_div]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hQ alpha)).mpr
  nlinarith

theorem exponent_le_of_unbounded_power_bound (U : Set ℝ) (hU : ¬ BddAbove U)
    (hQ : ∀ Q ∈ U, 1 < Q) (c K eta alpha : ℝ) (hc : 0 < c) (_hK : 0 < K)
    (hbound : ∀ Q ∈ U, c*Q^eta ≤ K*Q^alpha) : eta ≤ alpha := by
  by_contra hn
  have hbeta : 0 < eta-alpha := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨Q,hQU,hbig⟩ := unbounded_rpow_gt U hU (eta-alpha) hbeta (K/c)
  exact (not_lt_of_ge (power_gap_bound Q c K eta alpha (zero_lt_one.trans (hQ Q hQU)) hc
    (hbound Q hQU))) hbig

end CompoundFeasibility.ExponentOrder4
