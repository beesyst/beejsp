import SubspaceBridge.OriginalSource5
open scoped BigOperators Matrix Topology
open MeasureTheory
namespace CompoundFeasibility
noncomputable section

theorem q_width_product_le_prime_powers5 (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 5 → ℝ) (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    (∏ i, Q ^ c₀ i) ≤
      (2 : ℝ) ^ (∑ i, Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))) *
      3 ^ (∑ i, Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))) := by
  have hQpos : 0 < Q := lt_trans zero_lt_one hQ
  have hi (p : ℕ) (hp : 1 < p) (c : ℝ) :
      Q ^ (-c) ≤ (p : ℝ) ^ Nat.ceil (JSP000334.qThreshold p Q c) := by
    rw [← JSP000334.qThreshold_rpow p hp Q c hQ, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.le) (Nat.le_ceil _)
  have heq : (∏ i, Q ^ (-c₂ i) * Q ^ (-c₃ i)) = ∏ i, Q ^ c₀ i := by
    simp_rw [← Real.rpow_add hQpos]
    rw [← Real.rpow_sum_of_pos hQpos _ Finset.univ, ← Real.rpow_sum_of_pos hQpos _ Finset.univ]
    congr 1
    simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib]
    simp only [Finset.sum_add_distrib] at hb
    linarith
  rw [← heq, ← Finset.prod_pow_eq_pow_sum Finset.univ _ (2 : ℝ),
    ← Finset.prod_pow_eq_pow_sum Finset.univ _ (3 : ℝ), ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun i _ => mul_nonneg (Real.rpow_pos_of_pos hQpos _).le (Real.rpow_pos_of_pos hQpos _).le)
    (fun i _ => mul_le_mul (hi 2 (by decide) _) (hi 3 (by decide) _)
      (Real.rpow_pos_of_pos hQpos _).le (by positivity))


def sourceLocalDetFactor5 (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) : ℝ :=
  (padicNorm 2 A₂.det : ℝ) * (padicNorm 3 A₃.det : ℝ)

theorem sourceLocalDetFactor5_pos (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) : 0 < sourceLocalDetFactor5 A₂ A₃ := by
  have hd₂ := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp h₂)
  have hd₃ := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp h₃)
  exact mul_pos
    (Rat.cast_pos.mpr ((IsAbsoluteValue.toAbsoluteValue (padicNorm 2)).pos_iff.mpr hd₂))
    (Rat.cast_pos.mpr ((IsAbsoluteValue.toAbsoluteValue (padicNorm 3)).pos_iff.mpr hd₃))

theorem sourceLattice5_covolume_width_lower (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) :
    sourceLocalDetFactor5 A₂ A₃ * (∏ i, Q^c₀ i) ≤
      ZLattice.covolume (integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) := by
  let e₂ := fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))
  let e₃ := fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))
  obtain ⟨c⟩ := sourceLattice5_has_basis A₂ A₃ e₂ e₃
  have hlow := integerRealImage_padic_covolume_lower (sourceLattice5 A₂ A₃ e₂ e₃) c A₂ A₃ e₂ e₃
    (fun x hx => (lattice5_spec 2 A₂ e₂ x).mp hx.1)
    (fun x hx => (lattice5_spec 3 A₃ e₃ x).mp hx.2)
  have hf : 0 ≤ sourceLocalDetFactor5 A₂ A₃ := mul_nonneg
    (Rat.cast_nonneg.mpr (padicNorm.nonneg _)) (Rat.cast_nonneg.mpr (padicNorm.nonneg _))
  exact (mul_le_mul_of_nonneg_left (q_width_product_le_prime_powers5 Q hQ c₀ c₂ c₃ hb) hf).trans
    (by simpa only [sourceLocalDetFactor5,mul_assoc] using hlow)

theorem originalBody5_compact_convex (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) :
    IsCompact (originalBody5 L Q c₀) ∧ Convex ℝ (originalBody5 L Q c₀) := by
  let e := originalCoordinates5 L hL Q hQ c₀
  have he : originalBody5 L Q c₀ = e ⁻¹' Metric.closedBall (0 : Fin 5 → ℝ) 1 := by
    ext x
    rw [originalBody5_mem_iff L hL Q hQ c₀ x]
    simp only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,e]
  rw [he]
  exact ⟨e.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _),
    (convex_closedBall (0 : Fin 5 → ℝ) 1).linear_preimage e.toLinearMap⟩

theorem originalBody5_symmetric (L : Matrix (Fin 5) (Fin 5) ℝ) (Q : ℝ) (c₀ : Fin 5 → ℝ) :
    ∀ x ∈ originalBody5 L Q c₀, -x ∈ originalBody5 L Q c₀ := by
  intro x hx i
  simpa only [Matrix.mulVec_neg,Pi.neg_apply,abs_neg] using hx i

theorem originalBody5_zero_interior (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) : 0 ∈ interior (originalBody5 L Q c₀) := by
  let e := originalCoordinates5 L hL Q hQ c₀
  have ho : IsOpen (e ⁻¹' Metric.ball (0 : Fin 5 → ℝ) 1) :=
    Metric.isOpen_ball.preimage e.toContinuousLinearEquiv.continuous
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (ho.mem_nhds (by simp))
  intro x hx
  rw [originalBody5_mem_iff L hL Q hQ c₀ x]
  exact (by simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hx : ‖e x‖ < 1).le

theorem originalBody5_volume_pos (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) : 0 < volume.real (originalBody5 L Q c₀) := by
  rw [originalBody5_volume L hL Q hQ]
  have hd : L.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hL)
  exact div_pos (mul_pos (by norm_num) (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by linarith) _))) (abs_pos.mpr hd)

end
end CompoundFeasibility
