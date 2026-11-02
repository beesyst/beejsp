import SubspaceBridge.AllPointWeights3
open scoped BigOperators Matrix
namespace JSP000334

theorem allpoint_round_point3 (Q : ℝ) (hQ : 1 < Q)
    (k0 k2 k3 : Fin 3) (c : Fin 3 → Fin 3 → ℝ) (hc : sourceWeightConditions3 c)
    (z : IntegerTriple) (hz : z ∈ qSourceLattice3 k2 k3 Q (c 1) (c 2))
    (hshort : coordinateGauge3 (qSourceCoordinates3 k0 Q (c 0) hQ) (integerTripleReal3 z) ≤
      Q^(-(1 : ℝ)/12)) :
    let d := finiteWeightApprox3 168 c
    d ∈ finiteWeightCandidates3 168 ∧ sourceWeightConditions3 d ∧
    z ∈ qSourceLattice3 k2 k3 Q (d 1) (d 2) ∧
    coordinateGauge3 (qSourceCoordinates3 k0 Q (d 0) hQ) (integerTripleReal3 z) ≤ Q^(-(1 : ℝ)/24) := by
  intro d
  obtain ⟨hd,hreal,hfinite⟩ := finiteWeightApprox3_bounds 168 (by norm_num) c hc
  have hQ0 := lt_trans zero_lt_one hQ
  have hpoint := ((qSourceLattice3_spec k2 k3 Q (c 1) (c 2) hQ
    (fun i => (hc.2.1 1 (by decide) i).2) (fun i => (hc.2.1 2 (by decide) i).2)).1 z).mp hz
  refine ⟨finiteWeightApprox3_mem 168 (by norm_num) c hc,hd,?_,?_⟩
  · apply ((qSourceLattice3_spec k2 k3 Q (d 1) (d 2) hQ
      (fun i => (hd.2.1 1 (by decide) i).2) (fun i => (hd.2.1 2 (by decide) i).2)).1 z).mpr
    exact ⟨fun i => (hpoint.1 i).trans (Real.rpow_le_rpow_of_exponent_le hQ.le (hfinite 1 (by decide) i)),
      fun i => (hpoint.2 i).trans (Real.rpow_le_rpow_of_exponent_le hQ.le (hfinite 2 (by decide) i))⟩
  · apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    change |retainedRealCoordinates3 k0 (integerTripleReal3 z) i / Q^(d 0 i)| ≤ _
    rw [abs_div,abs_of_pos (Real.rpow_pos_of_pos hQ0 _),div_le_iff₀ (Real.rpow_pos_of_pos hQ0 _)]
    have hh := qSource_arch_bound k0 Q (c 0) hQ (integerTripleReal3 z) i
    have hbound := hh.trans (mul_le_mul_of_nonneg_right hshort (Real.rpow_nonneg hQ0.le _))
    have he : Q^(-(1 : ℝ)/12)*Q^(c 0 i) = Q^(c 0 i-(1 : ℝ)/12) := by
      rw [← Real.rpow_add hQ0]; congr 1; ring
    rw [he] at hbound
    have hw : c 0 i-(1 : ℝ)/12 ≤ d 0 i-(1 : ℝ)/24 := by
      have hr := hreal i
      norm_num at hr
      linarith
    have hp := hbound.trans (Real.rpow_le_rpow_of_exponent_le hQ.le hw)
    have he' : Q^(d 0 i-(1 : ℝ)/24) = Q^(-(1 : ℝ)/24)*Q^(d 0 i) := by
      rw [← Real.rpow_add hQ0]; congr 1; ring
    rw [he'] at hp
    exact hp

end JSP000334
