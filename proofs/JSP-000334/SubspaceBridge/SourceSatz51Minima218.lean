import SubspaceBridge.SourceSatz51Lattice218
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSatz51Entry218
open SourceOriginalVariable10

theorem source_minima_scale218
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (q Q : ℝ) (hq : 1 < q) (hQ : 1 < Q) (c0 c2 c3 d0 d2 d3 : Fin 10 → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hG : originalSourceGroup10 A2 A3 Q d2 d3 = originalSourceGroup10 A2 A3 q c2 c3)
    (hGauge : ∀ x, coordinateGauge10 (originalCoordinates10 L hL Q hQ d0) x =
      coordinateGauge10 (originalCoordinates10 L hL q hq c0) x/t) (j : Fin 10) :
    sourceMinima10 A2 A3 L hL Q hQ d0 d2 d3 j =
      sourceMinima10 A2 A3 L hL q hq c0 c2 c3 j/t := by
  have ho := (sourceMinima10_radius_set_properties A2 A3 L hL q hq c0 c2 c3 j).2.2
  have hn := (sourceMinima10_radius_set_properties A2 A3 L hL Q hQ d0 d2 d3 j).2.2
  apply le_antisymm
  · apply hn.2
    obtain ⟨u,hu,hm,hg⟩ := ho.1
    refine ⟨u,hu,?_,?_⟩
    · intro i
      rw [hG]
      exact hm i
    · intro i
      rw [hGauge]
      exact div_le_div_of_nonneg_right (hg i) ht.le
  · apply (div_le_iff₀ ht).mpr
    apply ho.2
    obtain ⟨u,hu,hm,hg⟩ := hn.1
    refine ⟨u,hu,?_,?_⟩
    · intro i
      rw [← hG]
      exact hm i
    · intro i
      apply (div_le_iff₀ ht).mp
      rw [← hGauge]
      exact hg i

theorem source_gauge_width_scale218
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (q Q : ℝ) (hq : 1 < q) (hQ : 1 < Q) (A : Fin 10 → ℝ) (hA : ∀ i, 0 < A i)
    (t : ℝ) (ht : 0 < t) (x : Fin 10 → ℝ) :
    coordinateGauge10 (originalCoordinates10 L hL Q hQ (fun i => normalizedWidth10 Q (t*A i))) x =
      coordinateGauge10 (originalCoordinates10 L hL q hq (fun i => normalizedWidth10 q (A i))) x/t := by
  have he : originalCoordinates10 L hL Q hQ (fun i => normalizedWidth10 Q (t*A i)) x =
      t⁻¹ • originalCoordinates10 L hL q hq (fun i => normalizedWidth10 q (A i)) x := by
    ext i
    change (L *ᵥ x) i / Q^(normalizedWidth10 Q (t*A i)) =
      t⁻¹*((L *ᵥ x) i / q^(normalizedWidth10 q (A i)))
    rw [normalized_width_exact10 Q _ hQ (mul_pos ht (hA i)),normalized_width_exact10 q _ hq (hA i)]
    field_simp
  change ‖originalCoordinates10 L hL Q hQ (fun i => normalizedWidth10 Q (t*A i)) x‖ = _
  rw [he,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos ht]
  simp only [coordinateGauge10,div_eq_mul_inv,mul_comm]

end CompoundFeasibility.SourceSatz51Entry218
