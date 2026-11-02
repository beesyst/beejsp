import SubspaceBridge.SourceBlockGauge245Q
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.BlockReduction245Q
open BlockReduction245P Exterior53_242

theorem source_lower245Q (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ) :
    Q^2*sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 4 ≤
      sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
        (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0) (weightp245P c2) (weightp245P c3) 9 := by
  let nu := sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
    (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0) (weightp245P c2) (weightp245P c3)
  obtain ⟨w,hw,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima10_attaining
    (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
    (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0) (weightp245P c2) (weightp245P c3)
  let pr : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) :=
    LinearMap.pi (fun i => LinearMap.proj (blockIndex245P (Sum.inl i)))
  have hpr : Function.Surjective pr := by
    intro x
    refine ⟨join245Q x 0,?_⟩
    exact first_join245Q x 0
  obtain ⟨a,ha⟩ := projected_frame245P pr hpr (fun j => integerReal (w j : Fin 10 → ℤ)) hw
  have hg (i : Fin 5) : coordinateGauge5 (originalCoordinates5 L hL Q hQ c0)
      (integerReal (first245Q (w (a i) : Fin 10 → ℤ))) ≤ nu 9/(Q^2) := by
    apply (le_div_iff₀ (sq_pos_of_pos (zero_lt_one.trans hQ))).mpr
    have hb := gauge_projection245Q L hL Q hQ c0 (integerReal (w (a i) : Fin 10 → ℤ))
    rw [hatt] at hb
    exact (by simpa only [mul_comm] using hb.trans (hmono (Fin.le_last _)))
  have hsmall : sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 4 ≤ nu 9/(Q^2) := by
    apply (sourceMinima5_radius_set_properties A2 A3 L hL Q hQ c0 c2 c3 4).2.2.2
    refine ⟨fun i => integerReal (first245Q (w (a i) : Fin 10 → ℤ)),ha,?_,hg⟩
    intro i
    exact ⟨first245Q (w (a i) : Fin 10 → ℤ),
      (block_source_group245Q A2 A3 Q c2 c3 _).mp (w (a i)).property,rfl⟩
  simpa only [mul_comm] using (le_div_iff₀ (sq_pos_of_pos (zero_lt_one.trans hQ))).mp hsmall

end CompoundFeasibility.BlockReduction245Q
