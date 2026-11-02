import SubspaceBridge.SourceOriginalAuxiliaryFamily10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSampling10

theorem rescaled_original_group10 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (q : ℝ) (c2 c3 : Fin 10 → ℝ) :
    originalSourceGroup10 A2 A3 (q^5) (fun i => c2 i/5) (fun i => c3 i/5) =
      originalSourceGroup10 A2 A3 q c2 c3 := by
  have he (p : ℕ) (c : ℝ) : JSP000334.qThreshold p (q^5) (c/5) =
      JSP000334.qThreshold p q c := by
    simp only [JSP000334.qThreshold,Real.log_pow]
    ring
  simp only [originalSourceGroup10,he]

theorem nine_short_vectors_absolute10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ)
    (epsilon : ℝ) (he : 0 < epsilon) (w : Fin 10 → Fin 10 → ℤ)
    (hw : LinearIndependent ℝ (fun j => integerReal (w j)))
    (hmem : ∀ j, w j ∈ originalSourceGroup10 A2 A3 Q c2 c3)
    (hbound : ∀ (j : Fin 9) i, ‖(L *ᵥ integerReal (w j.castSucc)) i‖ ≤ Q^(c0 i-epsilon)) :
    sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 8 < Q^(-(epsilon/2)) := by
  have hsmall : sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 8 ≤ Q^(-epsilon) := by
    apply (sourceMinima10_radius_set_properties A2 A3 L hL Q hQ c0 c2 c3 8).2.2.2
    refine ⟨fun j : Fin 9 => integerReal (w j.castSucc),
      hw.comp Fin.castSucc (Fin.castSucc_injective 9),?_,?_⟩
    · intro j
      exact ⟨w j.castSucc,hmem j.castSucc,rfl⟩
    · intro j
      apply (originalCoordinates10_bounds L hL Q hQ c0 _ _).mpr
      intro i
      rw [← Real.rpow_add (zero_lt_one.trans hQ)]
      have hh := hbound j i
      rw [Real.norm_eq_abs] at hh
      convert hh using 1 <;> congr 1 <;> ring
  exact hsmall.trans_lt ((Real.rpow_lt_rpow_left_iff hQ).mpr (by linarith))

theorem original_sample_absolute10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    (hL : IsUnit L) {c2 c3 : Fin 10 → ℝ} {V : Set ℝ} {v : V → Fin 10 → Fin 10 → ℤ}
    {c : Fin 3 → Fin 10 → ℝ} {epsilon eta D E B rho : ℝ} {m : ℕ} {hm : 0 < m}
    (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
    (he : 0 < epsilon) (hc : ∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5) (h : Fin m) :
    sourceMinima10 A2 A3 L hL ((S.data.t h).val^5) (S.conditions.large h).2.2.1
      (c 0) (c 1) (c 2) 8 < ((S.data.t h).val^5)^(-(epsilon/2)) := by
  apply nine_short_vectors_absolute10 A2 A3 L hL _ (S.conditions.large h).2.2.1
    (c 0) (c 1) (c 2) epsilon he (S.data.w h) (S.conditions.independent h)
    _ (S.conditions.real_bound h)
  intro j
  have h2 : c 1 = fun i => c2 i/5 := funext (fun i => (hc i).1)
  have h3 : c 2 = fun i => c3 i/5 := funext (fun i => (hc i).2)
  rw [h2,h3,rescaled_original_group10]
  exact S.conditions.member h j

end CompoundFeasibility.SourceSampling10
