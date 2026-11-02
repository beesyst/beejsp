import SubspaceBridge.SourceDeformation10
import SubspaceBridge.SourceFixedLine235
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceRatioLine236
open OriginalDeformation10 SourceOriginalVariable10 SourceSatz51Entry218

theorem powered_gt_one236 (Q : ℝ) (hQ : 1 < Q) : 1 < Q^5 :=
  one_lt_pow₀ hQ (by decide)

theorem scaled_exponents236 (c : Fin 10 → ℝ) (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 0) :
    ∀ i, -1 ≤ c i/5 ∧ c i/5 ≤ 0 := by
  intro i
  constructor <;> linarith [(hc i).1,(hc i).2]

theorem powered_lattice236 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (Q : ℝ) (c2 c3 : Fin 10 → ℝ) :
    originalSourceGroup10 A2 A3 (Q^5) (fun i => c2 i/5) (fun i => c3 i/5) =
      originalSourceGroup10 A2 A3 Q c2 c3 := by
  unfold originalSourceGroup10
  simp_rw [rescaled_threshold10]

theorem normalized_coordinates236 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 d : Fin 10 → ℝ) (sigma : Equiv.Perm (Fin 10))
    (hd : ∀ i, 0 < d i) :
    originalCoordinates10 L hL (Q^5) (powered_gt_one236 Q hQ)
      (fun i => normalizedWidth10 (Q^5) (deformedWidths10 Q c0 d sigma i)) =
        originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd := by
  ext x i
  change (L *ᵥ x) i/(Q^5)^normalizedWidth10 (Q^5) (deformedWidths10 Q c0 d sigma i) = _
  rw [normalized_width_exact10 _ _ (powered_gt_one236 Q hQ)
    (deformedWidths10_pos Q (zero_lt_one.trans hQ) c0 d hd sigma i),
    originalDeformedCoordinates10_apply]
  unfold deformedWidths10
  field_simp <;> ring

theorem normalized_gauge236 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 d : Fin 10 → ℝ) (sigma : Equiv.Perm (Fin 10))
    (hd : ∀ i, 0 < d i) (x : Fin 10 → ℝ) :
    coordinateGauge10 (originalCoordinates10 L hL (Q^5) (powered_gt_one236 Q hQ)
      (fun i => normalizedWidth10 (Q^5) (deformedWidths10 Q c0 d sigma i))) x =
    coordinateGauge10 (originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd) x := by
  rw [normalized_coordinates236 L hL Q hQ c0 d sigma hd]

theorem normalized_body236 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 d : Fin 10 → ℝ) (sigma : Equiv.Perm (Fin 10))
    (hd : ∀ i, 0 < d i) :
    parallelepipedBody10 (originalCoordinates10 L hL (Q^5) (powered_gt_one236 Q hQ)
      (fun i => normalizedWidth10 (Q^5) (deformedWidths10 Q c0 d sigma i))) =
    parallelepipedBody10 (originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd) := by
  rw [normalized_coordinates236 L hL Q hQ c0 d sigma hd]

theorem normalized_minima236 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 d : Fin 10 → ℝ) (sigma : Equiv.Perm (Fin 10)) (hd : ∀ i, 0 < d i) (j : Fin 10) :
    sourceMinima10 A2 A3 L hL (Q^5) (powered_gt_one236 Q hQ)
      (fun i => normalizedWidth10 (Q^5) (deformedWidths10 Q c0 d sigma i))
      (fun i => c2 i/5) (fun i => c3 i/5) j =
      originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j := by
  rw [sourceMinima10_eq_radius,normalized_coordinates236 L hL Q hQ c0 d sigma hd]
  unfold originalDeformedMinima10
  simp_rw [rescaled_threshold10]

theorem powered_balance236 (Q : ℝ) (hQ : 1 < Q) (A c2 c3 : Fin 10 → ℝ)
    (hb : (∏ i, A i)*(∏ i, Q^(c2 i+c3 i)) = 1) :
    (∏ i, A i*(Q^5)^(c2 i/5)*(Q^5)^(c3 i/5)) = 1 := by
  simp_rw [rescaled_power10 Q _ (zero_lt_one.trans hQ)]
  simpa only [Real.rpow_add (zero_lt_one.trans hQ),Finset.prod_mul_distrib,mul_assoc] using hb

theorem exists_deformed_frame236
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 d : Fin 10 → ℝ)
    (sigma : Equiv.Perm (Fin 10)) (hd : ∀ i, 0 < d i) :
    ∃ w : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun j => integerReal (w j : Fin 10 → ℤ)) ∧
      (∀ j, 0 < originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j) ∧
      Monotone (originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd) ∧
      ∀ j, coordinateGauge10 (originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd)
        (integerReal (w j : Fin 10 → ℤ)) =
          originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j := by
  let b := sourceRealBasis10 A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))
  let e := originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd
  obtain ⟨v,hv,hmem,hpos,hmono,hatt⟩ := exists_successive_minima10 b e
  have hlift (j : Fin 10) : ∃ z : originalSourceGroup10 A2 A3 Q c2 c3,
      integerReal (z : Fin 10 → ℤ) = v j := by
    have hj := hmem j
    rw [sourceRealBasis10_span] at hj
    obtain ⟨z,hz,he⟩ := hj
    exact ⟨⟨z,hz⟩,he⟩
  choose w hw using hlift
  refine ⟨w,?_,hpos,hmono,?_⟩
  · simpa only [hw] using hv
  · intro j
    change coordinateGauge10 e (integerReal (w j : Fin 10 → ℤ)) = successiveRadius10 b e j
    rw [hw j]
    exact hatt.1 j

end CompoundFeasibility.SourceRatioLine236
