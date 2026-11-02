import SubspaceBridge.OriginalDual10
import SubspaceBridge.SourceDeformation10
import SubspaceBridge.OriginalSpanTransport10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSampling10
open OriginalDeformation10

theorem deformed_gauge_bounds10
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c0 d : Fin 10 → ℝ) (sigma : Equiv.Perm (Fin 10)) (hd : ∀ i, 0 < d i)
    (x : Fin 10 → ℝ) (r : ℝ) :
    coordinateGauge10 (originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd) x ≤ r ↔
      ∀ i, |(L *ᵥ x) i| ≤ r*deformedWidths10 Q c0 d sigma i := by
  rw [coordinateGauge10,pi_norm_le_iff_of_nonempty]
  apply forall_congr'
  intro i
  rw [originalDeformedCoordinates10_apply,Real.norm_eq_abs,abs_div,abs_mul,
    abs_of_pos (hd _),abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _),
    div_le_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _)]
  dsimp [deformedWidths10]
  rw [← mul_div_assoc,le_div_iff₀ (hd _)]
  constructor <;> intro h <;> nlinarith

theorem exists_deformed_frame10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 d : Fin 10 → ℝ)
    (sigma : Equiv.Perm (Fin 10)) (hd : ∀ i, 0 < d i) :
    ∃ w : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun j => integerReal (w j : Fin 10 → ℤ)) ∧
      Monotone (originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd) ∧
      (∀ j, coordinateGauge10 (originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd)
        (integerReal (w j : Fin 10 → ℤ)) =
        originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j) := by
  let b := sourceRealBasis10 A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))
  let e := originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd
  obtain ⟨v,hv,hmem,hpos,hmono,hatt,hbound⟩ := exists_successive_minima10 b e
  have hlift (j : Fin 10) : ∃ z : originalSourceGroup10 A2 A3 Q c2 c3,
      integerReal (z : Fin 10 → ℤ) = v j := by
    have hj := hmem j
    rw [sourceRealBasis10_span] at hj
    obtain ⟨z,hz,he⟩ := hj
    exact ⟨⟨z,hz⟩,he⟩
  choose w hw using hlift
  refine ⟨w,?_,hmono,?_⟩
  · simpa only [hw] using hv
  · intro j
    change coordinateGauge10 e (integerReal (w j : Fin 10 → ℤ)) = successiveRadius10 b e j
    rw [hw j]
    exact hatt j

end CompoundFeasibility.SourceSampling10
