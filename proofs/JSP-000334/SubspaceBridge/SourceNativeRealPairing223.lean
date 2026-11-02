import SubspaceBridge.SourceDualPairing222
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceDualAnnihilation222

theorem native_real_pairing223
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : L.det ≠ 0)
    (x z : Fin 10 → ℝ) :
    (∑ i, x i * z i) = ∑ i, (L *ᵥ x) i * (L⁻¹.transpose *ᵥ z) i := by
  change x ⬝ᵥ z = (L *ᵥ x) ⬝ᵥ (L⁻¹.transpose *ᵥ z)
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hL),
      Matrix.one_mulVec]

theorem real_pairing_bound222
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (d : ℝ) (hd : 0 < d) (A : Fin 10 → ℝ) (hA : ∀ i, 0 < A i)
    (x z : Fin 10 → ℝ) (s r : ℝ) (hs : 0 ≤ s)
    (hx : ∀ i, |(L *ᵥ x) i| ≤ s * A i)
    (hz : dualGauge222 L hL d hd A hA z ≤ r) :
    |∑ i, x i * z i| ≤ 10 * r * d * s := by
  have hr : 0 ≤ r :=
    (show 0 ≤ dualGauge222 L hL d hd A hA z from norm_nonneg _).trans hz
  have hb := (dualGauge_bounds222 L hL d hd A hA z r).mp hz
  have hp := native_real_pairing223 L
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hL)) x z
  calc
    _ = |∑ i, (L *ᵥ x) i * (L⁻¹.transpose *ᵥ z) i| := congrArg abs hp
    _ ≤ 10 * r * d * s :=
      sum_pairing222 (L *ᵥ x) (L⁻¹.transpose *ᵥ z) A d s r hA hd hs hr hx hb

end CompoundFeasibility.SourceDualAnnihilation222
