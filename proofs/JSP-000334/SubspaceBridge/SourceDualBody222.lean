import SubspaceBridge.SourceDualLattice219
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceDualAnnihilation222
open SourceDualGeometry219

def dualBody222 (L : Matrix (Fin 10) (Fin 10) ℝ) (d : ℝ) (A : Fin 10 → ℝ) :
    Set (Fin 10 → ℝ) := {z | ∀ i, |(L⁻¹.transpose *ᵥ z) i| ≤ d/A i}

theorem inverse_transpose_unit222 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) :
    IsUnit L⁻¹.transpose := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_transpose,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
  exact IsUnit.inv ((Matrix.isUnit_iff_isUnit_det _).mp hL)

def dualCoordinates222 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (d : ℝ) (hd : 0 < d) (A : Fin 10 → ℝ) (hA : ∀ i, 0 < A i) :
    (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ) :=
  weightedCoordinates10 (originalFormEquiv10 L⁻¹.transpose (inverse_transpose_unit222 L hL))
    (fun i => d/A i) (fun i => div_pos hd (hA i))

def dualGauge222 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (d : ℝ) (hd : 0 < d) (A : Fin 10 → ℝ) (hA : ∀ i, 0 < A i)
    (z : Fin 10 → ℝ) : ℝ := coordinateGauge10 (dualCoordinates222 L hL d hd A hA) z

theorem dualGauge_bounds222 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (d : ℝ) (hd : 0 < d) (A : Fin 10 → ℝ) (hA : ∀ i, 0 < A i)
    (z : Fin 10 → ℝ) (r : ℝ) :
    dualGauge222 L hL d hd A hA z ≤ r ↔
      ∀ i, |(L⁻¹.transpose *ᵥ z) i| ≤ r*(d/A i) := by
  rw [dualGauge222,coordinateGauge10,pi_norm_le_iff_of_nonempty]
  apply forall_congr'
  intro i
  change ‖(L⁻¹.transpose *ᵥ z) i / (d/A i)‖ ≤ r ↔ _
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (div_pos hd (hA i)),div_le_iff₀ (div_pos hd (hA i))]

theorem dualBody_gauge222 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (d : ℝ) (hd : 0 < d) (A : Fin 10 → ℝ) (hA : ∀ i, 0 < A i)
    (z : Fin 10 → ℝ) : z ∈ dualBody222 L d A ↔ dualGauge222 L hL d hd A hA z ≤ 1 := by
  rw [dualGauge_bounds222]
  simp only [dualBody222,Set.mem_setOf_eq,one_mul]

def ratReal222 (z : Fin 10 → ℚ) : Fin 10 → ℝ := fun i => (z i : ℝ)

theorem pairing_cast222 (z : Fin 10 → ℚ) (x : Fin 10 → ℤ) :
    (∑ i, integerReal x i*ratReal222 z i) = (pairing219 z x : ℝ) := by
  change (∑ i, (x i : ℝ)*(z i : ℝ)) = _
  simp only [pairing219,Rat.cast_sum,Rat.cast_mul,Rat.cast_intCast]

end CompoundFeasibility.SourceDualAnnihilation222
