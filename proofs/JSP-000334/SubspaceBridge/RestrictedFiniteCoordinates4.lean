import SubspaceBridge.RestrictedSelectedBasis4
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedFiniteCoordinates4
open RestrictedGeometry4 RestrictedRelaxed4 RestrictedIntegerCoordinates4 RestrictedRows4
noncomputable section

theorem integerCoordinateMap4_integerReal (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (z : Fin (Module.finrank ℚ P) → ℤ) :
    ((integerCoordinateMap4 P hP z : rationalRealSpan4 P) : Fin 4 → ℝ) =
      integerReal (fun i => ∑ k, z k * baseIntegerVector4 P hP k i) := by
  change ((((baseIntegerBasis4 P hP).equivFun.symm z : baseLattice4 P) : rationalRealSpan4 P) : Fin 4 → ℝ) = _
  rw [Basis.equivFun_symm_apply]
  ext i
  simp only [Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_smul_of_tower,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [← baseIntegerVector4_values P hP]
  simp [integerReal]

theorem selected_local_coordinates4 {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c : Fin 4 → ℝ)
    (s : Fin d → Fin 4) (z : Fin (Module.finrank ℚ P) → ℤ)
    (hz : ((integerCoordinateMap4 P hP z : rationalRealSpan4 P) : Fin 4 → ℝ) ∈
      integerRealImage (selectedLocalGroup4 p A Q c s)) :
    ∀ k, padicNorm p (((fun a b => rowCoordinates4 P (baseRationalBasis4 P hP) A (s a) b) *ᵥ
      (fun i => (z i : ℚ))) k) ≤ (p : ℚ)^(-(Nat.ceil (JSP000334.qThreshold p Q (c (s k))) : ℤ)) := by
  obtain ⟨w,hw,hval⟩ := hz
  have hwval : w = fun i => ∑ k, z k * baseIntegerVector4 P hP k i :=
    integerReal_injective (hval.trans (integerCoordinateMap4_integerReal P hP z))
  subst w
  intro k
  have hk := (AddSubgroup.mem_iInf.mp hw) k
  change padicNorm p ((A *ᵥ (fun i => ((∑ a, z a * baseIntegerVector4 P hP a i : ℤ) : ℚ))) (s k)) ≤
    ((p : ℚ)^Nat.ceil (JSP000334.qThreshold p Q (c (s k))))⁻¹ at hk
  have heval : (((fun a b => rowCoordinates4 P (baseRationalBasis4 P hP) A (s a) b) *ᵥ
      (fun i => (z i : ℚ))) k) =
      (A *ᵥ (fun i => ((∑ a, z a * baseIntegerVector4 P hP a i : ℤ) : ℚ))) (s k) := by
    simp only [Matrix.mulVec,dotProduct,rowCoordinates4,baseRationalBasis4,Basis.mk_apply,
      baseRationalVector4,Int.cast_sum,Int.cast_mul]
    simp_rw [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [heval]
  simpa only [zpow_neg,zpow_natCast] using hk

end
end CompoundFeasibility.RestrictedFiniteCoordinates4
