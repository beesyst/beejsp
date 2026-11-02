import SubspaceBridge.RestrictedSelectedBasis5
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedFiniteCoordinates5
open RestrictedGeometry5 RestrictedRelaxed5 RestrictedIntegerCoordinates5 RestrictedRows5
noncomputable section

theorem integerCoordinateMap5_integerReal (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (z : Fin (Module.finrank ℚ P) → ℤ) :
    ((integerCoordinateMap5 P hP z : rationalRealSpan5 P) : Fin 5 → ℝ) =
      integerReal (fun i => ∑ k, z k * baseIntegerVector5 P hP k i) := by
  change ((((baseIntegerBasis5 P hP).equivFun.symm z : baseLattice5 P) : rationalRealSpan5 P) : Fin 5 → ℝ) = _
  rw [Basis.equivFun_symm_apply]
  ext i
  simp only [Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_smul_of_tower,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [← baseIntegerVector5_values P hP]
  simp [integerReal]

theorem selected_local_coordinates5 {d : ℕ} (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c : Fin 5 → ℝ)
    (s : Fin d → Fin 5) (z : Fin (Module.finrank ℚ P) → ℤ)
    (hz : ((integerCoordinateMap5 P hP z : rationalRealSpan5 P) : Fin 5 → ℝ) ∈
      integerRealImage (selectedLocalGroup5 p A Q c s)) :
    ∀ k, padicNorm p (((fun a b => rowCoordinates5 P (baseRationalBasis5 P hP) A (s a) b) *ᵥ
      (fun i => (z i : ℚ))) k) ≤ (p : ℚ)^(-(Nat.ceil (JSP000334.qThreshold p Q (c (s k))) : ℤ)) := by
  obtain ⟨w,hw,hval⟩ := hz
  have hwval : w = fun i => ∑ k, z k * baseIntegerVector5 P hP k i :=
    integerReal_injective (hval.trans (integerCoordinateMap5_integerReal P hP z))
  subst w
  intro k
  have hk := (AddSubgroup.mem_iInf.mp hw) k
  change padicNorm p ((A *ᵥ (fun i => ((∑ a, z a * baseIntegerVector5 P hP a i : ℤ) : ℚ))) (s k)) ≤
    ((p : ℚ)^Nat.ceil (JSP000334.qThreshold p Q (c (s k))))⁻¹ at hk
  have heval : (((fun a b => rowCoordinates5 P (baseRationalBasis5 P hP) A (s a) b) *ᵥ
      (fun i => (z i : ℚ))) k) =
      (A *ᵥ (fun i => ((∑ a, z a * baseIntegerVector5 P hP a i : ℤ) : ℚ))) (s k) := by
    simp only [Matrix.mulVec,dotProduct,rowCoordinates5,baseRationalBasis5,Basis.mk_apply,
      baseRationalVector5,Int.cast_sum,Int.cast_mul]
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
end CompoundFeasibility.RestrictedFiniteCoordinates5
