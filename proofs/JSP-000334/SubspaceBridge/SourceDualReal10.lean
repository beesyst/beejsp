import SubspaceBridge.SourceDualRows10
open scoped Matrix
namespace CompoundFeasibility.SourceOriginalDual10
open OriginalDual10
noncomputable section

theorem original_real_row_nonzero10
    (r : Fin 10 → ℝ) (u : Fin 10 → Fin 10 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) :
    rowLinear ℝ (Fin 10) r (fun k => (integerLastDual10 u k : ℝ)) ≠ 0 ↔
      rowLinear ℝ (Fin 10) r (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : ℝ)) ≠ 0 := by
  exact original_cofactor_linear_nonzero (n := 9) ℝ u hu (rowLinear ℝ (Fin 10) r)

theorem original_real_nonzero10 (L : Matrix (Fin 10) (Fin 10) ℝ)
    (u : Fin 10 → Fin 10 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) (i : Fin 10) :
    (L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 u k : ℝ))) i ≠ 0 ↔
      (L⁻¹.transpose *ᵥ (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : ℝ))) i ≠ 0 := by
  exact original_real_row_nonzero10 (fun k => L⁻¹ k i) u hu


end
end CompoundFeasibility.SourceOriginalDual10
