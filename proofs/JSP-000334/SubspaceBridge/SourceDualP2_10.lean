import SubspaceBridge.SourceDualRows10
open scoped Matrix
namespace CompoundFeasibility.SourceOriginalDual10
open OriginalDual10
noncomputable section

theorem original_p2_row_nonzero10
    (r : Fin 10 → ℚ_[2]) (u : Fin 10 → Fin 10 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) :
    rowLinear ℚ_[2] (Fin 10) r (fun k => (integerLastDual10 u k : ℚ_[2])) ≠ 0 ↔
      rowLinear ℚ_[2] (Fin 10) r (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : ℚ_[2])) ≠ 0 := by
  exact original_cofactor_linear_nonzero (n := 9) ℚ_[2] u hu (rowLinear ℚ_[2] (Fin 10) r)

theorem original_p2_nonzero10 (A : Matrix (Fin 10) (Fin 10) ℚ)
    (u : Fin 10 → Fin 10 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) (i : Fin 10) :
    ((A.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (integerLastDual10 u k : ℚ_[2]))) i ≠ 0 ↔
      ((A.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : ℚ_[2]))) i ≠ 0 := by
  exact original_p2_row_nonzero10 (fun k => (A.map (algebraMap ℚ ℚ_[2]))⁻¹ k i) u hu

end
end CompoundFeasibility.SourceOriginalDual10
