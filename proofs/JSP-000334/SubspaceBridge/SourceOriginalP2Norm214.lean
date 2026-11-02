import SubspaceBridge.SourceSignedNorm214
import SubspaceBridge.SourceOriginalRationalDual10
import SubspaceBridge.SourceOriginalNormalization213
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceOriginalNorm214
open OriginalDual10 SourceOriginalDual10 SourceOriginalSatz212 SourceOriginalVariable10

theorem p2_row_norm214 (r : Fin 10 → ℚ_[2]) (u : Fin 10 → Fin 10 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ)))
    (N : ℕ) (hN : N = (Matrix.of u : Matrix (Fin 10) (Fin 10) ℤ).det.natAbs) :
    ‖rowLinear ℚ_[2] (Fin 10) r (fun k => (integerLastDual10 u k : ℚ_[2]))‖ =
      ‖rowLinear ℚ_[2] (Fin 10) r
        (fun k => (N : ℚ_[2])*(lastDual10 (fun j i => (u j i : ℚ)) hu k : ℚ_[2]))‖ := by
  have h := cofactor_signed_linear214 (n := 9) ℚ_[2] u hu (rowLinear ℚ_[2] (Fin 10) r)
  have hs : rowLinear ℚ_[2] (Fin 10) r
      (fun k => (N : ℚ_[2])*(lastDual10 (fun j i => (u j i : ℚ)) hu k : ℚ_[2])) =
      (N : ℚ_[2])*rowLinear ℚ_[2] (Fin 10) r
        (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : ℚ_[2])) := by
    change (rowLinear ℚ_[2] (Fin 10) r) ((N : ℚ_[2]) • _) = _
    rw [map_smul,smul_eq_mul]
  have hn : ‖((Matrix.det u : ℤ) : ℚ_[2])‖ = ‖(N : ℚ_[2])‖ := by
    have hm : (Matrix.of u : Matrix (Fin 10) (Fin 10) ℤ) = u := by
      ext i j
      rfl
    rw [hN,hm]
    exact signed_integer_norm214 ℚ_[2] (Matrix.det u)
  rw [h,hs,norm_mul,norm_mul,hn]

variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset SourceSelectedSet10.MixedIndex10}

theorem original_p2_norm214 (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (i : Fin 10) :
    ‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (integerLastDual10 D.u k : ℚ_[2]))) i‖ =
      ‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k =>
        ((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[2])*
          (lastDual10 (fun j i => (D.u j i : ℚ))
            (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[2]))) i‖ := by
  exact p2_row_norm214 (fun k => (A2.map (algebraMap ℚ ℚ_[2]))⁻¹ k i) D.u
    (integer_frame_rational_independent10 D.u D.independent)
    (originalIndex212 D * (originalLattice212 D).index) (original_index_det212 D)

end CompoundFeasibility.SourceOriginalNorm214
