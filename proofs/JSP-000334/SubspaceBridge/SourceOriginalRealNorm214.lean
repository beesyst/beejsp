import SubspaceBridge.SourceSignedNorm214
import SubspaceBridge.SourceOriginalRationalDual10
import SubspaceBridge.SourceOriginalNormalization213
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceOriginalNorm214
open OriginalDual10 SourceOriginalDual10 SourceOriginalSatz212 SourceOriginalVariable10

theorem real_row_norm214 (r : Fin 10 → ℝ) (u : Fin 10 → Fin 10 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ)))
    (N : ℕ) (hN : N = (Matrix.of u : Matrix (Fin 10) (Fin 10) ℤ).det.natAbs) :
    ‖rowLinear ℝ (Fin 10) r (fun k => (integerLastDual10 u k : ℝ))‖ =
      ‖rowLinear ℝ (Fin 10) r
        (fun k => (N : ℝ)*(lastDual10 (fun j i => (u j i : ℚ)) hu k : ℝ))‖ := by
  have h := cofactor_signed_linear214 (n := 9) ℝ u hu (rowLinear ℝ (Fin 10) r)
  have hs : rowLinear ℝ (Fin 10) r
      (fun k => (N : ℝ)*(lastDual10 (fun j i => (u j i : ℚ)) hu k : ℝ)) =
      (N : ℝ)*rowLinear ℝ (Fin 10) r
        (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : ℝ)) := by
    change (rowLinear ℝ (Fin 10) r) ((N : ℝ) • _) = _
    rw [map_smul,smul_eq_mul]
  have hn : ‖((Matrix.det u : ℤ) : ℝ)‖ = ‖(N : ℝ)‖ := by
    have hm : (Matrix.of u : Matrix (Fin 10) (Fin 10) ℤ) = u := by
      ext i j
      rfl
    rw [hN,hm]
    exact signed_integer_norm214 ℝ (Matrix.det u)
  rw [h,hs,norm_mul,norm_mul,hn]

variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset SourceSelectedSet10.MixedIndex10}

theorem original_real_integer_norm214 (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (i : Fin 10) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 D.u k : ℝ))) i‖ =
      ‖(L⁻¹.transpose *ᵥ (fun k =>
        ((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℝ)*
          (lastDual10 (fun j i => (D.u j i : ℚ))
            (integer_frame_rational_independent10 D.u D.independent) k : ℝ))) i‖ := by
  exact real_row_norm214 (fun k => L⁻¹ k i) D.u
    (integer_frame_rational_independent10 D.u D.independent)
    (originalIndex212 D * (originalLattice212 D).index) (original_index_det212 D)

theorem original_real_norm214 (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (i : Fin 10) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 D.u k : ℝ))) i‖ =
      ‖(L⁻¹.transpose *ᵥ (fun k =>
        ((originalIndex212 D : ℝ)*originalCovolume212 D)*
          (lastDual10 (fun j i => (D.u j i : ℚ))
            (integer_frame_rational_independent10 D.u D.independent) k : ℝ))) i‖ := by
  have h := original_real_integer_norm214 D i
  rw [original_integer_scale212 D] at h
  exact h

theorem original_real_sum_norm214 (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (i : Fin 10) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 D.u k : ℝ))) i‖ =
      ‖∑ k, (((originalIndex212 D : ℝ)*originalCovolume212 D)*
          (lastDual10 (fun j i => (D.u j i : ℚ))
            (integer_frame_rational_independent10 D.u D.independent) k : ℝ))*L⁻¹.transpose i k‖ := by
  rw [original_real_norm214 D i]
  congr 1
  simp only [Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

end CompoundFeasibility.SourceOriginalNorm214
