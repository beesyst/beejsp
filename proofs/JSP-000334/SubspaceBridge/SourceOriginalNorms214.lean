import SubspaceBridge.SourceOriginalRealNorm214
import SubspaceBridge.SourceOriginalP2Norm214
import SubspaceBridge.SourceOriginalP3Norm214
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceOriginalNorm214
open OriginalDual10 SourceOriginalDual10 SourceOriginalSatz212 SourceOriginalVariable10
variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset SourceSelectedSet10.MixedIndex10}

theorem original_norm_transport214 (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    0 < originalIndex212 D ∧ 0 < originalCovolume212 D ∧
      originalIndex212 D * (originalLattice212 D).index = ((Matrix.of D.u : Matrix (Fin 10) (Fin 10) ℤ).det).natAbs ∧
      |((Matrix.of D.u : Matrix (Fin 10) (Fin 10) ℤ).det : ℝ)| = (originalIndex212 D : ℝ)*originalCovolume212 D ∧
      originalCovolume212 D = ((originalLattice212 D).index : ℝ) ∧
      ((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℝ) =
        (originalIndex212 D : ℝ)*originalCovolume212 D ∧
      ∀ i : Fin 10,
      ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 D.u k : ℝ))) i‖ =
      ‖(L⁻¹.transpose *ᵥ (fun k =>
        ((originalIndex212 D : ℝ)*originalCovolume212 D)*
          (lastDual10 (fun j i => (D.u j i : ℚ))
            (integer_frame_rational_independent10 D.u D.independent) k : ℝ))) i‖ ∧
      ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 D.u k : ℝ))) i‖ =
      ‖∑ k, (((originalIndex212 D : ℝ)*originalCovolume212 D)*
          (lastDual10 (fun j i => (D.u j i : ℚ))
            (integer_frame_rational_independent10 D.u D.independent) k : ℝ))*L⁻¹.transpose i k‖ ∧
      ‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (integerLastDual10 D.u k : ℚ_[2]))) i‖ =
      ‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k =>
        ((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[2])*
          (lastDual10 (fun j i => (D.u j i : ℚ))
            (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[2]))) i‖ ∧
      ‖((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k => (integerLastDual10 D.u k : ℚ_[3]))) i‖ =
      ‖((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k =>
        ((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[3])*
          (lastDual10 (fun j i => (D.u j i : ℚ))
            (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[3]))) i‖ := by
  obtain ⟨hJ,hd,hN,hdet,hidx,hscale⟩ := original_index_normalization212 D
  refine ⟨hJ,hd,hN,hdet,hidx,hscale,?_⟩
  intro i
  exact ⟨original_real_norm214 D i,original_real_sum_norm214 D i,
    original_p2_norm214 D i,original_p3_norm214 D i⟩

end CompoundFeasibility.SourceOriginalNorm214
