import SubspaceBridge.SourceOriginalRationalDual10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.M216ProductBridge
open SourceOriginalVariable10 SourceOriginalDual10 OriginalDual10
variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset SourceSelectedSet10.MixedIndex10}

theorem original_product_expanded216
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (u : Fin 10 → Fin 10 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) (s : Fin 3 → Fin 10) :
    originalRationalDualProduct10 A2 A3 L u hu s =
      let v : Fin 10 → ℚ := lastDual10 (fun j i => (u j i : ℚ)) hu
      |(L⁻¹.transpose *ᵥ (fun k => (v k : ℝ))) (s 0)| *
        ‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (v k : ℚ_[2]))) (s 1)‖ *
        ‖((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k => (v k : ℚ_[3]))) (s 2)‖ := by
  dsimp only [originalRationalDualProduct10]

theorem data_product_witness216 (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    dataRationalDualProduct10._proof_6 D =
      integer_frame_rational_independent10 D.u D.independent := by
  exact Subsingleton.elim _ _

theorem data_product_expanded216 (D : OriginalData10 A2 A3 L hL Q hQ delta S0)
    (s : Fin 3 → Fin 10) :
    dataRationalDualProduct10 D s =
      let hu := integer_frame_rational_independent10 D.u D.independent
      let v : Fin 10 → ℚ := lastDual10 (fun j i => (D.u j i : ℚ)) hu
      |(L⁻¹.transpose *ᵥ (fun k => (v k : ℝ))) (s 0)| *
        ‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (v k : ℚ_[2]))) (s 1)‖ *
        ‖((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k => (v k : ℚ_[3]))) (s 2)‖ := by
  calc
    dataRationalDualProduct10 D s = originalRationalDualProduct10 A2 A3 L D.u
        (integer_frame_rational_independent10 D.u D.independent) s :=
      congrArg (fun h => originalRationalDualProduct10 A2 A3 L D.u h s)
        (data_product_witness216 D)
    _ = _ := original_product_expanded216 A2 A3 L D.u
      (integer_frame_rational_independent10 D.u D.independent) s

end CompoundFeasibility.M216ProductBridge
#print CompoundFeasibility.M216ProductBridge.original_product_expanded216
#print axioms CompoundFeasibility.M216ProductBridge.original_product_expanded216
#print CompoundFeasibility.M216ProductBridge.data_product_expanded216
#print axioms CompoundFeasibility.M216ProductBridge.data_product_expanded216

#print CompoundFeasibility.M216ProductBridge.data_product_witness216
#print axioms CompoundFeasibility.M216ProductBridge.data_product_witness216
