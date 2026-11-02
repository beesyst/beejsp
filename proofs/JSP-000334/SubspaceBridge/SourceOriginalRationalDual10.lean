import SubspaceBridge.SourceDualReal10
import SubspaceBridge.SourceDualP2_10
import SubspaceBridge.SourceDualP3_10
import SubspaceBridge.SourceOriginalData10
import SubspaceBridge.SourceSelectedNormalTransport10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceOriginalDual10
open OriginalDual10 SourceSelectedSet10 SourceSelectedUpper10 SourceGlobalSelected10 SourceOriginalVariable10
noncomputable section

def originalRationalDualProduct10 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (u : Fin 10 → Fin 10 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) (s : MixedIndex10) : ℝ :=
  |(L⁻¹.transpose *ᵥ (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : ℝ))) (s 0)| *
    ‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ
      (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : ℚ_[2]))) (s 1)‖ *
    ‖((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ
      (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : ℚ_[3]))) (s 2)‖

theorem original_rational_product_nonzero_iff (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (u : Fin 10 → Fin 10 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) (s : MixedIndex10) :
    originalRationalDualProduct10 A2 A3 L u hu s ≠ 0 ↔
      mixedProduct10 A2 A3 L (integerLastDual10 u) s ≠ 0 := by
  have hp : originalRationalDualProduct10 A2 A3 L u hu s ≠ 0 ↔
      (L⁻¹.transpose *ᵥ (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : ℝ))) (s 0) ≠ 0 ∧
      ((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ
        (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : ℚ_[2]))) (s 1) ≠ 0 ∧
      ((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ
        (fun k => (lastDual10 (fun j i => (u j i : ℚ)) hu k : ℚ_[3]))) (s 2) ≠ 0 := by
    simp only [originalRationalDualProduct10,mul_ne_zero_iff,abs_ne_zero,norm_ne_zero_iff,and_assoc]
  constructor
  · intro h
    obtain ⟨h0,h2,h3⟩ := hp.mp h
    exact (mixedProduct10_ne_zero_iff A2 A3 L (integerLastDual10 u) s).mpr
      ⟨(original_real_nonzero10 L u hu (s 0)).mpr h0,
       (original_p2_nonzero10 A2 u hu (s 1)).mpr h2,
       (original_p3_nonzero10 A3 u hu (s 2)).mpr h3⟩
  · intro h
    obtain ⟨h0,h2,h3⟩ := (mixedProduct10_ne_zero_iff A2 A3 L (integerLastDual10 u) s).mp h
    exact hp.mpr ⟨(original_real_nonzero10 L u hu (s 0)).mp h0,
      (original_p2_nonzero10 A2 u hu (s 1)).mp h2,
      (original_p3_nonzero10 A3 u hu (s 2)).mp h3⟩

theorem integer_frame_rational_independent10 (u : Fin 10 → Fin 10 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j))) :
    LinearIndependent ℚ (fun j i => (u j i : ℚ)) := by
  let f : (Fin 10 → ℚ) →ₗ[ℚ] (Fin 10 → ℝ) :=
    LinearMap.pi (fun i => (Algebra.linearMap ℚ ℝ).comp (LinearMap.proj i))
  apply LinearIndependent.of_comp f
  convert hu.restrict_scalars' ℚ using 1

def dataRationalDualProduct10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset MixedIndex10}
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (s : MixedIndex10) : ℝ :=
  originalRationalDualProduct10 A2 A3 L D.u
    (integer_frame_rational_independent10 D.u D.independent) s

theorem data_rational_product_nonzero_iff
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset MixedIndex10}
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (s : MixedIndex10) :
    dataRationalDualProduct10 D s ≠ 0 ↔ mixedProduct10 A2 A3 L (integerLastDual10 D.u) s ≠ 0 :=
  original_rational_product_nonzero_iff A2 A3 L D.u
    (integer_frame_rational_independent10 D.u D.independent) s

end
end CompoundFeasibility.SourceOriginalDual10
