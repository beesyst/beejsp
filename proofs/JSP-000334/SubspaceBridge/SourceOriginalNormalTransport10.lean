import SubspaceBridge.SourceOriginalData10
import SubspaceBridge.SourceSelectedNormalTransport10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceOriginalVariable10
open SourceSelectedSet10 SourceSelectedUpper10 OriginalDual10 SourceGlobalSelected10
noncomputable section

theorem original_data_primitive_upper_nonzero10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset MixedIndex10}
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1)
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (M a : Fin 10 → ℤ)
    (hM : M ≠ 0) (ha : (∑ i, a i*M i) = 1)
    (hann : ∀ j : Fin 9, (∑ i, M i*D.u j.castSucc i) = 0) :
    ∃ g : ℤ, g ≠ 0 ∧ integerLastDual10 D.u = (fun i => g*M i) ∧
      ∀ s ∈ S0, mixedProduct10 A2 A3 L M s ≤ 362880*Q^(-17*delta/2) ∧
        (mixedProduct10 A2 A3 L (integerLastDual10 D.u) s ≠ 0 ↔
          mixedProduct10 A2 A3 L M s ≠ 0) := by
  let f : (Fin 10 → ℚ) →ₗ[ℚ] (Fin 10 → ℝ) :=
    LinearMap.pi (fun i => (Algebra.linearMap ℚ ℝ).comp (LinearMap.proj i))
  have hvQ : LinearIndependent ℚ (fun j i => (D.u j i : ℚ)) := by
    apply LinearIndependent.of_comp f
    convert D.independent.restrict_scalars' ℚ using 1
  have hg := SourcePrimitiveHeight10.primitive_original_cofactor_factor10 D.u hvQ M a hM ha hann
  let g : ℤ := ∑ i, a i*integerLastDual10 D.u i
  have hscale : integerLastDual10 D.u = fun i => g*M i := funext hg.2.1
  refine ⟨g,hg.1,hscale,?_⟩
  intro s hs
  have hup := original_data_cofactor_upper10 h2 h3 hLd D s hs
  have hle := mixedProduct10_le_int_mul10 A2 A3 L g hg.1 M s
  rw [← hscale] at hle
  refine ⟨hle.trans hup,?_⟩
  rw [hscale]
  exact mixedProduct10_int_mul_ne_zero_iff A2 A3 L g hg.1 M s

end
end CompoundFeasibility.SourceOriginalVariable10
