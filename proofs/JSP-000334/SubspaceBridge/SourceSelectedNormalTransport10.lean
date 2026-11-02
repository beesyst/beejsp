import SubspaceBridge.SourceSampleSchmidtExclusion10
import SubspaceBridge.SourceSelectedSampleUpper10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceGlobalSelected10
open SourceSampling10 OriginalDual10 SourceSelectedSet10 SourceSelectedUpper10 SchmidtNormal10

theorem mixedProduct10_ne_zero_iff (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (M : Fin 10 → ℤ) (s : MixedIndex10) :
    mixedProduct10 A2 A3 L M s ≠ 0 ↔
      (L⁻¹.transpose *ᵥ integerReal M) (s 0) ≠ 0 ∧
      ((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (M k : ℚ_[2]))) (s 1) ≠ 0 ∧
      ((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k => (M k : ℚ_[3]))) (s 2) ≠ 0 := by
  simp only [mixedProduct10,mul_ne_zero_iff,abs_ne_zero,norm_ne_zero_iff,and_assoc]

theorem mixedProduct10_int_mul_ne_zero_iff (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (g : ℤ) (hg : g ≠ 0)
    (M : Fin 10 → ℤ) (s : MixedIndex10) :
    mixedProduct10 A2 A3 L (fun k => g*M k) s ≠ 0 ↔ mixedProduct10 A2 A3 L M s ≠ 0 := by
  rw [mixedProduct10_int_mul]
  have hn := ne_of_gt (zero_lt_one.trans_le (integer_three_place_scalar10 g hg))
  exact ⟨fun h => (mul_ne_zero_iff.mp h).2,fun h => mul_ne_zero hn h⟩

theorem original_attaining_cofactor_factor10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {c2 c3 : Fin 10 → ℝ} {V : Set ℝ} {v : V → Fin 10 → Fin 10 → ℤ}
    {c : Fin 3 → Fin 10 → ℝ} {epsilon eta D E B rho : ℝ} {m : ℕ} {hm : 0 < m}
    (hv : ∀ q : V, LinearIndependent ℝ (fun j => integerReal (v q j)))
    (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
    (h : Fin m) :
    ∃ g : ℤ, g ≠ 0 ∧ integerLastDual10 (v (S.data.t h)) = fun i => g*S.data.M h i := by
  let f : (Fin 10 → ℚ) →ₗ[ℚ] (Fin 10 → ℝ) :=
    LinearMap.pi (fun i => (Algebra.linearMap ℚ ℝ).comp (LinearMap.proj i))
  have hvQ : LinearIndependent ℚ (fun j i => (v (S.data.t h) j i : ℚ)) := by
    apply LinearIndependent.of_comp f
    convert (hv (S.data.t h)).restrict_scalars' ℚ using 1
  have hann (j : Fin 9) : (∑ i, S.data.M h i*v (S.data.t h) j.castSucc i) = 0 := by
    have hk : (fun i => (v (S.data.t h) j.castSucc i : ℚ)) ∈
        LinearMap.ker (normalForm10 (S.data.M h)) := by
      rw [S.conditions.original_rational_kernel h]
      exact Submodule.subset_span ⟨j,rfl⟩
    have hq : (∑ i, (S.data.M h i : ℚ)*(v (S.data.t h) j.castSucc i : ℚ)) = 0 := hk
    exact_mod_cast hq
  have hg := SourcePrimitiveHeight10.primitive_original_cofactor_factor10
    (v (S.data.t h)) hvQ (S.data.M h) (S.data.a h)
    (S.conditions.normal_nonzero h) (S.conditions.bezout h) hann
  exact ⟨_,hg.1,funext hg.2.1⟩

theorem original_cofactor_sample_nonzero10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {c2 c3 : Fin 10 → ℝ} {V : Set ℝ} {v : V → Fin 10 → Fin 10 → ℤ}
    {c : Fin 3 → Fin 10 → ℝ} {epsilon eta D E B rho : ℝ} {m : ℕ} {hm : 0 < m}
    (hv : ∀ q : V, LinearIndependent ℝ (fun j => integerReal (v q j)))
    (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
    (h : Fin m) (s : MixedIndex10)
    (hn : mixedProduct10 A2 A3 L (integerLastDual10 (v (S.data.t h))) s ≠ 0) :
    mixedProduct10 A2 A3 L (S.data.M h) s ≠ 0 := by
  obtain ⟨g,hg,hscale⟩ := original_attaining_cofactor_factor10 hv S h
  rw [hscale] at hn
  exact (mixedProduct10_int_mul_ne_zero_iff A2 A3 L g hg (S.data.M h) s).mp hn

end CompoundFeasibility.SourceGlobalSelected10
