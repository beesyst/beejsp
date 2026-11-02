import SubspaceBridge.SourceSelectedCofactorUpper10
import SubspaceBridge.SourceSelectedPrimitive10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSelectedUpper10
open OriginalDual10 SourceSelectedSet10 SchmidtNormal10 SourceHeightEnvelope10 SourceSampling10

theorem original_sample_cofactor_factor10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {c2 c3 : Fin 10 → ℝ} {V : Set ℝ} {v : V → Fin 10 → Fin 10 → ℤ}
    {c : Fin 3 → Fin 10 → ℝ} {epsilon eta D E B rho : ℝ} {m : ℕ} {hm : 0 < m}
    (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
    (h : Fin m) :
    ∃ g : ℤ, g ≠ 0 ∧ integerLastDual10 (S.data.w h) = fun i => g*S.data.M h i := by
  let f : (Fin 10 → ℚ) →ₗ[ℚ] (Fin 10 → ℝ) :=
    LinearMap.pi (fun i => (Algebra.linearMap ℚ ℝ).comp (LinearMap.proj i))
  have hwQ : LinearIndependent ℚ (fun j i => (S.data.w h j i : ℚ)) := by
    apply LinearIndependent.of_comp f
    convert (S.conditions.independent h).restrict_scalars' ℚ using 1
  have hann (j : Fin 9) : (∑ i, S.data.M h i*S.data.w h j.castSucc i) = 0 := by
    have hk : (fun i => (S.data.w h j.castSucc i : ℚ)) ∈
        LinearMap.ker (normalForm10 (S.data.M h)) := by
      rw [S.conditions.rational_kernel h]
      exact Submodule.subset_span ⟨j,rfl⟩
    have hq : (∑ i, (S.data.M h i : ℚ)*(S.data.w h j.castSucc i : ℚ)) = 0 := hk
    exact_mod_cast hq
  have hg := SourcePrimitiveHeight10.primitive_original_cofactor_factor10
    (S.data.w h) hwQ (S.data.M h) (S.data.a h)
    (S.conditions.normal_nonzero h) (S.conditions.bezout h) hann
  exact ⟨_,hg.1,funext hg.2.1⟩

theorem original_sample_selected_upper_bound10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (c2 c3 : Fin 10 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (c : Fin 3 → Fin 10 → ℝ) (hb : (∑ tau, ∑ i, c tau i) = 0)
    (hc : ∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5)
    (epsilon : ℝ) (he : 0 < epsilon)
    {V : Set ℝ} {v : V → Fin 10 → Fin 10 → ℤ}
    {eta D E B rho : ℝ} {m : ℕ} {hm : 0 < m}
    (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
    (h : Fin m) (s : MixedIndex10)
    (hs : s ∈ roundedSelector10 ((S.data.t h).val^5) (epsilon/2)
      (fun i => ((S.data.t h).val^5)^(c 0 i)) (c 1) (c 2)) :
    mixedProduct10 A2 A3 L (S.data.M h) s ≤
      362880*((S.data.t h).val^5)^(-(epsilon/2)/4) := by
  obtain ⟨g,hg,hscale⟩ := original_sample_cofactor_factor10 S h
  have htransfer := mixedProduct10_le_int_mul10 A2 A3 L g hg (S.data.M h) s
  rw [← hscale] at htransfer
  apply htransfer.trans
  exact original_cofactor_selected_upper10 A2 A3 L h2 h3 hL (S.data.t h).val epsilon
    (S.conditions.large h).2.1 he c2 c3 hc2 hc3 c hb hc (S.data.w h)
    (S.conditions.member h) (S.conditions.real_bound h) s hs

theorem original_sample_selected_upper10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (c2 c3 : Fin 10 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (c : Fin 3 → Fin 10 → ℝ) (hb : (∑ tau, ∑ i, c tau i) = 0)
    (hc : ∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ K T : ℝ, 0 < K ∧ 1 < T ∧
      ∀ (V : Set ℝ) (v : V → Fin 10 → Fin 10 → ℤ)
        (eta D E B rho : ℝ) (m : ℕ) (hm : 0 < m)
        (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
        (h : Fin m), T < (S.data.t h).val^5 →
        ∀ s : MixedIndex10,
          s ∈ roundedSelector10 ((S.data.t h).val^5) (epsilon/2)
            (fun i => ((S.data.t h).val^5)^(c 0 i)) (c 1) (c 2) →
          mixedProduct10 A2 A3 L (S.data.M h) s ≤
            K*((S.data.t h).val^5)^(-(epsilon/2)/4) := by
  refine ⟨362880,2,by norm_num,by norm_num,?_⟩
  intro V v eta D E B rho m hm S h _hlarge s hs
  exact original_sample_selected_upper_bound10 A2 A3 L h2 h3 hL c2 c3 hc2 hc3 c hb hc epsilon he S h s hs

end CompoundFeasibility.SourceSelectedUpper10
