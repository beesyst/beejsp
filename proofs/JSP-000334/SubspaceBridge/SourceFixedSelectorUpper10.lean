import SubspaceBridge.SourceSampleHeightBounds10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFixedSelector10
open SourceSelectedSet10 SourceSelectedUpper10 SourceHeightEnvelope10 SourceSampling10 OriginalDual10

theorem fixed_set_sample_upper10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (c2 c3 : Fin 10 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (c : Fin 3 → Fin 10 → ℝ) (hb : (∑ tau, ∑ i, c tau i) = 0)
    (hc : ∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5)
    (epsilon : ℝ) (he : 0 < epsilon) (S0 : Finset MixedIndex10)
    (hmargin : ∀ s ∈ S0, -3*epsilon/4 ≤ ∑ tau, c tau (s tau))
    {V : Set ℝ} {v : V → Fin 10 → Fin 10 → ℤ}
    {eta D E B rho : ℝ} {m : ℕ} {hm : 0 < m}
    (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
    (h : Fin m) (s : MixedIndex10) (hs : s ∈ S0) :
    mixedProduct10 A2 A3 L (S.data.M h) s ≤
      362880*((S.data.t h).val^5)^(-epsilon/8) := by
  obtain ⟨g,hg,hscale⟩ := original_sample_cofactor_factor10 S h
  have htransfer := mixedProduct10_le_int_mul10 A2 A3 L g hg (S.data.M h) s
  rw [← hscale] at htransfer
  apply htransfer.trans
  apply (original_cofactor_mixed_power10 A2 A3 L h2 h3 hL (S.data.t h).val epsilon
    (S.conditions.large h).2.1 c2 c3 hc2 hc3 c hb hc (S.data.w h)
    (S.conditions.member h) (S.conditions.real_bound h) s).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 362880)
  apply Real.rpow_le_rpow_of_exponent_le (S.conditions.large h).2.2.1.le
  linarith [hmargin s hs]

end CompoundFeasibility.SourceFixedSelector10
