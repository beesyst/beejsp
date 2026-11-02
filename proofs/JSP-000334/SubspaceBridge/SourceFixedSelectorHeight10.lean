import SubspaceBridge.SourceFixedSelectorUpper10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFixedSelector10
open SourceSelectedSet10 SourceSelectedUpper10 SourceHeightEnvelope10 SourceSampling10 OriginalDual10 SchmidtNormal10

theorem fixed_set_height_envelope10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ alpha C_upper T : ℝ, 0 < alpha ∧ 0 < C_upper ∧ 1 < T ∧
      ∀ (c2 c3 : Fin 10 → ℝ), (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) →
      ∀ (c : Fin 3 → Fin 10 → ℝ), (∀ i, |c 0 i| ≤ 1) →
      (∑ tau, ∑ i, c tau i) = 0 → (∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5) →
      ∀ S0 : Finset MixedIndex10, (∀ s ∈ S0, -3*epsilon/4 ≤ ∑ tau, c tau (s tau)) →
      ∀ (V : Set ℝ) (v : V → Fin 10 → Fin 10 → ℤ)
        (eta D E B rho : ℝ) (m : ℕ) (hm : 0 < m)
        (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
        (h : Fin m), T < (S.data.t h).val^5 →
        ∀ s ∈ S0,
          (L⁻¹.transpose *ᵥ integerReal (S.data.M h)) (s 0) ≠ 0 →
          ((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ
            (fun k => (S.data.M h k : ℚ_[2]))) (s 1) ≠ 0 →
          ((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ
            (fun k => (S.data.M h k : ℚ_[3]))) (s 2) ≠ 0 →
          ((S.data.t h).val^5)^alpha ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
          (normalHeight10 (S.data.M h) : ℝ) ≤ C_upper*((S.data.t h).val^5)^9 := by
  obtain ⟨C,hC,d,hlower⟩ := actual_same_normal_mixed_lower10 A2 A3 L h2 h3 hL hAlg
  obtain ⟨T,hT,hcut⟩ := height_growth_cutoff10 C epsilon hC he
  refine ⟨epsilon/(16*((d+2 : ℕ) : ℝ)),transposeRowConstant10 L*362880,T,
    by positivity,mul_pos (transposeRowConstant10_pos L) (by norm_num),hT,?_⟩
  intro c2 c3 hc2 hc3 c hc0 hb hc S0 hmargin V v eta D E B rho m hm S h hlarge s hs hn0 hn2 hn3
  have hl := hlower (S.data.M h) (s 0) (s 1) (s 2) hn0 hn2 hn3
  rw [original_p2_dual_norm10 A2 h2 (S.data.M h) (s 1),
    original_p3_dual_norm10 A3 h3 (S.data.M h) (s 2)] at hl
  have hu := fixed_set_sample_upper10 A2 A3 L h2 h3 hL c2 c3 hc2 hc3 c hb hc epsilon he
    S0 hmargin S h s hs
  rw [mixedProduct10_canonical A2 A3 L h2 h3 (S.data.M h) s] at hu
  have htotal : C ≤ 362880*((S.data.t h).val^5)^(-epsilon/8)*
      (max 1 (normalHeight10 (S.data.M h) : ℝ))^(d+2) :=
    hl.trans (mul_le_mul_of_nonneg_right hu (by positivity))
  have hp := height_power_rearrange10 C _ epsilon _ d
    (zero_lt_one.trans (S.conditions.large h).2.2.1) htotal
  have hheight := nonzero_normal_height_one10 (S.data.M h) (S.conditions.normal_nonzero h)
  rw [max_eq_right hheight] at hp
  have hgrowth := height_growth_root10 _ epsilon _ d
    (zero_lt_one.trans (S.conditions.large h).2.2.1) (zero_le_one.trans hheight)
    ((hcut _ hlarge).trans hp)
  obtain ⟨g,_hg,_hscale,hupper⟩ := original_sample_height_upper10 hL hc0 he S h
  exact ⟨hgrowth,hupper⟩

end CompoundFeasibility.SourceFixedSelector10
