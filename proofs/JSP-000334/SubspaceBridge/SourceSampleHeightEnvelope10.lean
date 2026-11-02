import SubspaceBridge.SourceSampleHeightBounds10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceHeightEnvelope10
open SchmidtNormal10 OriginalDual10 SourceSampling10 SourceSelectedSet10 SourceSelectedUpper10

theorem original_sample_height_envelope10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c2 c3 : Fin 10 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (c : Fin 3 → Fin 10 → ℝ) (hc0 : ∀ i, |c 0 i| ≤ 1) (hb : (∑ tau, ∑ i, c tau i) = 0)
    (hc : ∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ alpha C_upper T : ℝ, 0 < alpha ∧ 0 < C_upper ∧ 1 < T ∧
      ∀ (V : Set ℝ) (v : V → Fin 10 → Fin 10 → ℤ)
        (eta D E B rho : ℝ) (m : ℕ) (hm : 0 < m)
        (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
        (h : Fin m), T < (S.data.t h).val^5 →
        ∀ s : MixedIndex10,
          s ∈ roundedSelector10 ((S.data.t h).val^5) (epsilon/2)
            (fun i => ((S.data.t h).val^5)^(c 0 i)) (c 1) (c 2) →
          (L⁻¹.transpose *ᵥ integerReal (S.data.M h)) (s 0) ≠ 0 →
          ((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ
            (fun k => (S.data.M h k : ℚ_[2]))) (s 1) ≠ 0 →
          ((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ
            (fun k => (S.data.M h k : ℚ_[3]))) (s 2) ≠ 0 →
          ((S.data.t h).val^5)^alpha ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
          (normalHeight10 (S.data.M h) : ℝ) ≤ C_upper*((S.data.t h).val^5)^9 := by
  obtain ⟨C,hC,d,hpower⟩ := original_sample_height_power10 A2 A3 L h2 h3 hL hAlg
    c2 c3 hc2 hc3 c hb hc epsilon he
  obtain ⟨_K,T_upper,_hK,hT_upper,_hupper⟩ := original_sample_selected_upper10
    A2 A3 L h2 h3 hL c2 c3 hc2 hc3 c hb hc epsilon he
  obtain ⟨T,hT,hcut⟩ := height_growth_cutoff10 C epsilon hC he
  refine ⟨epsilon/(16*((d+2 : ℕ) : ℝ)),transposeRowConstant10 L*362880,max T_upper T,
    by positivity,mul_pos (transposeRowConstant10_pos L) (by norm_num),hT_upper.trans_le (le_max_left _ _),?_⟩
  intro V v eta D E B rho m hm S h hlarge s hs hn0 hn2 hn3
  have hheight := nonzero_normal_height_one10 (S.data.M h) (S.conditions.normal_nonzero h)
  have hp := (hpower V v eta D E B rho m hm S h s hs hn0 hn2 hn3).2
  rw [max_eq_right hheight] at hp
  have hgrowth := height_growth_root10 _ epsilon _ d
    (zero_lt_one.trans (S.conditions.large h).2.2.1) (zero_le_one.trans hheight)
    ((hcut _ ((le_max_right _ _).trans_lt hlarge)).trans hp)
  obtain ⟨g,_hg,_hscale,hupper⟩ := original_sample_height_upper10 hL hc0 he S h
  exact ⟨hgrowth,hupper⟩

end CompoundFeasibility.SourceHeightEnvelope10
