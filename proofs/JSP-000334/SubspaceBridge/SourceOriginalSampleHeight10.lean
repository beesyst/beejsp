import SubspaceBridge.SourceOriginalSampleTransfer10
import SubspaceBridge.SourceFixedSelectorHeight10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceOriginalVariable10
open SourceSampling10 SourceSelectedSet10 SourceSelectedUpper10 OriginalDual10 SourceHeightEnvelope10 SchmidtNormal10
noncomputable section

theorem original_fixed_set_sample_height10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    ∃ alpha C_upper T : ℝ, 0 < alpha ∧ 0 < C_upper ∧ 1 < T ∧
      ∀ (S0 : Finset MixedIndex10) (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q)
        (D : (q : V) → OriginalData10 A2 A3 L hL q.val (hQV q.val q.property) delta S0),
      (∀ q : V, ∃ s ∈ S0, mixedProduct10 A2 A3 L (integerLastDual10 (D q).u) s ≠ 0) →
      ∀ (c2 c3 : Fin 10 → ℝ) (c : Fin 3 → Fin 10 → ℝ), (∀ i, |c 0 i| ≤ 1) →
      ∀ (e : ℝ), 0 < e → ∀ (eta D0 E0 B rho : ℝ) (m : ℕ) (hm : 0 < m)
        (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V (fun q => (D q).u) c e eta D0 E0 B rho m hm)
        (h : Fin m), T < (S.data.t h).val^5 →
          ((S.data.t h).val^5)^alpha ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
          (normalHeight10 (S.data.M h) : ℝ) ≤ C_upper*((S.data.t h).val^5)^9 := by
  obtain ⟨C,hC,d,hlower⟩ := actual_same_normal_mixed_lower10 A2 A3 L h2 h3 hLd hAlg
  let z := 68*delta/5
  have hz : 0 < z := by dsimp [z]; positivity
  obtain ⟨T,hT,hcut⟩ := height_growth_cutoff10 C z hC hz
  refine ⟨z/(16*((d+2 : ℕ) : ℝ)),transposeRowConstant10 L*362880,T,
    by positivity,mul_pos (transposeRowConstant10_pos L) (by norm_num),hT,?_⟩
  intro S0 V hQV D hbad c2 c3 c hc0 e he eta D0 E0 B rho m hm S h hlarge
  obtain ⟨s,hs,hn,hu⟩ := original_fixed_set_sample_transfer10 h2 h3 hLd hQV D hbad S h
  have hn' := (SourceGlobalSelected10.mixedProduct10_ne_zero_iff A2 A3 L (S.data.M h) s).mp hn
  have hl := hlower (S.data.M h) (s 0) (s 1) (s 2) hn'.1 hn'.2.1 hn'.2.2
  rw [original_p2_dual_norm10 A2 h2 (S.data.M h) (s 1),
    original_p3_dual_norm10 A3 h3 (S.data.M h) (s 2)] at hl
  rw [mixedProduct10_canonical A2 A3 L h2 h3 (S.data.M h) s] at hu
  have heq : -17*delta/10 = -z/8 := by dsimp [z]; ring
  rw [heq] at hu
  have htotal : C ≤ 362880*((S.data.t h).val^5)^(-z/8)*
      (max 1 (normalHeight10 (S.data.M h) : ℝ))^(d+2) :=
    hl.trans (mul_le_mul_of_nonneg_right hu (by positivity))
  have hp := height_power_rearrange10 C _ z _ d
    (zero_lt_one.trans (S.conditions.large h).2.2.1) htotal
  have hheight := nonzero_normal_height_one10 (S.data.M h) (S.conditions.normal_nonzero h)
  rw [max_eq_right hheight] at hp
  have hgrowth := height_growth_root10 _ z _ d
    (zero_lt_one.trans (S.conditions.large h).2.2.1) (zero_le_one.trans hheight)
    ((hcut _ hlarge).trans hp)
  obtain ⟨g,_hg,_hscale,hupper⟩ := original_sample_height_upper10 hLd hc0 he S h
  exact ⟨hgrowth,hupper⟩

end
end CompoundFeasibility.SourceOriginalVariable10
