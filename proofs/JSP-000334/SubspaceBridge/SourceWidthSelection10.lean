import SubspaceBridge.SourceWeightSampling10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSampling10
open OriginalDeformation10

theorem fixed_width_exponents10 (U : Set ℝ) (hU : ¬ BddAbove U)
    (hQ : ∀ q ∈ U, 1 < q) (W : U → Fin 10 → ℝ) (c2 c3 : Fin 10 → ℝ)
    (hW : ∀ q i, 0 < W q i)
    (hsizes : ∀ q i, W q i < q.val^5 ∧ (W q i)⁻¹ < q.val^5)
    (hbal : ∀ q, (∏ i, W q i)*(∏ i, q.val^(c2 i+c3 i)) = 1)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ V : Set ℝ, ∃ hVU : V ⊆ U, ¬ BddAbove V ∧
      ∃ a : Fin 10 → ℝ, (∀ i, -1 < a i ∧ a i < 1) ∧
        (∑ i, a i)+(∑ i, c2 i/5)+(∑ i, c3 i/5) = 0 ∧
        ∀ q : V, ∀ i, W ⟨q.val,hVU q.property⟩ i ≤ (q.val^5)^(a i+epsilon) := by
  let alpha (q : ℝ) (i : Fin 10) := if hq : q ∈ U then logWeight10 (q^5) (W ⟨q,hq⟩ i) else 0
  have halpha (q : U) (i) : alpha q.val i = logWeight10 (q.val^5) (W q i) := by
    simp only [alpha,dif_pos q.property]
  have hQ5 (q : U) : 1 < q.val^5 := one_lt_pow₀ (hQ q.val q.property) (by decide)
  have hab (q : U) (i) : -1 < alpha q.val i ∧ alpha q.val i < 1 := by
    rw [halpha]
    exact logWeight10_bounds _ _ (hQ5 q) (hW q i) (hsizes q i).1 (hsizes q i).2
  obtain ⟨V,hVU,hV,q0,hq0,hclose⟩ := select_unbounded_weights10 U hU alpha
    (fun q hq i => abs_le.mpr ⟨(hab ⟨q,hq⟩ i).1.le,(hab ⟨q,hq⟩ i).2.le⟩) epsilon he
  let q : U := ⟨q0,hVU hq0⟩
  have hp : (∏ i, W q i*(q0^5)^(c2 i/5)*(q0^5)^(c3 i/5)) = 1 := by
    simp_rw [rescaled_power10 q0 _ (zero_lt_one.trans (hQ q0 q.property))]
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,mul_assoc,← Finset.prod_mul_distrib]
    simpa only [← Real.rpow_add (zero_lt_one.trans (hQ q0 q.property))] using hbal q
  have hb := logWeight10_balance (q0^5) (hQ5 q) (W q) (fun i => c2 i/5) (fun i => c3 i/5) (hW q) hp
  refine ⟨V,hVU,hV,alpha q0,hab q,?_,?_⟩
  · have hs : (∑ i, alpha q0 i) = ∑ i, logWeight10 (q0^5) (W q i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact halpha q i
    rw [hs]
    exact hb
  · intro v i
    have hv : alpha v.val i ≤ alpha q0 i+epsilon := by
      have hh := (abs_lt.mp (hclose v.val v.property i)).2
      linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le (hQ5 ⟨v.val,hVU v.property⟩).le hv
    rw [halpha ⟨v.val,hVU v.property⟩ i,logWeight10_power _ _ (hQ5 ⟨v.val,hVU v.property⟩) (hW ⟨v.val,hVU v.property⟩ i)] at hpow
    exact hpow

end CompoundFeasibility.SourceSampling10
