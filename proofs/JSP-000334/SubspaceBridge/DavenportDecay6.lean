import SubspaceBridge.Davenport6
open scoped BigOperators Matrix
namespace CompoundFeasibility
noncomputable section

theorem directMinima42_product_upper (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (C₄ : ℝ) (hC : 0 < C₄)
    (hfour : (∏ i : Fin 4, sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ≤ C₄) :
    (∏ j : Fin 6, directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ≤ 64 * C₄^3 := by
  have hp := (directMinima42_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1
  have hc := directMinima42_comparison A₂ A₃ L hL Q hQ c₀ c₂ c₃ hc₂ hc₃
  have hu := source_compound_minima_upper42 A₂ A₃ L hL Q hQ c₀ c₂ c₃
  calc
    _ ≤ ∏ j : Fin 6, (2 * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) :=
      Finset.prod_le_prod (fun i _ => (hp i).le) (fun i _ => (hc i).1.trans (hu i))
    _ = 64 * (∏ i : Fin 4, sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i)^3 := by
      rw [Finset.prod_mul_distrib, sourcePairProducts42_product]
      norm_num
    _ ≤ 64 * C₄^3 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.prod_pos (fun i _ =>
        (sourceMinima4_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1 i)).le hfour 3) (by norm_num)

theorem gapRadius6_quantitative (rho : Fin 6 → ℝ) (hp : ∀ i, 0 < rho i)
    (B Q delta : ℝ) (hQ : 1 < Q) (hprod : (∏ i, rho i) ≤ B)
    (hgap : rho 4 < rho 5 * Q ^ (-delta/2)) :
    gapRadius6 rho ^ (6 : ℕ) < B * Q ^ (-delta/2) := by
  rw [gapRadius6_source_formula rho hp]
  have hratio : rho 4 / rho 5 < Q ^ (-delta/2) := (div_lt_iff₀ (hp 5)).mpr (by nlinarith [hgap])
  exact (mul_lt_mul_of_pos_left hratio (Finset.prod_pos (fun i _ => hp i))).trans_le
    (mul_le_mul_of_nonneg_right hprod (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _).le)

theorem davenport_decay_absorb6 (R B Q delta : ℝ) (hR : 0 ≤ R) (hQ : 1 < Q)
    (hroot : R^(6 : ℕ) < B * Q ^ (-delta/2))
    (hcut : (64 : ℝ)^6 * B < Q ^ (delta/4)) :
    64 * R < Q ^ (-delta/24) := by
  have hq : 0 < Q := lt_trans zero_lt_one hQ
  have he : (Q ^ (-delta/24)) ^ (6 : ℕ) = Q ^ (-delta/4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    congr 1
    ring
  have hmul : Q ^ (delta/4) * Q ^ (-delta/2) = Q ^ (-delta/4) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  have hh : (64 * R)^(6 : ℕ) < (Q ^ (-delta/24))^(6 : ℕ) := by
    rw [mul_pow, he]
    calc
      _ < (64 : ℝ)^6 * (B * Q ^ (-delta/2)) := mul_lt_mul_of_pos_left hroot (by norm_num)
      _ = ((64 : ℝ)^6 * B) * Q ^ (-delta/2) := by ring
      _ < Q ^ (delta/4) * Q ^ (-delta/2) := mul_lt_mul_of_pos_right hcut (Real.rpow_pos_of_pos hq _)
      _ = _ := hmul
  exact lt_of_pow_lt_pow_left₀ 6 (Real.rpow_pos_of_pos hq _).le hh

def sourceDavenportDecay42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (delta : ℝ)
    (v : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃) : Prop :=
  let rho := directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let d := gapDeformation6 rho
  ∃ hd : ∀ i, 0 < d i, (∏ i, d i) = 1 ∧ Antitone d ∧ Monotone (fun i => d i * rho i) ∧
    ∃ sigma : Equiv.Perm (Fin 6),
      (∀ j, d j*rho j/64 ≤ directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ d sigma hd j ∧
        directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ d sigma hd j ≤ 64*(d j*rho j)) ∧
      MeasureTheory.volume.real (parallelepipedBody6
        (davenportCoordinates6 (compoundCoordinates42 L hL Q hQ c₀) d sigma hd)) =
          MeasureTheory.volume.real (compoundBody42 L Q c₀) ∧
      (∀ j : Fin 6, ∀ z : directCompoundGroup42 A₂ A₃ Q c₂ c₃,
        integerReal (z : Fin 6 → ℤ) ∉ minimaFlag6 (fun i => integerReal (v i : Fin 6 → ℤ)) j →
        d j*rho j/64 ≤ coordinateGauge6
          (davenportCoordinates6 (compoundCoordinates42 L hL Q hQ c₀) d sigma hd)
            (integerReal (z : Fin 6 → ℤ))) ∧
      directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ d sigma hd 4 ≤ 64*gapRadius6 rho ∧
      directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ d sigma hd 4 < Q ^ (-delta/24) ∧
      ∃ w : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃,
        LinearIndependent ℝ (fun i => integerReal (w i : Fin 6 → ℤ)) ∧
        (∀ i, 0 < directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ d sigma hd i) ∧
        Monotone (directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ d sigma hd) ∧
        ∀ i, coordinateGauge6
          (davenportCoordinates6 (compoundCoordinates42 L hL Q hQ c₀) d sigma hd)
            (integerReal (w i : Fin 6 → ℤ)) =
              directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ d sigma hd i

theorem source_uniform_davenport_decay42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    ∃ C₄ T : ℝ, 0 < C₄ ∧ 1 < T ∧
      (∀ Q : ℝ, T < Q → (64 : ℝ)^6 * (64*C₄^3) < Q ^ (delta/4)) ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) →
        (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) → (∑ i, (c₀ i+c₂ i+c₃ i) = 0) → T < Q →
        ∀ v : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃,
          LinearIndependent ℝ (fun i => integerReal (v i : Fin 6 → ℤ)) →
          (∀ i, coordinateGauge6 (compoundCoordinates42 L (sourceUnit42 L hL) Q hQ c₀)
            (integerReal (v i : Fin 6 → ℤ)) =
              directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) →
          directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 4 <
            directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 5 * Q ^ (-delta/2) →
          let rho := directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
          (0 < ∏ i, rho i) ∧ (∏ i, rho i) ≤ 64*C₄^3 ∧
            gapRadius6 rho^(6 : ℕ) < (64*C₄^3)*Q ^ (-delta/2) ∧
            sourceDavenportDecay42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ delta v := by
  obtain ⟨_,C₄,_,hC,_,hfour⟩ := source_original_uniform_minima_upper4 A₂ A₃ L
    (sourceUnit42 A₂ h₂) (sourceUnit42 A₃ h₃) (sourceUnit42 L hL)
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 ((64 : ℝ)^6*(64*C₄^3)) (delta/2) (by linarith)
  have hexp : delta/2/2 = delta/4 := by ring
  simp only [hexp] at hcut
  refine ⟨C₄,T,hC,hT,hcut,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₀ hc₂ hc₃ hb hTQ v hv hatt hgap
  dsimp only
  let rho := directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
  have hp := (directMinima42_pos_mono A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃).1
  have hprod : (∏ i, rho i) ≤ 64*C₄^3 := directMinima42_product_upper A₂ A₃ L
    (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ (fun i => (hc₂ i).2) (fun i => (hc₃ i).2) C₄ hC
      (hfour Q hQ c₀ c₂ c₃ (fun i => (hc₂ i).2) (fun i => (hc₃ i).2) hb)
  have hroot := gapRadius6_quantitative rho hp (64*C₄^3) Q delta hQ hprod hgap
  refine ⟨Finset.prod_pos (fun i _ => hp i),hprod,hroot,?_⟩
  obtain ⟨hdp,hprodD,hanti,hm,sigma,hbounds,hvol,hsep⟩ :=
    source_davenport42 A₂ A₃ L h₂ h₃ hL hAlg c₀ c₂ c₃ hc₀ hc₂ hc₃ hb Q hQ v hv hatt
  have he : gapDeformation6 rho 4 * rho 4 = gapRadius6 rho := by
    dsimp only [gapDeformation6]
    rw [min_self, div_mul_cancel₀ _ (hp 4).ne']
  have hu : directDavenportMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
      (gapDeformation6 rho) sigma hdp 4 ≤ 64*gapRadius6 rho := by
    have hh : directDavenportMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
        (gapDeformation6 rho) sigma hdp 4 ≤ 64*(gapDeformation6 rho 4*rho 4) := (hbounds 4).2
    rw [he] at hh
    exact hh
  have hsmall := davenport_decay_absorb6 (gapRadius6 rho) (64*C₄^3) Q delta
    (gapRadius6_pos rho hp).le hQ hroot (hcut Q hTQ)
  dsimp only [sourceDavenportDecay42]
  refine ⟨hdp,hprodD,hanti,hm,sigma,hbounds,hvol,hsep,hu,hu.trans_lt hsmall,?_⟩
  exact exists_directDavenportMinima42_attaining A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
    (gapDeformation6 rho) sigma hdp

theorem source_compound_unbounded_davenport_decay42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    (∀ s t, IsAlgebraic ℚ (compound L s t)) ∧
    IsUnit (compound A₂) ∧ IsUnit (compound A₃) ∧ IsUnit (compound L) ∧
    ∃ κ C₄ T : ℝ, 0 < κ ∧ 0 < C₄ ∧ 1 < T ∧ (∀ Q : ℝ, T < Q → 12 / κ < Q ^ (delta / 2)) ∧
      ∀ c₀ c₂ c₃ : Fin 4 → ℝ,
        (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) →
        (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) → (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        (∀ s, |pairWeights42 c₀ s| ≤ 2) ∧
        (∀ s, -2 ≤ pairWeights42 c₂ s ∧ pairWeights42 c₂ s ≤ 0) ∧
        (∀ s, -2 ≤ pairWeights42 c₃ s ∧ pairWeights42 c₃ s ≤ 0) ∧
        (∑ s, (pairWeights42 c₀ s + pairWeights42 c₂ s + pairWeights42 c₃ s) = 0) ∧
        ∀ (U : Set ℝ) (_hUb : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q),
          (∀ (Q : ℝ) (hmem : Q ∈ U),
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hmem) c₀ c₂ c₃ 1 <
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hmem) c₀ c₂ c₃ 2 * Q ^ (-delta)) →
          ∃ (V : Set ℝ) (hVU : V ⊆ U), ¬ BddAbove V ∧
            ∃ (u : (t : V) → Fin 4 → originalSourceGroup4 A₂ A₃ t.val c₂ c₃)
              (v : (t : V) → Fin 6 → directCompoundGroup42 A₂ A₃ t.val c₂ c₃),
              ∀ t : V, T < t.val ∧
                sourceHyperplane42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property))
                  c₀ c₂ c₃ κ (u t) (v t) ∧
                rationalDualLine42 (fun i => (u t i : Fin 4 → ℤ)) (fun j => (v t j : Fin 6 → ℤ))
                  (sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃) ∧
                directMinima42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ 4 <
                directMinima42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ 5 *
                  t.val ^ (-delta / 2) ∧
                let rho := directMinima42 A₂ A₃ L (sourceUnit42 L hL) t.val
                  (hQU t.val (hVU t.property)) c₀ c₂ c₃
                (0 < ∏ i, rho i) ∧ (∏ i, rho i) ≤ 64*C₄^3 ∧
                  gapRadius6 rho^(6 : ℕ) < (64*C₄^3)*t.val ^ (-delta/2) ∧
                  sourceDavenportDecay42 A₂ A₃ L (sourceUnit42 L hL) t.val
                    (hQU t.val (hVU t.property)) c₀ c₂ c₃ delta (v t) := by
  classical
  obtain ⟨hAlgC,hunit₂,hunit₃,hunitL,κ,T₀,hk,hT₀,hcut₀,hfam⟩ :=
    source_compound_unbounded_family42 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  obtain ⟨C₄,T₁,hC,hT₁,hcut₁,hdecay⟩ :=
    source_uniform_davenport_decay42 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  let T := max T₀ T₁
  refine ⟨hAlgC,hunit₂,hunit₃,hunitL,κ,C₄,T,hk,hC,hT₀.trans_le (le_max_left _ _),?_,?_⟩
  · intro Q hTQ
    exact hcut₀ Q ((le_max_left _ _).trans_lt hTQ)
  · intro c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
    obtain ⟨hw₀,hw₂,hw₃,hwb,hfamily⟩ := hfam c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
    refine ⟨hw₀,hw₂,hw₃,hwb,?_⟩
    intro U hUb hQU horiginal
    obtain ⟨V₀,hV₀U,hV₀b,u₀,v₀,hframes⟩ := hfamily U hUb hQU horiginal
    let V := {Q : ℝ | Q ∈ V₀ ∧ T < Q}
    have hVU : V ⊆ U := fun Q hQ => hV₀U hQ.1
    have hVb : ¬ BddAbove V := JSP000334.sourceDual_unbounded_tail3 V₀ hV₀b T
    let lift : V → V₀ := fun t => ⟨t.val,t.property.1⟩
    let u : (t : V) → Fin 4 → originalSourceGroup4 A₂ A₃ t.val c₂ c₃ := fun t => u₀ (lift t)
    let v : (t : V) → Fin 6 → directCompoundGroup42 A₂ A₃ t.val c₂ c₃ := fun t => v₀ (lift t)
    refine ⟨V,hVU,hVb,u,v,?_⟩
    intro t
    obtain ⟨_,hhyper,hdual,hgap⟩ := hframes (lift t)
    have hhyper' : sourceHyperplane42 A₂ A₃ L (sourceUnit42 L hL) t.val
        (hQU t.val (hVU t.property)) c₀ c₂ c₃ κ (u t) (v t) := hhyper
    have hdec := hdecay t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
      ((le_max_right _ _).trans_lt t.property.2) (v t) hhyper'.2.2.1 hhyper'.2.2.2.1 hgap
    exact ⟨t.property.2,hhyper',hdual,hgap,hdec⟩

end
end CompoundFeasibility
