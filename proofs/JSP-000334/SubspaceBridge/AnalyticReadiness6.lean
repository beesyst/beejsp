import SubspaceBridge.DavenportDecay6
open scoped BigOperators Matrix
namespace CompoundFeasibility
noncomputable section

theorem integerReal_norm_lower6 (z : Fin 6 → ℤ) (hz : z ≠ 0) : 1 ≤ ‖integerReal z‖ := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hz
  have hi' : z i ≠ 0 := by simpa only [Pi.zero_apply] using hi
  have ha : (1 : ℝ) ≤ |(z i : ℝ)| := by exact_mod_cast Int.one_le_abs hi'
  exact ha.trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (integerReal z) i)

theorem compound_unweighted_gauge_bound42 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (hc : ∀ i, |c₀ i| ≤ 1) (x : Fin 6 → ℝ) :
    ‖compoundFormEquiv42 L hL x‖ ≤ coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) x * Q^(2 : ℕ) := by
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro s
  have hh := (compoundCoordinates42_bounds L hL Q hQ c₀ x _).mp le_rfl s
  have he : Q ^ c₀ (lo s) * Q ^ c₀ (hi s) ≤ Q^(2 : ℕ) := by
    rw [← Real.rpow_add (lt_trans zero_lt_one hQ)]
    exact_mod_cast Real.rpow_le_rpow_of_exponent_le hQ.le
      (show c₀ (lo s)+c₀ (hi s) ≤ (2 : ℝ) by linarith [(abs_le.mp (hc (lo s))).2,(abs_le.mp (hc (hi s))).2])
  exact hh.trans (mul_le_mul_of_nonneg_left he (norm_nonneg _))

theorem source_direct_first_lower42 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
      (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ), (∀ i, |c₀ i| ≤ 1) →
      1/(C*Q^(2 : ℕ)) ≤ directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 0 := by
  let E := (compoundFormEquiv42 L hL).toContinuousLinearEquiv
  let C := max 1 ‖E.symm.toContinuousLinearMap‖
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro A₂ A₃ Q hQ c₀ c₂ c₃ hc₀
  obtain ⟨u,hu,hp,hm,hatt⟩ := exists_directMinima42_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have hz : (u 0 : Fin 6 → ℤ) ≠ 0 := by
    intro hz
    apply hu.ne_zero 0
    rw [hz,map_zero]
  have hnorm := integerReal_norm_lower6 (u 0) hz
  have hinv : ‖integerReal (u 0 : Fin 6 → ℤ)‖ ≤ C * ‖compoundFormEquiv42 L hL (integerReal (u 0 : Fin 6 → ℤ))‖ := by
    have hi := E.symm.toContinuousLinearMap.le_opNorm (E (integerReal (u 0 : Fin 6 → ℤ)))
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at hi
    exact hi.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hg := compound_unweighted_gauge_bound42 L hL Q hQ c₀ hc₀ (integerReal (u 0 : Fin 6 → ℤ))
  rw [hatt] at hg
  apply (div_le_iff₀ (mul_pos hC (sq_pos_of_pos (lt_trans zero_lt_one hQ)))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hg hC.le,hnorm.trans hinv]

noncomputable def directPrimeExponent42 (p : ℕ) (Q : ℝ) (c : Fin 4 → ℝ) : ℕ :=
  Finset.univ.sup (fun s : Fin 6 => Nat.ceil (JSP000334.qThreshold p Q (c (lo s)+c (hi s))))

theorem directPrimeExponent42_bound (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q)
    (c : Fin 4 → ℝ) (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 0) :
    (p : ℝ)^directPrimeExponent42 p Q c < p*Q^(2 : ℕ) := by
  obtain ⟨s,_,hs⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun s : Fin 6 => Nat.ceil (JSP000334.qThreshold p Q (c (lo s)+c (hi s))))
  change (p : ℝ)^Finset.univ.sup _ < _
  rw [hs,JSP000334.pow_ceil_factorization _ _ (by exact_mod_cast (lt_trans Nat.zero_lt_one hp)),
    JSP000334.qThreshold_rpow p hp Q _ hQ]
  have hb : Q ^ (-(c (lo s)+c (hi s))) ≤ Q^(2 : ℕ) := by
    exact_mod_cast Real.rpow_le_rpow_of_exponent_le hQ.le
      (show -(c (lo s)+c (hi s)) ≤ (2 : ℝ) by linarith [(hc (lo s)).1,(hc (hi s)).1])
  have hf := (JSP000334.ceilingFactor_bounds (p : ℝ) (JSP000334.qThreshold p Q (c (lo s)+c (hi s))) (by exact_mod_cast hp)
    (JSP000334.qThreshold_nonneg p hp Q (c (lo s)+c (hi s)) hQ (add_nonpos (hc (lo s)).2 (hc (hi s)).2))).2
  have hm := mul_lt_mul_of_pos_left hf (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) (-(c (lo s)+c (hi s))))
  have hn := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  nlinarith

theorem local_max_multiple_bounds6 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ) (e : Fin 6 → ℕ) (E : ℕ) (hE : ∀ i, e i ≤ E)
    (D : ℤ) (hD : ∀ i j, ∃ z : ℤ, (z : ℚ) = (D : ℚ)*B i j) (T : ℤ) (j : Fin 6) :
    ∀ i, padicNorm p ((B *ᵥ (fun k => ((Pi.single j (D*(p : ℤ)^E*T) : Fin 6 → ℤ) k : ℚ))) i) ≤
      ((p : ℚ)^(e i))⁻¹ := by
  intro i
  obtain ⟨z,hz⟩ := hD i j
  have hm : (B *ᵥ (fun k => ((Pi.single j (D*(p : ℤ)^E*T) : Fin 6 → ℤ) k : ℚ))) i =
      (((p : ℤ)^E*T*z : ℤ) : ℚ) := by
    have hc : (fun k => ((Pi.single j (D*(p : ℤ)^E*T) : Fin 6 → ℤ) k : ℚ)) =
        Pi.single j ((D : ℚ)*(p : ℚ)^E*(T : ℚ)) := by
      ext k
      by_cases hk : k = j <;> simp [Pi.single_apply,hk]
    rw [hc,Matrix.mulVec_single]
    change B i j*((D : ℚ)*(p : ℚ)^E*(T : ℚ)) = _
    push_cast
    rw [hz]
    ring
  rw [hm]
  have hd : (p : ℤ)^(e i) ∣ (p : ℤ)^E*T*z :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) (hE i)) T) z
  rw [show ((p : ℚ)^(e i))⁻¹ = (p : ℚ)^(-(e i : ℤ)) by rw [zpow_neg,zpow_natCast]]
  apply padicNorm.dvd_iff_norm_le.mp
  exact_mod_cast hd

theorem direct_scaled_basis42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) :
    ∃ D₂ D₃ : ℤ, D₂ ≠ 0 ∧ D₃ ≠ 0 ∧ ∀ Q : ℝ, ∀ c₂ c₃ : Fin 4 → ℝ, ∀ j : Fin 6,
      Pi.single j (D₂*D₃*2^directPrimeExponent42 2 Q c₂*3^directPrimeExponent42 3 Q c₃) ∈
        directCompoundGroup42 A₂ A₃ Q c₂ c₃ := by
  obtain ⟨D₂,hD₂,hm₂⟩ := clear_matrix_denominators (compound A₂)
  obtain ⟨D₃,hD₃,hm₃⟩ := clear_matrix_denominators (compound A₃)
  refine ⟨D₂,D₃,hD₂,hD₃,?_⟩
  intro Q c₂ c₃ j
  constructor
  · change Pi.single j (D₂*D₃*2^directPrimeExponent42 2 Q c₂*3^directPrimeExponent42 3 Q c₃) ∈
      directLocal42 2 A₂ (fun i => JSP000334.qThreshold 2 Q (c₂ i))
    rw [directLocal42_spec]
    have hE : ∀ s : Fin 6, Nat.ceil (JSP000334.qThreshold 2 Q (c₂ (lo s)+c₂ (hi s))) ≤
        directPrimeExponent42 2 Q c₂ := by
      intro s
      exact Finset.le_sup (f := fun s : Fin 6 => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ (lo s)+c₂ (hi s)))) (Finset.mem_univ s)
    have hh := local_max_multiple_bounds6 2 (compound A₂) _ _ hE D₂ hm₂
      (D₃*3^directPrimeExponent42 3 Q c₃) j
    have he : D₂*D₃*2^directPrimeExponent42 2 Q c₂*3^directPrimeExponent42 3 Q c₃ =
        D₂*2^directPrimeExponent42 2 Q c₂*(D₃*3^directPrimeExponent42 3 Q c₃) := by ring
    simpa only [he,qThreshold_add42] using hh
  · change Pi.single j (D₂*D₃*2^directPrimeExponent42 2 Q c₂*3^directPrimeExponent42 3 Q c₃) ∈
      directLocal42 3 A₃ (fun i => JSP000334.qThreshold 3 Q (c₃ i))
    rw [directLocal42_spec]
    have hE : ∀ s : Fin 6, Nat.ceil (JSP000334.qThreshold 3 Q (c₃ (lo s)+c₃ (hi s))) ≤
        directPrimeExponent42 3 Q c₃ := by
      intro s
      exact Finset.le_sup (f := fun s : Fin 6 => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ (lo s)+c₃ (hi s)))) (Finset.mem_univ s)
    have hh := local_max_multiple_bounds6 3 (compound A₃) _ _ hE D₃ hm₃
      (D₂*2^directPrimeExponent42 2 Q c₂) j
    have he : D₂*D₃*2^directPrimeExponent42 2 Q c₂*3^directPrimeExponent42 3 Q c₃ =
        D₃*3^directPrimeExponent42 3 Q c₃*(D₂*2^directPrimeExponent42 2 Q c₂) := by ring
    simpa only [he,qThreshold_add42] using hh

theorem direct_scale_bound42 (D₂ D₃ : ℤ) (Q : ℝ) (hQ : 1 < Q) (c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) :
    |((D₂*D₃*2^directPrimeExponent42 2 Q c₂*3^directPrimeExponent42 3 Q c₃ : ℤ) : ℝ)| ≤
      6*|(D₂*D₃ : ℤ)| *Q^(4 : ℕ) := by
  have h₂ := directPrimeExponent42_bound 2 (by decide) Q hQ c₂ hc₂
  have h₃ := directPrimeExponent42_bound 3 (by decide) Q hQ c₃ hc₃
  have hm := mul_le_mul h₂.le h₃.le (by positivity : (0 : ℝ) ≤ 3^directPrimeExponent42 3 Q c₃)
    (by positivity : (0 : ℝ) ≤ 2*Q^2)
  have hh := mul_le_mul_of_nonneg_left hm (abs_nonneg ((D₂*D₃ : ℤ) : ℝ))
  push_cast at *
  convert hh using 1 <;> simp only [abs_mul,abs_pow,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] <;> ring

theorem compound_weighted_gauge_bound42 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (hc : ∀ i, |c₀ i| ≤ 1) (x : Fin 6 → ℝ) :
    coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) x ≤ ‖compoundFormEquiv42 L hL x‖ * Q^(2 : ℕ) := by
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro s
  have hq : 0 < Q := lt_trans zero_lt_one hQ
  have hw : 0 < Q ^ c₀ (lo s)*Q ^ c₀ (hi s) := mul_pos (Real.rpow_pos_of_pos hq _) (Real.rpow_pos_of_pos hq _)
  have hone : 1 ≤ Q^(2 : ℕ)*(Q ^ c₀ (lo s)*Q ^ c₀ (hi s)) := by
    rw [← Real.rpow_add hq,← Real.rpow_natCast,← Real.rpow_add hq]
    have he := Real.rpow_le_rpow_of_exponent_le hQ.le
      (show (0 : ℝ) ≤ 2+(c₀ (lo s)+c₀ (hi s)) by linarith [(abs_le.mp (hc (lo s))).1,(abs_le.mp (hc (hi s))).1])
    simpa only [Real.rpow_zero] using he
  change ‖(compoundFormEquiv42 L hL x) s / (Q ^ c₀ (lo s)*Q ^ c₀ (hi s))‖ ≤ _
  simp only [norm_div,Real.norm_eq_abs,abs_of_pos hw]
  rw [div_le_iff₀ hw]
  have hh := mul_le_mul_of_nonneg_left hone (norm_nonneg (compoundFormEquiv42 L hL x))
  have hs := norm_le_pi_norm (compoundFormEquiv42 L hL x) s
  rw [Real.norm_eq_abs] at hs
  nlinarith

theorem source_direct_last_upper42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
      (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) →
      (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) →
      directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5 ≤ K*Q^(6 : ℕ) := by
  obtain ⟨D₂,D₃,hD₂,hD₃,hmem⟩ := direct_scaled_basis42 A₂ A₃
  let E := (compoundFormEquiv42 L hL).toContinuousLinearEquiv
  let M := max 1 ‖E.toContinuousLinearMap‖
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hD : 0 < |((D₂*D₃ : ℤ) : ℝ)| := abs_pos.mpr (by exact_mod_cast mul_ne_zero hD₂ hD₃)
  refine ⟨6*|((D₂*D₃ : ℤ) : ℝ)| *M,by positivity,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₀ hc₂ hc₃
  let S : ℤ := D₂*D₃*2^directPrimeExponent42 2 Q c₂*3^directPrimeExponent42 3 Q c₃
  have hS : S ≠ 0 := by dsimp [S]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero hD₂ hD₃) (by positivity)) (by positivity)
  let v : Fin 6 → (Fin 6 → ℝ) := fun j => (S : ℝ) • (Pi.basisFun ℝ (Fin 6)) j
  have hv : LinearIndependent ℝ v := (Pi.basisFun ℝ (Fin 6)).linearIndependent.units_smul
    (fun _ => Units.mk0 (S : ℝ) (by exact_mod_cast hS))
  have heq (j : Fin 6) : v j = integerReal (Pi.single j S) := by
    ext i
    simp [v,integerReal,Pi.basisFun_apply,Pi.single_apply]
  rw [directMinima42_eq_radius]
  apply successiveRadius6_le_family _ _ 5 v hv
  · intro j
    rw [heq,directRealBasis42_span]
    exact ⟨Pi.single j S,hmem Q c₂ c₃ j,rfl⟩
  · intro j
    have hg := compound_weighted_gauge_bound42 L hL Q hQ c₀ hc₀ (v j)
    have he : ‖compoundFormEquiv42 L hL (v j)‖ ≤ M*|((S : ℤ) : ℝ)| := by
      have hh := E.toContinuousLinearMap.le_opNorm (v j)
      have hvn : ‖v j‖ = |((S : ℤ) : ℝ)| := by
        change ‖(S : ℝ) • (Pi.basisFun ℝ (Fin 6)) (j : Fin 6)‖ = _
        rw [norm_smul]
        have hf : (Pi.basisFun ℝ (Fin 6)) (j : Fin 6) = Pi.single (j : Fin 6) (1 : ℝ) := by
          ext i
          by_cases hi : i = (j : Fin 6) <;> simp [Pi.basisFun_apply,Pi.single_apply,hi,eq_comm]
        rw [hf,Pi.norm_single,norm_one,Real.norm_eq_abs,mul_one]
      rw [hvn] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
    have hs := direct_scale_bound42 D₂ D₃ Q hQ c₂ c₃ hc₂ hc₃
    have hq : 0 ≤ Q^(2 : ℕ) := sq_nonneg Q
    have hh := mul_le_mul_of_nonneg_right (he.trans (mul_le_mul_of_nonneg_left hs hM.le)) hq
    apply hg.trans
    convert hh using 1 <;> push_cast <;> ring

theorem gapRadius6_between (rho : Fin 6 → ℝ) (hp : ∀ i, 0 < rho i) (hm : Monotone rho) :
    rho 0 ≤ gapRadius6 rho ∧ gapRadius6 rho ≤ rho 5 := by
  have he : gapRadius6 rho^(6 : ℕ) = ∏ i : Fin 6, rho (min i 4) := by
    rw [gapRadius6_power rho hp,Fin.prod_univ_six]
    rw [show min (0 : Fin 6) 4 = 0 by decide, show min (1 : Fin 6) 4 = 1 by decide,
      show min (2 : Fin 6) 4 = 2 by decide, show min (3 : Fin 6) 4 = 3 by decide,
      min_self,show min (5 : Fin 6) 4 = 4 by decide]
    ring
  have hlo : rho 0^(6 : ℕ) ≤ gapRadius6 rho^(6 : ℕ) := by
    rw [he]
    calc
      _ = ∏ _i : Fin 6, rho 0 := by simp
      _ ≤ _ := Finset.prod_le_prod (fun i _ => (hp 0).le) (fun i _ => hm (by omega))
  have hhi : gapRadius6 rho^(6 : ℕ) ≤ rho 5^(6 : ℕ) := by
    rw [he]
    calc
      _ ≤ ∏ _i : Fin 6, rho 5 := Finset.prod_le_prod (fun i _ => (hp _).le) (fun i _ => hm (by omega))
      _ = _ := by simp
  exact ⟨le_of_pow_le_pow_left₀ (by decide) (gapRadius6_pos rho hp).le hlo,
    le_of_pow_le_pow_left₀ (by decide) (hp 5).le hhi⟩

theorem gapDeformation6_polynomial_bounds (rho : Fin 6 → ℝ) (hp : ∀ i, 0 < rho i)
    (hm : Monotone rho) (C K Q : ℝ) (hC : 0 < C) (hK : 0 < K) (hQ : 1 < Q)
    (hfirst : 1/(C*Q^(2 : ℕ)) ≤ rho 0) (hlast : rho 5 ≤ K*Q^(6 : ℕ)) :
    ∀ i, gapDeformation6 rho i ≤ C*K*Q^(8 : ℕ) ∧ (gapDeformation6 rho i)⁻¹ ≤ C*K*Q^(8 : ℕ) := by
  have hq : 0 < Q := lt_trans zero_lt_one hQ
  obtain ⟨hRlo,hRhi⟩ := gapRadius6_between rho hp hm
  have hf : 1 ≤ C*Q^(2 : ℕ)*rho 0 := by
    have hh := (div_le_iff₀ (by positivity : 0 < C*Q^(2 : ℕ))).mp hfirst
    nlinarith
  intro i
  have hmini : rho (min i 4) ≤ K*Q^(6 : ℕ) := (hm (by omega)).trans hlast
  have hR : gapRadius6 rho ≤ K*Q^(6 : ℕ) := hRhi.trans hlast
  have hi : 1 ≤ C*Q^(2 : ℕ)*rho (min i 4) :=
    hf.trans (mul_le_mul_of_nonneg_left (hm (by omega)) (by positivity))
  have h0 : 1 ≤ C*Q^(2 : ℕ)*gapRadius6 rho :=
    hf.trans (mul_le_mul_of_nonneg_left hRlo (by positivity))
  constructor
  · apply (div_le_iff₀ (hp (min i 4))).mpr
    calc
      _ ≤ K*Q^(6 : ℕ) := hR
      _ ≤ K*Q^(6 : ℕ)*(C*Q^(2 : ℕ)*rho (min i 4)) := by nlinarith [mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ K*Q^(6 : ℕ))]
      _ = _ := by ring
  · change (gapRadius6 rho / rho (min i 4))⁻¹ ≤ _
    rw [inv_div]
    apply (div_le_iff₀ (gapRadius6_pos rho hp)).mpr
    calc
      _ ≤ K*Q^(6 : ℕ) := hmini
      _ ≤ K*Q^(6 : ℕ)*(C*Q^(2 : ℕ)*gapRadius6 rho) := by nlinarith [mul_le_mul_of_nonneg_left h0 (by positivity : 0 ≤ K*Q^(6 : ℕ))]
      _ = _ := by ring

def davenportWidths42 (Q : ℝ) (c₀ : Fin 4 → ℝ) (d : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6)) : Fin 6 → ℝ :=
  fun s => (Q ^ c₀ (lo s)*Q ^ c₀ (hi s))/d (sigma s)

theorem davenportWidths42_bounds (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ)
    (hc : ∀ i, |c₀ i| ≤ 1) (rho : Fin 6 → ℝ) (hp : ∀ i, 0 < rho i) (hm : Monotone rho)
    (C K : ℝ) (hC : 0 < C) (hK : 0 < K)
    (hfirst : 1/(C*Q^(2 : ℕ)) ≤ rho 0) (hlast : rho 5 ≤ K*Q^(6 : ℕ))
    (sigma : Equiv.Perm (Fin 6)) :
    ∀ i, 0 < davenportWidths42 Q c₀ (gapDeformation6 rho) sigma i ∧
      davenportWidths42 Q c₀ (gapDeformation6 rho) sigma i ≤ C*K*Q^(10 : ℕ) ∧
      (davenportWidths42 Q c₀ (gapDeformation6 rho) sigma i)⁻¹ ≤ C*K*Q^(10 : ℕ) := by
  have hq : 0 < Q := lt_trans zero_lt_one hQ
  have hd := gapDeformation6_pos rho hp
  have hb := gapDeformation6_polynomial_bounds rho hp hm C K Q hC hK hQ hfirst hlast
  intro i
  have hw : 0 < Q ^ c₀ (lo i)*Q ^ c₀ (hi i) := mul_pos (Real.rpow_pos_of_pos hq _) (Real.rpow_pos_of_pos hq _)
  have harch : Q ^ c₀ (lo i)*Q ^ c₀ (hi i) ≤ Q^(2 : ℕ) := by
    rw [← Real.rpow_add hq]
    exact_mod_cast Real.rpow_le_rpow_of_exponent_le hQ.le
      (show c₀ (lo i)+c₀ (hi i) ≤ (2 : ℝ) by linarith [(abs_le.mp (hc (lo i))).2,(abs_le.mp (hc (hi i))).2])
  have hinv : (Q ^ c₀ (lo i)*Q ^ c₀ (hi i))⁻¹ ≤ Q^(2 : ℕ) := by
    rw [← Real.rpow_add hq,← Real.rpow_neg hq.le]
    exact_mod_cast Real.rpow_le_rpow_of_exponent_le hQ.le
      (show -(c₀ (lo i)+c₀ (hi i)) ≤ (2 : ℝ) by linarith [(abs_le.mp (hc (lo i))).1,(abs_le.mp (hc (hi i))).1])
  refine ⟨div_pos hw (hd _),?_,?_⟩
  · change (Q ^ c₀ (lo i)*Q ^ c₀ (hi i))/gapDeformation6 rho (sigma i) ≤ _
    rw [div_eq_mul_inv]
    have hh := mul_le_mul harch (hb (sigma i)).2 (inv_nonneg.mpr (hd _).le) (sq_nonneg Q)
    convert hh using 1 <;> ring
  · change ((Q ^ c₀ (lo i)*Q ^ c₀ (hi i))/gapDeformation6 rho (sigma i))⁻¹ ≤ _
    rw [inv_div,div_eq_mul_inv]
    have hh := mul_le_mul (hb (sigma i)).1 hinv (inv_nonneg.mpr hw.le) (by positivity : 0 ≤ C*K*Q^(8 : ℕ))
    convert hh using 1 <;> ring

theorem davenport_rescaled_power42 (Q c : ℝ) (hQ : 0 < Q) :
    (Q^(11 : ℕ))^(c/11) = Q^c := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hQ.le]
  congr 1
  ring

theorem davenport_rescaled_threshold42 (p : ℕ) (Q c : ℝ) :
    JSP000334.qThreshold p (Q^(11 : ℕ)) (c/11) = JSP000334.qThreshold p Q c := by
  unfold JSP000334.qThreshold
  rw [Real.log_pow]
  ring

theorem davenport_rescaled_group42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    directCompoundGroup42 A₂ A₃ (Q^(11 : ℕ)) (fun i => c₂ i/11) (fun i => c₃ i/11) =
      directCompoundGroup42 A₂ A₃ Q c₂ c₃ := by
  unfold directCompoundGroup42
  simp_rw [davenport_rescaled_threshold42]

theorem davenportWidths42_normalization (Q : ℝ) (hQ : 0 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (d : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6))
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) (hd : (∏ i, d i) = 1) :
    (∏ s, davenportWidths42 Q c₀ d sigma s *
      (Q^(11 : ℕ))^((c₂ (lo s)+c₂ (hi s))/11) *
      (Q^(11 : ℕ))^((c₃ (lo s)+c₃ (hi s))/11)) = 1 := by
  simp_rw [davenport_rescaled_power42 Q _ hQ]
  have he (s : Fin 6) : davenportWidths42 Q c₀ d sigma s * Q^(c₂ (lo s)+c₂ (hi s)) *
      Q^(c₃ (lo s)+c₃ (hi s)) =
      Q^(pairWeights42 c₀ s+pairWeights42 c₂ s+pairWeights42 c₃ s)/d (sigma s) := by
    unfold davenportWidths42 pairWeights42
    simp only [Real.rpow_add hQ]
    ring
  simp_rw [he]
  rw [Finset.prod_div_distrib,Equiv.prod_comp,hd,div_one,← Real.rpow_sum_of_pos hQ,
    pairWeights42_balance c₀ c₂ c₃ hb,Real.rpow_zero]

theorem davenportWidths42_coordinates (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (d : Fin 6 → ℝ)
    (sigma : Equiv.Perm (Fin 6)) (hd : ∀ i, 0 < d i)
    (hw : ∀ i, 0 < davenportWidths42 Q c₀ d sigma i) :
    weightedCoordinates6 (compoundFormEquiv42 L hL) (davenportWidths42 Q c₀ d sigma) hw =
      davenportCoordinates6 (compoundCoordinates42 L hL Q hQ c₀) d sigma hd := by
  ext x i
  rw [davenportCoordinates6_apply]
  change (compoundFormEquiv42 L hL x) i / ((Q^c₀ (lo i)*Q^c₀ (hi i))/d (sigma i)) =
    d (sigma i)*((compoundFormEquiv42 L hL x) i/(Q^c₀ (lo i)*Q^c₀ (hi i)))
  field_simp
  ring

theorem davenport_rescaled_minima42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (d : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6))
    (hd : ∀ i, 0 < d i) (hw : ∀ i, 0 < davenportWidths42 Q c₀ d sigma i) (j : Fin 6) :
    successiveRadius6 (directRealBasis42 A₂ A₃ (Q^(11 : ℕ)) (fun i => c₂ i/11) (fun i => c₃ i/11))
      (weightedCoordinates6 (compoundFormEquiv42 L hL) (davenportWidths42 Q c₀ d sigma) hw) j =
        directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ d sigma hd j := by
  simp only [successiveRadius6,directDavenportMinima42,directRealBasis42_span,
    davenport_rescaled_group42,davenportWidths42_coordinates L hL Q hQ c₀ d sigma hd hw]

theorem davenport_rescaled_small42 (Q delta x : ℝ) (hQ : 0 < Q) (hx : x < Q^(-delta/24)) :
    x < (Q^(11 : ℕ))^(-(delta/264)) := by
  have he : (Q^(11 : ℕ))^(-(delta/264)) = Q^(-delta/24) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hQ.le]
    congr 1
    ring
  rw [he]
  exact hx

def davenportRescaledDomain42 (U : Set ℝ) (C : ℝ) : Set ℝ :=
  (fun Q : ℝ => Q^(11 : ℕ)) '' {Q | Q ∈ U ∧ C < Q ∧ 1 < Q}

theorem davenportRescaledDomain42_unbounded (U : Set ℝ) (hU : ¬ BddAbove U) (C : ℝ) :
    ¬ BddAbove (davenportRescaledDomain42 U C) := by
  intro hbounded
  obtain ⟨B,hB⟩ := hbounded
  obtain ⟨Q,hQU,hQ⟩ := not_bddAbove_iff.mp hU (max (max C 1) B)
  have hC : C < Q := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have h1 : 1 < Q := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hBQ : B < Q := lt_of_le_of_lt (le_max_right _ _) hQ
  have hQQ : Q ≤ Q^(11 : ℕ) := by
    have hh := pow_le_pow_right₀ h1.le (by norm_num : (1 : ℕ) ≤ 11)
    simpa only [pow_one] using hh
  exact (not_lt_of_ge (hB (show Q^(11 : ℕ) ∈ davenportRescaledDomain42 U C from
    ⟨Q,⟨hQU,hC,h1⟩,rfl⟩))) (hBQ.trans_le hQQ)

def sourceAnalyticReady42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (delta : ℝ) (v : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃) : Prop :=
  let rho := directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let d := gapDeformation6 rho
  ∃ hd : ∀ i, 0 < d i, ∃ sigma : Equiv.Perm (Fin 6),
    ∃ hw : ∀ i, 0 < davenportWidths42 Q c₀ d sigma i,
      1 < Q^(11 : ℕ) ∧
      (∀ i : Fin 6, -1 ≤ (c₂ (lo i)+c₂ (hi i))/11 ∧ (c₂ (lo i)+c₂ (hi i))/11 ≤ 0) ∧
      (∀ i : Fin 6, -1 ≤ (c₃ (lo i)+c₃ (hi i))/11 ∧ (c₃ (lo i)+c₃ (hi i))/11 ≤ 0) ∧
      (∀ i, davenportWidths42 Q c₀ d sigma i < Q^(11 : ℕ) ∧
        (davenportWidths42 Q c₀ d sigma i)⁻¹ < Q^(11 : ℕ)) ∧
      (∏ i, davenportWidths42 Q c₀ d sigma i *
        (Q^(11 : ℕ))^((c₂ (lo i)+c₂ (hi i))/11) *
        (Q^(11 : ℕ))^((c₃ (lo i)+c₃ (hi i))/11)) = 1 ∧
      let b := directRealBasis42 A₂ A₃ (Q^(11 : ℕ)) (fun i => c₂ i/11) (fun i => c₃ i/11)
      let e := weightedCoordinates6 (compoundFormEquiv42 L hL) (davenportWidths42 Q c₀ d sigma) hw
      (∀ j, successiveRadius6 b e j = directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ d sigma hd j) ∧
      (∀ j : Fin 6, ∀ z : directCompoundGroup42 A₂ A₃ Q c₂ c₃,
        integerReal (z : Fin 6 → ℤ) ∉ minimaFlag6 (fun i => integerReal (v i : Fin 6 → ℤ)) j →
        d j*rho j/64 ≤ coordinateGauge6 e (integerReal (z : Fin 6 → ℤ))) ∧
      ∃ w : Fin 6 → directCompoundGroup42 A₂ A₃ (Q^(11 : ℕ)) (fun i => c₂ i/11) (fun i => c₃ i/11),
        LinearIndependent ℝ (fun i => integerReal (w i : Fin 6 → ℤ)) ∧
        (∀ j, coordinateGauge6 e (integerReal (w j : Fin 6 → ℤ)) = successiveRadius6 b e j) ∧
        successiveRadius6 b e 4 < (Q^(11 : ℕ))^(-(delta/264))

theorem source_uniform_analytic_ready42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    ∃ C K T : ℝ, 0 < C ∧ 0 < K ∧ 1 < T ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) →
        (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) → (∑ i, (c₀ i+c₂ i+c₃ i) = 0) → T < Q →
        ∀ v : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃,
          sourceDavenportDecay42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ delta v →
          1/(C*Q^(2 : ℕ)) ≤ directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 0 ∧
          directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 5 ≤ K*Q^(6 : ℕ) ∧
          (∀ sigma : Equiv.Perm (Fin 6), ∀ i,
            davenportWidths42 Q c₀ (gapDeformation6 (directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃)) sigma i ≤ C*K*Q^(10 : ℕ) ∧
            (davenportWidths42 Q c₀ (gapDeformation6 (directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃)) sigma i)⁻¹ ≤ C*K*Q^(10 : ℕ)) ∧
          sourceAnalyticReady42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ delta v := by
  obtain ⟨C,hC,hfirst⟩ := source_direct_first_lower42 L (sourceUnit42 L hL)
  obtain ⟨K,hK,hlast⟩ := source_direct_last_upper42 A₂ A₃ L (sourceUnit42 L hL)
  let T := max 2 (C*K)
  refine ⟨C,K,T,hC,hK,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Q hQ c₀ c₂ c₃ hc₀ hc₂ hc₃ hb hTQ v hdec
  let rho := directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
  obtain ⟨hp,hm⟩ := directMinima42_pos_mono A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
  have hf := hfirst A₂ A₃ Q hQ c₀ c₂ c₃ hc₀
  have hl := hlast Q hQ c₀ c₂ c₃ hc₀ hc₂ hc₃
  have hw := fun sigma => davenportWidths42_bounds Q hQ c₀ hc₀ rho hp hm C K hC hK hf hl sigma
  refine ⟨hf,hl,fun sigma i => ⟨(hw sigma i).2.1,(hw sigma i).2.2⟩,?_⟩
  obtain ⟨hdp,hprod,hanti,hscaled,sigma,hbounds,hvol,hsep,hupper,hsmall,w,hwi,hwp,hwm,hwatt⟩ := hdec
  have hW : ∀ i, 0 < davenportWidths42 Q c₀ (gapDeformation6 rho) sigma i := fun i => (hw sigma i).1
  dsimp only [sourceAnalyticReady42]
  refine ⟨hdp,sigma,hW,one_lt_pow₀ hQ (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    constructor <;> linarith [(hc₂ (lo i)).1,(hc₂ (lo i)).2,(hc₂ (hi i)).1,(hc₂ (hi i)).2]
  · intro i
    constructor <;> linarith [(hc₃ (lo i)).1,(hc₃ (lo i)).2,(hc₃ (hi i)).1,(hc₃ (hi i)).2]
  · intro i
    have hCK : C*K < Q := (le_max_right _ _).trans_lt hTQ
    have hbnd : C*K*Q^(10 : ℕ) < Q^(11 : ℕ) := by
      have hh := mul_lt_mul_of_pos_right hCK (pow_pos (lt_trans zero_lt_one hQ) 10)
      convert hh using 1 <;> ring
    exact ⟨((hw sigma i).2.1).trans_lt hbnd,((hw sigma i).2.2).trans_lt hbnd⟩
  · exact davenportWidths42_normalization Q (lt_trans zero_lt_one hQ) c₀ c₂ c₃ _ sigma hb hprod
  · exact davenport_rescaled_minima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ _ sigma hdp hW
  · intro j z hz
    rw [davenportWidths42_coordinates L (sourceUnit42 L hL) Q hQ c₀ _ sigma hdp hW]
    exact hsep j z hz
  · exact fun i => ⟨(w i : Fin 6 → ℤ),by rw [davenport_rescaled_group42]; exact (w i).property⟩
  · exact hwi
  · intro j
    rw [davenport_rescaled_minima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ _ sigma hdp hW j,
      davenportWidths42_coordinates L (sourceUnit42 L hL) Q hQ c₀ _ sigma hdp hW]
    exact hwatt j
  · rw [davenport_rescaled_minima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ _ sigma hdp hW 4]
    exact davenport_rescaled_small42 Q delta _ (lt_trans zero_lt_one hQ) hsmall

theorem source_compound_unbounded_analytic_ready42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    (∀ s t, IsAlgebraic ℚ (compound L s t)) ∧
    IsUnit (compound A₂) ∧ IsUnit (compound A₃) ∧ IsUnit (compound L) ∧
    ∃ κ C₄ C K T : ℝ, 0 < κ ∧ 0 < C₄ ∧ 0 < C ∧ 0 < K ∧ 1 < T ∧ (∀ Q : ℝ, T < Q → 12 / κ < Q ^ (delta / 2)) ∧
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
          ∃ (V : Set ℝ) (hVU : V ⊆ U), ¬ BddAbove V ∧ ¬ BddAbove (davenportRescaledDomain42 V T) ∧
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
                    (hQU t.val (hVU t.property)) c₀ c₂ c₃ delta (v t) ∧
                  1/(C*t.val^(2 : ℕ)) ≤ rho 0 ∧ rho 5 ≤ K*t.val^(6 : ℕ) ∧
                  (∀ sigma : Equiv.Perm (Fin 6), ∀ i,
                    davenportWidths42 t.val c₀ (gapDeformation6 rho) sigma i ≤ C*K*t.val^(10 : ℕ) ∧
                    (davenportWidths42 t.val c₀ (gapDeformation6 rho) sigma i)⁻¹ ≤ C*K*t.val^(10 : ℕ)) ∧
                  sourceAnalyticReady42 A₂ A₃ L (sourceUnit42 L hL) t.val
                    (hQU t.val (hVU t.property)) c₀ c₂ c₃ delta (v t) := by
  classical
  obtain ⟨halg,hu₂,hu₃,huL,κ,C₄,T₀,hk,hC₄,hT₀,hcut,hfamily⟩ :=
    source_compound_unbounded_davenport_decay42 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  obtain ⟨C,K,T₁,hC,hK,hT₁,hready⟩ := source_uniform_analytic_ready42 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  let T := max T₀ T₁
  have hT : 1 < T := hT₀.trans_le (le_max_left _ _)
  refine ⟨halg,hu₂,hu₃,huL,κ,C₄,C,K,T,hk,hC₄,hC,hK,hT,?_,?_⟩
  · intro Q hQ
    exact hcut Q ((le_max_left _ _).trans_lt hQ)
  · intro c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
    obtain ⟨hw₀,hw₂,hw₃,hwb,hF⟩ := hfamily c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
    refine ⟨hw₀,hw₂,hw₃,hwb,?_⟩
    intro U hUb hQU horiginal
    obtain ⟨V₀,hV₀U,hV₀b,u₀,v₀,hframes⟩ := hF U hUb hQU horiginal
    let V := {Q : ℝ | Q ∈ V₀ ∧ T < Q}
    have hVU : V ⊆ U := fun Q hQ => hV₀U hQ.1
    have hVb : ¬ BddAbove V := JSP000334.sourceDual_unbounded_tail3 V₀ hV₀b T
    let lift : V → V₀ := fun t => ⟨t.val,t.property.1⟩
    let u : (t : V) → Fin 4 → originalSourceGroup4 A₂ A₃ t.val c₂ c₃ := fun t => u₀ (lift t)
    let v : (t : V) → Fin 6 → directCompoundGroup42 A₂ A₃ t.val c₂ c₃ := fun t => v₀ (lift t)
    refine ⟨V,hVU,hVb,davenportRescaledDomain42_unbounded V hVb T,u,v,?_⟩
    intro t
    obtain ⟨_,hH,hD,hgap,hp,hprod,hroot,hdec⟩ := hframes (lift t)
    have hH' : sourceHyperplane42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property))
        c₀ c₂ c₃ κ (u t) (v t) := hH
    have hr := hready t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
      ((le_max_right _ _).trans_lt t.property.2) (v t) hdec
    exact ⟨t.property.2,hH',hD,hgap,hp,hprod,hroot,hdec,hr⟩

theorem davenport_rescaled_finite_cutoff42 (Q : ℝ) (hQ : 1 < Q) (c : Fin 4 → ℝ)
    (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 0) :
    ∀ i : Fin 6, (Q^(11 : ℕ))^(-((c (lo i)+c (hi i))/11)) < Q^(11 : ℕ) := by
  intro i
  have he : -((c (lo i)+c (hi i))/11) = (-(c (lo i)+c (hi i)))/11 := by ring
  rw [he,davenport_rescaled_power42 Q _ (lt_trans zero_lt_one hQ)]
  have hb : Q ^ (-(c (lo i)+c (hi i))) ≤ Q^(2 : ℕ) := by
    exact_mod_cast Real.rpow_le_rpow_of_exponent_le hQ.le
      (show -(c (lo i)+c (hi i)) ≤ (2 : ℝ) by linarith [(hc (lo i)).1,(hc (hi i)).1])
  exact hb.trans_lt (pow_lt_pow_right₀ hQ (by decide : (2 : ℕ) < 11))

end
end CompoundFeasibility
