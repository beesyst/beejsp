import SubspaceBridge.CompoundComparisonReverse42
open scoped BigOperators Matrix
namespace CompoundFeasibility

theorem sourcePairProducts42_top (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 =
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 1 * sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 3 ∧
    sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5 =
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 * sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 3 := by
  constructor <;> rfl

theorem source_summed_gap_bound42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (κ Q delta : ℝ) (hk : 0 < κ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hcompare : ∀ j, κ * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤
      sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j)
    (hgap : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 1 <
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 * Q ^ (-delta)) :
    sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 <
      (2 / κ) * sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5 * Q ^ (-delta) := by
  let mu := sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let nu := sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have hp := (sourceMinima4_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1
  have ht := sourcePairProducts42_top A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have hm : mu 4 < mu 5 * Q ^ (-delta) := by
    dsimp [mu]
    rw [ht.1,ht.2]
    convert mul_lt_mul_of_pos_right hgap (hp 3) using 1 <;> ring
  have hu : nu 4 ≤ 2 * mu 4 := source_compound_minima_upper42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4
  change nu 4 < (2 / κ) * nu 5 * Q ^ (-delta)
  calc
    _ ≤ 2 * mu 4 := hu
    _ < 2 * (mu 5 * Q ^ (-delta)) := mul_lt_mul_of_pos_left hm (by norm_num)
    _ = (2 / κ) * (κ * mu 5) * Q ^ (-delta) := by field_simp; ring
    _ ≤ (2 / κ) * nu 5 * Q ^ (-delta) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcompare 5) (by positivity))
        (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _).le

theorem compound_gap_cutoff42 (B delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ Q : ℝ, T < Q → B < Q ^ (delta / 2) := by
  obtain ⟨C,hC⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < delta / 2 by linarith)).eventually
      (Filter.eventually_gt_atTop B))
  refine ⟨max 2 C,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Q hQ
  exact hC Q (le_trans (le_max_right _ _) hQ.le)

theorem absorb_compound_gap42 (x y B Q delta : ℝ) (hy : 0 < y) (hQ : 1 < Q)
    (hcut : B < Q ^ (delta / 2)) (hgap : x < B * y * Q ^ (-delta)) :
    x < y * Q ^ (-delta / 2) := by
  have hq : 0 < Q := lt_trans zero_lt_one hQ
  have he : Q ^ (delta / 2) * Q ^ (-delta) = Q ^ (-delta / 2) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  calc
    _ < B * y * Q ^ (-delta) := hgap
    _ < Q ^ (delta / 2) * y * Q ^ (-delta) :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hcut hy) (Real.rpow_pos_of_pos hq _)
    _ = _ := by rw [mul_right_comm,he]; ring

noncomputable def directLocal42 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (a : Fin 4 → ℝ) : AddSubgroup (Fin 6 → ℤ) :=
  ⨅ s, (normBall p (Nat.ceil (a (lo s) + a (hi s)))).comap (row6 (compound A) s)

theorem normBall_antitone42 (p : ℕ) [hp : Fact p.Prime] (a b : ℕ) (h : a ≤ b) :
    normBall p b ≤ normBall p a := by
  intro x hx
  change padicNorm p x ≤ ((p : ℚ) ^ b)⁻¹ at hx
  change padicNorm p x ≤ ((p : ℚ) ^ a)⁻¹
  apply hx.trans
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  apply (inv_le_inv₀ (pow_pos hp0 _) (pow_pos hp0 _)).2
  exact pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le) h

theorem summed_le_directLocal42 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (a : Fin 4 → ℝ) :
    lattice6 p A (fun i => Nat.ceil (a i)) ≤ directLocal42 p A a := by
  intro x hx
  simp only [lattice6, directLocal42, AddSubgroup.mem_iInf, AddSubgroup.mem_comap] at hx ⊢
  intro s
  exact normBall_antitone42 p _ _ (Nat.ceil_add_le _ _) (hx s)

theorem six_norm2_42 : padicNorm 2 (6 : ℚ) = (2 : ℚ)⁻¹ := by
  have h : padicNorm 2 (3 : ℚ) = 1 := (padicNorm.nat_eq_one_iff 3).mpr (by decide)
  rw [show (6 : ℚ) = 2 * 3 by norm_num,padicNorm.mul,h,mul_one]
  exact padicNorm.padicNorm_p (by decide)

theorem six_norm3_42 : padicNorm 3 (6 : ℚ) = (3 : ℚ)⁻¹ := by
  have h : padicNorm 3 (2 : ℚ) = 1 := (padicNorm.nat_eq_one_iff 2).mpr (by decide)
  rw [show (6 : ℚ) = 3 * 2 by norm_num,padicNorm.mul,h,mul_one]
  exact padicNorm.padicNorm_p (by decide)

theorem padic_rpow_ceil42 (p : ℕ) [hp : Fact p.Prime]
    (Q c : ℝ) (hQ : 1 < Q) (hc : c ≤ 0) (x : ℚ) :
    (padicNorm p x : ℝ) ≤ Q ^ c ↔
      padicNorm p x ≤ ((p : ℚ) ^ Nat.ceil (JSP000334.qThreshold p Q c))⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by positivity
  have hQ0 : 0 < Q := lt_trans zero_lt_one hQ
  have ht := JSP000334.qThreshold_nonneg p hp.out.one_lt Q c hQ hc
  by_cases hx : x = 0
  · subst x
    simp only [padicNorm.zero, Rat.cast_zero]
    exact iff_of_true (by positivity) (by positivity)
  have he := padicNorm.eq_zpow_of_nonzero (p := p) hx
  have hcst : (padicNorm p x : ℝ) = (p : ℝ) ^ (-(padicValRat p x : ℤ)) := by
    simpa only [Rat.cast_zpow,Rat.cast_natCast] using congrArg (fun q : ℚ => (q : ℝ)) he
  have hr : Q ^ c = (p : ℝ) ^ (-JSP000334.qThreshold p Q c) := by
    rw [Real.rpow_neg (le_of_lt hp0), JSP000334.qThreshold_rpow p hp.out.one_lt Q c hQ,
      ← Real.rpow_neg hQ0.le, neg_neg]
  have hinv : (↑(((p : ℚ) ^ Nat.ceil (JSP000334.qThreshold p Q c))⁻¹) : ℝ) =
      (p : ℝ) ^ (-(Nat.ceil (JSP000334.qThreshold p Q c) : ℝ)) := by
    simp [Real.rpow_neg, Real.rpow_natCast]
  have hcast : (padicNorm p x ≤ ((p : ℚ) ^ Nat.ceil (JSP000334.qThreshold p Q c))⁻¹) ↔
      (padicNorm p x : ℝ) ≤ (((p : ℚ) ^ Nat.ceil (JSP000334.qThreshold p Q c))⁻¹ : ℚ) := by
    norm_cast
  rw [hcast]
  rw [hcst,hr,hinv,← Real.rpow_intCast, Real.rpow_le_rpow_left_iff hp1,
    Real.rpow_le_rpow_left_iff hp1]
  simp only [Int.cast_neg, neg_le_neg_iff]
  rw [natCast_ceil_eq_intCast_ceil ht]
  have hiff : Int.ceil (JSP000334.qThreshold p Q c) ≤ padicValRat p x ↔
      JSP000334.qThreshold p Q c ≤ (padicValRat p x : ℝ) := Int.ceil_le
  exact_mod_cast hiff.symm


theorem qThreshold_add42 (p : ℕ) (Q a b : ℝ) :
    JSP000334.qThreshold p Q (a + b) = JSP000334.qThreshold p Q a + JSP000334.qThreshold p Q b := by
  unfold JSP000334.qThreshold
  ring

theorem directLocal42_spec (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (a : Fin 4 → ℝ) (z : Fin 6 → ℤ) :
    z ∈ directLocal42 p A a ↔ ∀ s, padicNorm p ((compound A *ᵥ (fun t => (z t : ℚ))) s) ≤
      ((p : ℚ) ^ Nat.ceil (a (lo s) + a (hi s)))⁻¹ := by
  simp [directLocal42,AddSubgroup.mem_iInf,AddSubgroup.mem_comap,normBall,row6]

theorem directLocal42_raw (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (hQ : 1 < Q) (c : Fin 4 → ℝ)
    (hc : ∀ i, c i ≤ 0) (z : Fin 6 → ℤ) :
    z ∈ directLocal42 p A (fun i => JSP000334.qThreshold p Q (c i)) ↔
      ∀ s, (padicNorm p ((compound A *ᵥ (fun t => (z t : ℚ))) s) : ℝ) ≤ Q ^ (c (lo s) + c (hi s)) := by
  rw [directLocal42_spec]
  apply forall_congr'
  intro s
  rw [← qThreshold_add42]
  exact (padic_rpow_ceil42 p Q _ hQ (add_nonpos (hc _) (hc _)) _).symm

noncomputable def directCompoundGroup42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : AddSubgroup (Fin 6 → ℤ) :=
  directLocal42 2 A₂ (fun i => JSP000334.qThreshold 2 Q (c₂ i)) ⊓
    directLocal42 3 A₃ (fun i => JSP000334.qThreshold 3 Q (c₃ i))

theorem directCompoundGroup42_raw (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (hQ : 1 < Q) (c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) (z : Fin 6 → ℤ) :
    z ∈ directCompoundGroup42 A₂ A₃ Q c₂ c₃ ↔
      (∀ s, (padicNorm 2 ((compound A₂ *ᵥ (fun t => (z t : ℚ))) s) : ℝ) ≤ Q ^ (c₂ (lo s) + c₂ (hi s))) ∧
      (∀ s, (padicNorm 3 ((compound A₃ *ᵥ (fun t => (z t : ℚ))) s) : ℝ) ≤ Q ^ (c₃ (lo s) + c₃ (hi s))) := by
  change (z ∈ directLocal42 2 A₂ (fun i => JSP000334.qThreshold 2 Q (c₂ i))) ∧
    (z ∈ directLocal42 3 A₃ (fun i => JSP000334.qThreshold 3 Q (c₃ i))) ↔ _
  rw [directLocal42_raw 2 A₂ Q hQ c₂ hc₂,directLocal42_raw 3 A₃ Q hQ c₃ hc₃]

theorem summed_le_directCompoundGroup42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    compoundSourceGroup6 A₂ A₃ Q c₂ c₃ ≤ directCompoundGroup42 A₂ A₃ Q c₂ c₃ := by
  intro z hz
  exact ⟨summed_le_directLocal42 2 A₂ _ hz.1,summed_le_directLocal42 3 A₃ _ hz.2⟩

theorem directCompoundGroup42_multiple (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ j : Fin 6, Pi.single j D ∈ directCompoundGroup42 A₂ A₃ Q c₂ c₃ := by
  obtain ⟨D,hD,hm⟩ := sourceLattice6_multiple A₂ A₃
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
  exact ⟨D,hD,fun j => summed_le_directCompoundGroup42 A₂ A₃ Q c₂ c₃ (hm j)⟩

theorem directCompoundGroup42_has_basis (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : Nonempty (Basis (Fin 6) ℤ (directCompoundGroup42 A₂ A₃ Q c₂ c₃)) := by
  obtain ⟨D,hD,hm⟩ := directCompoundGroup42_multiple A₂ A₃ Q c₂ c₃
  exact integer_subgroup_has_basis _ D hD hm

instance directCompoundGroup42_isZLattice (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : IsZLattice ℝ (integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃)) where
  span_top := by
    obtain ⟨D,hD,hm⟩ := directCompoundGroup42_multiple A₂ A₃ Q c₂ c₃
    exact integerRealImage_span_top _ D hD hm

set_option maxHeartbeats 800000 in
theorem directLocal42_scale (p : ℕ) [hp : Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (a : Fin 4 → ℝ) (ha : ∀ i, 0 ≤ a i)
    (m : ℤ) (hm : padicNorm p (m : ℚ) ≤ (p : ℚ)⁻¹)
    (z : Fin 6 → ℤ) (hz : z ∈ directLocal42 p A a) :
    m • z ∈ lattice6 p A (fun i => Nat.ceil (a i)) := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  rw [directLocal42_spec] at hz
  apply (lattice6_spec p A (fun i => Nat.ceil (a i)) (m • z)).mpr
  intro s
  rw [zpow_neg,zpow_natCast]
  change padicNorm p (row6 (compound A) s (m • z)) ≤
    ((p : ℚ) ^ (Nat.ceil (a (lo s)) + Nat.ceil (a (hi s))))⁻¹
  have he : row6 (compound A) s (m • z) = (m : ℚ) * row6 (compound A) s z := by
    simpa only [zsmul_eq_mul] using (row6 (compound A) s).map_zsmul z m
  rw [he,padicNorm.mul]
  have hd := (ceil_pair_prime_powers p hp.out.one_le (a (lo s)) (a (hi s)) (ha _) (ha _)).2
  have hdQ : (p : ℚ) ^ (Nat.ceil (a (lo s)) + Nat.ceil (a (hi s))) ≤
      (p : ℚ) * (p : ℚ) ^ Nat.ceil (a (lo s) + a (hi s)) := by exact_mod_cast hd
  have hfirst : padicNorm p (m : ℚ) * padicNorm p (row6 (compound A) s z) ≤
      (p : ℚ)⁻¹ * ((p : ℚ) ^ Nat.ceil (a (lo s) + a (hi s)))⁻¹ :=
    mul_le_mul hm (hz s) (padicNorm.nonneg _) (inv_nonneg.mpr hp0.le)
  have hsecond : ((p : ℚ) * (p : ℚ) ^ Nat.ceil (a (lo s) + a (hi s)))⁻¹ ≤
      ((p : ℚ) ^ (Nat.ceil (a (lo s)) + Nat.ceil (a (hi s))))⁻¹ :=
    (inv_le_inv₀ (mul_pos hp0 (pow_pos hp0 _)) (pow_pos hp0 _)).mpr hdQ
  exact hfirst.trans (by simpa only [mul_inv] using hsecond)

theorem directCompoundGroup42_six_mem (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (hQ : 1 < Q) (c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (z : Fin 6 → ℤ) (hz : z ∈ directCompoundGroup42 A₂ A₃ Q c₂ c₃) :
    (6 : ℤ) • z ∈ compoundSourceGroup6 A₂ A₃ Q c₂ c₃ := by
  constructor
  · exact directLocal42_scale 2 A₂ _
      (fun i => JSP000334.qThreshold_nonneg 2 (by decide) Q (c₂ i) hQ (hc₂ i))
      6 six_norm2_42.le z hz.1
  · exact directLocal42_scale 3 A₃ _
      (fun i => JSP000334.qThreshold_nonneg 3 (by decide) Q (c₃ i) hQ (hc₃ i))
      6 six_norm3_42.le z hz.2


theorem directCompoundGroup42_real_lattice (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    DiscreteTopology (integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃)) ∧
      Submodule.span ℝ (integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃) : Set (Fin 6 → ℝ)) = ⊤ := by
  refine ⟨inferInstance,?_⟩
  obtain ⟨D,hD,hm⟩ := directCompoundGroup42_multiple A₂ A₃ Q c₂ c₃
  exact integerRealImage_span_top _ D hD hm

noncomputable def directRealBasis42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : Basis (Fin 6) ℝ (Fin 6 → ℝ) :=
  (integerRealImageBasis (directCompoundGroup42 A₂ A₃ Q c₂ c₃)
    (directCompoundGroup42_has_basis A₂ A₃ Q c₂ c₃).some).ofZLatticeBasis ℝ
      (integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃))

theorem directRealBasis42_span (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    lattice6Span (directRealBasis42 A₂ A₃ Q c₂ c₃) =
      integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃) :=
  Basis.ofZLatticeBasis_span ℝ (integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃))
    (integerRealImageBasis (directCompoundGroup42 A₂ A₃ Q c₂ c₃)
      (directCompoundGroup42_has_basis A₂ A₃ Q c₂ c₃).some)

noncomputable def directMinima42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) : ℝ :=
  sInf {r : ℝ | ∃ u : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ u ∧
    (∀ i, u i ∈ integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃)) ∧
    ∀ i, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (u i) ≤ r}

theorem directMinima42_eq_radius (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) :
    directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j =
      successiveRadius6 (directRealBasis42 A₂ A₃ Q c₂ c₃)
        (compoundCoordinates42 L hL Q hQ c₀) j := by
  simp only [directMinima42,successiveRadius6,directRealBasis42_span]

theorem exists_directMinima42_attaining (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    ∃ u : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃,
      LinearIndependent ℝ (fun j => integerReal (u j : Fin 6 → ℤ)) ∧
      (∀ j, 0 < directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃) ∧
      ∀ j, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀)
        (integerReal (u j : Fin 6 → ℤ)) = directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  classical
  let b := directRealBasis42 A₂ A₃ Q c₂ c₃
  let e := compoundCoordinates42 L hL Q hQ c₀
  obtain ⟨v,hv,hvL,hpos,hmono,hatt⟩ := exists_successive_minima6 b e
  have hrad (j : Fin 6) : directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j = successiveRadius6 b e j :=
    directMinima42_eq_radius A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
  have hvImage (j : Fin 6) : v j ∈ integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃) := by
    rw [← directRealBasis42_span A₂ A₃ Q c₂ c₃]
    exact hvL j
  have hlift (j : Fin 6) : ∃ x : directCompoundGroup42 A₂ A₃ Q c₂ c₃,
      integerReal (x : Fin 6 → ℤ) = v j := by
    obtain ⟨x,hx,he⟩ := hvImage j
    exact ⟨⟨x,hx⟩,he⟩
  choose u hu using hlift
  have hfun : (fun j => integerReal (u j : Fin 6 → ℤ)) = v := funext hu
  refine ⟨u,?_,?_,?_,?_⟩
  · rw [hfun]
    exact hv
  · intro j
    rw [hrad]
    exact hpos j
  · intro i j hij
    rw [hrad,hrad]
    exact hmono hij
  · intro j
    rw [hu j,hrad]
    exact hatt j

theorem directMinima42_pos_mono (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    (∀ j, 0 < directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃) := by
  obtain ⟨_,_,hp,hm,_⟩ := exists_directMinima42_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  exact ⟨hp,hm⟩

theorem directMinima42_admissible (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) :
    ∃ v : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (v i) ≤
        directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  obtain ⟨u,hu,_,hmono,hatt⟩ := exists_directMinima42_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let f : Fin (j.val+1) → Fin 6 := Fin.castLE (by omega)
  refine ⟨fun i => integerReal (u (f i) : Fin 6 → ℤ),
    hu.comp f (Fin.castLE_injective _),?_,?_⟩
  · intro i
    exact ⟨(u (f i) : Fin 6 → ℤ),(u (f i)).property,rfl⟩
  · intro i
    rw [hatt]
    exact hmono (show f i ≤ j from (by change i.val ≤ j.val; omega))

theorem directMinima42_radius_set_properties (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) :
    let S := {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (v i) ≤ r}
    S.Nonempty ∧ BddBelow S ∧ IsLeast S (directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) := by
  dsimp only
  have hm := directMinima42_admissible A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
  have hne : ({r : ℝ | ∃ v : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (v i) ≤ r}).Nonempty := ⟨_,hm⟩
  have hb : BddBelow {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (v i) ≤ r} := by
    refine ⟨0,?_⟩
    rintro r ⟨v,_,_,hv⟩
    exact (norm_nonneg _).trans (hv 0)
  refine ⟨hne,hb,hm,?_⟩
  intro r hr
  exact csInf_le hb hr

theorem directMinima42_comparison (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    ∀ j : Fin 6,
      directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤ sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ∧
      sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤ 6 * directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  intro j
  constructor
  · obtain ⟨v,hv,hm,hb⟩ := sourceMinima6_admissible A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
    apply (directMinima42_radius_set_properties A₂ A₃ L hL Q hQ c₀ c₂ c₃ j).2.2.2
    refine ⟨v,hv,?_,hb⟩
    intro i
    obtain ⟨z,hz,he⟩ := hm i
    exact ⟨z,summed_le_directCompoundGroup42 A₂ A₃ Q c₂ c₃ hz,he⟩
  · obtain ⟨v,hv,hm,hb⟩ := directMinima42_admissible A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
    apply (sourceMinima6_radius_set_properties A₂ A₃ L hL Q hQ c₀ c₂ c₃ j).2.2.2
    have hi := hv.units_smul (fun _ => Units.mk0 (6 : ℝ) (by norm_num))
    change LinearIndependent ℝ (fun i => (6 : ℝ) • v i) at hi
    refine ⟨fun i => (6 : ℝ) • v i,hi,?_,?_⟩
    · intro i
      obtain ⟨z,hz,he⟩ := hm i
      refine ⟨(6 : ℤ) • z,directCompoundGroup42_six_mem A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ z hz,?_⟩
      change integerReal ((6 : ℤ) • z) = (6 : ℝ) • v i
      rw [← he]
      ext s
      simp [integerReal,Pi.smul_apply,zsmul_eq_mul]
    · intro i
      simp only [coordinateGauge6,map_smul,norm_smul,Real.norm_eq_abs,
        show |(6 : ℝ)| = 6 from by norm_num]
      exact mul_le_mul_of_nonneg_left (hb i) (by norm_num)

theorem source_direct_gap_bound42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (κ Q delta : ℝ) (hk : 0 < κ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hcompare : ∀ j, κ * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤
      sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j)
    (hgap : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 1 <
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 * Q ^ (-delta)) :
    directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 <
      (12 / κ) * directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5 * Q ^ (-delta) := by
  have hc := directMinima42_comparison A₂ A₃ L hL Q hQ c₀ c₂ c₃ hc₂ hc₃
  calc
    _ ≤ sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 := (hc 4).1
    _ < (2 / κ) * sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5 * Q ^ (-delta) :=
      source_summed_gap_bound42 A₂ A₃ L hL κ Q delta hk hQ c₀ c₂ c₃ hcompare hgap
    _ ≤ (2 / κ) * (6 * directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5) * Q ^ (-delta) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hc 5).2 (by positivity))
        (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _).le
    _ = _ := by ring

theorem source_uniform_direct_gap42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ κ T : ℝ, 0 < κ ∧ 1 < T ∧
      (∀ Q : ℝ, T < Q → 12 / κ < Q ^ (delta / 2)) ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) →
        (∑ i, (c₀ i + c₂ i + c₃ i) = 0) → T < Q →
        sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 1 <
          sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 * Q ^ (-delta) →
        directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 <
          (12 / κ) * directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5 * Q ^ (-delta) ∧
        directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 <
          directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5 * Q ^ (-delta / 2) := by
  obtain ⟨_,_,κ,_,_,hk,_,hcomp⟩ := source_compound_uniform_comparison42 A₂ A₃ L h₂ h₃ hL
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 (12 / κ) delta hd
  refine ⟨κ,T,hk,hT,hcut,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb hTQ hgap
  have hbound := source_direct_gap_bound42 A₂ A₃ L hL κ Q delta hk hQ c₀ c₂ c₃ hc₂ hc₃
    (fun j => (hcomp Q hQ c₀ c₂ c₃ hc₂ hc₃ hb j).1) hgap
  refine ⟨hbound,?_⟩
  exact absorb_compound_gap42 _ _ (12 / κ) Q delta
    ((directMinima42_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1 5)
    hQ (hcut Q hTQ) hbound

end CompoundFeasibility
