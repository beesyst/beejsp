import SubspaceBridge.Exterior3Minima4
open scoped BigOperators Matrix
open CompoundFeasibility.Exterior3
namespace CompoundFeasibility.Exterior3NormalizationLiteral183
noncomputable section

def normalizedWeights3_4 (c : Fin 4 → ℝ) : Fin 4 → ℝ := fun s => tripleWeights4 c s/3

theorem cube_gt_one3 (Q : ℝ) (hQ : 1 < Q) : 1 < Q^(3 : ℕ) :=
  one_lt_pow₀ hQ (by decide)

theorem normalizedWeights3_conditions (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₀ : ∀ i, |c₀ i| ≤ 1) (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0)
    (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) :
    (∀ s, |normalizedWeights3_4 c₀ s| ≤ 1) ∧
    (∀ s, -1 ≤ normalizedWeights3_4 c₂ s ∧ normalizedWeights3_4 c₂ s ≤ 0) ∧
    (∀ s, -1 ≤ normalizedWeights3_4 c₃ s ∧ normalizedWeights3_4 c₃ s ≤ 0) ∧
    (∑ s, (normalizedWeights3_4 c₀ s+normalizedWeights3_4 c₂ s+normalizedWeights3_4 c₃ s) = 0) := by
  obtain ⟨h₀,h₂,h₃⟩ := tripleWeights4_bounds c₀ c₂ c₃ hc₀ hc₂ hc₃
  refine ⟨?_,?_,?_,?_⟩
  · intro s
    dsimp [normalizedWeights3_4]
    rw [abs_div,show |(3 : ℝ)| = 3 by norm_num]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr (by simpa using h₀ s)
  · intro s
    dsimp [normalizedWeights3_4]
    constructor <;> linarith [(h₂ s).1,(h₂ s).2]
  · intro s
    dsimp [normalizedWeights3_4]
    constructor <;> linarith [(h₃ s).1,(h₃ s).2]
  · calc
      _ = (∑ s, (tripleWeights4 c₀ s+tripleWeights4 c₂ s+tripleWeights4 c₃ s))/3 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro s _
        dsimp [normalizedWeights3_4]
        ring
      _ = 0 := by rw [tripleWeights4_balance c₀ c₂ c₃ hb,zero_div]

theorem normalized_power3 (Q : ℝ) (hQ : 0 < Q) (c : Fin 4 → ℝ) (s : Fin 4) :
    (Q^(3 : ℕ))^normalizedWeights3_4 c s = Q^tripleWeights4 c s := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hQ.le]
  congr 1
  dsimp [normalizedWeights3_4]
  ring

theorem normalized_threshold3 (p : ℕ) (Q : ℝ) (c : Fin 4 → ℝ) (s : Fin 4) :
    JSP000334.qThreshold p (Q^(3 : ℕ)) (normalizedWeights3_4 c s) =
      JSP000334.qThreshold p Q (tripleWeights4 c s) := by
  unfold JSP000334.qThreshold normalizedWeights3_4
  rw [Real.log_pow]
  ring

def directExponents3_4 (p : ℕ) (Q : ℝ) (c : Fin 4 → ℝ) : Fin 4 → ℕ :=
  originalExponents3_4 p (Q^(3 : ℕ)) (normalizedWeights3_4 c)

theorem direct_summed_exponents3 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q)
    (c : Fin 4 → ℝ) (hc : ∀ i, c i ≤ 0) (s : Fin 4) :
    directExponents3_4 p Q c s ≤ summedExponents3_4 p Q c s ∧
      summedExponents3_4 p Q c s ≤ directExponents3_4 p Q c s+2 := by
  simp only [directExponents3_4,originalExponents3_4,normalized_threshold3]
  exact source_triple_rounding4 p hp Q hQ c hc s

def normalizedGroup3_4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : AddSubgroup (Fin 4 → ℤ) :=
  originalSourceGroup4 (compound3Matrix4 A₂) (compound3Matrix4 A₃) (Q^(3 : ℕ))
    (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃)

theorem normalized_group3_eq (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    normalizedGroup3_4 A₂ A₃ Q c₂ c₃ = sourceLattice4 (compound3Matrix4 A₂) (compound3Matrix4 A₃)
      (directExponents3_4 2 Q c₂) (directExponents3_4 3 Q c₃) := rfl

theorem lattice4_antitone3 (p : ℕ) [Fact p.Prime] (B : Matrix (Fin 4) (Fin 4) ℚ)
    (d e : Fin 4 → ℕ) (hde : ∀ i, d i ≤ e i) : lattice4 p B e ≤ lattice4 p B d := by
  intro x hx
  simp only [lattice4,AddSubgroup.mem_iInf,AddSubgroup.mem_comap] at hx ⊢
  intro i
  exact normBall_antitone42 p (d i) (e i) (hde i) (hx i)

theorem summed_le_normalized_group3 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (hQ : 1 < Q) (c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃ ≤ normalizedGroup3_4 A₂ A₃ Q c₂ c₃ := by
  rw [compound_group3_eq,normalized_group3_eq]
  intro x hx
  exact ⟨lattice4_antitone3 2 _ _ _ (fun i => (direct_summed_exponents3 2 (by decide) Q hQ c₂ hc₂ i).1) hx.1,
    lattice4_antitone3 3 _ _ _ (fun i => (direct_summed_exponents3 3 (by decide) Q hQ c₃ hc₃ i).1) hx.2⟩

theorem thirtysix_norm2_3 : padicNorm 2 (36 : ℚ) = ((2 : ℚ)^2)⁻¹ := by
  rw [show (36 : ℚ) = 6*6 by norm_num,padicNorm.mul,six_norm2_42]
  norm_num

theorem thirtysix_norm3_3 : padicNorm 3 (36 : ℚ) = ((3 : ℚ)^2)⁻¹ := by
  rw [show (36 : ℚ) = 6*6 by norm_num,padicNorm.mul,six_norm3_42]
  norm_num

theorem lattice4_scale_loss2_3 (p : ℕ) [hp : Fact p.Prime] (B : Matrix (Fin 4) (Fin 4) ℚ)
    (d e : Fin 4 → ℕ) (hE : ∀ i, e i ≤ d i+2) (m : ℤ)
    (hm : padicNorm p (m : ℚ) ≤ ((p : ℚ)^2)⁻¹) (x : Fin 4 → ℤ) (hx : x ∈ lattice4 p B d) :
    m • x ∈ lattice4 p B e := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_le
  simp only [lattice4,AddSubgroup.mem_iInf,AddSubgroup.mem_comap] at hx ⊢
  change (∀ i, padicNorm p (row4 B i x) ≤ ((p : ℚ)^d i)⁻¹) at hx
  change ∀ i, padicNorm p (row4 B i (m • x)) ≤ ((p : ℚ)^e i)⁻¹
  intro i
  have he : row4 B i (m • x) = (m : ℚ)*row4 B i x := by
    simpa only [zsmul_eq_mul] using (row4 B i).map_zsmul x m
  rw [he,padicNorm.mul]
  calc
    _ ≤ ((p : ℚ)^2)⁻¹ * ((p : ℚ)^d i)⁻¹ :=
      mul_le_mul hm (hx i) (padicNorm.nonneg _) (inv_nonneg.mpr (pow_nonneg hp0.le _))
    _ = ((p : ℚ)^(d i+2))⁻¹ := by rw [pow_add,mul_inv]; ring
    _ ≤ ((p : ℚ)^e i)⁻¹ :=
      (inv_le_inv₀ (pow_pos hp0 _) (pow_pos hp0 _)).mpr (pow_le_pow_right₀ hp1 (hE i))

theorem normalized_thirtysix_mem3 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (hQ : 1 < Q) (c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (x : Fin 4 → ℤ) (hx : x ∈ normalizedGroup3_4 A₂ A₃ Q c₂ c₃) :
    (36 : ℤ) • x ∈ originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃ := by
  rw [normalized_group3_eq] at hx
  rw [compound_group3_eq]
  exact ⟨lattice4_scale_loss2_3 2 _ _ _ (fun i => (direct_summed_exponents3 2 (by decide) Q hQ c₂ hc₂ i).2)
    36 thirtysix_norm2_3.le x hx.1,
    lattice4_scale_loss2_3 3 _ _ _ (fun i => (direct_summed_exponents3 3 (by decide) Q hQ c₃ hc₃ i).2)
    36 thirtysix_norm3_3.le x hx.2⟩
theorem normalized_coordinates3_eq (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) :
    originalCoordinates4 (compound3Matrix4 L) (compound3_unit L hL)
      (Q^(3 : ℕ)) (cube_gt_one3 Q hQ) (normalizedWeights3_4 c₀) = compoundCoordinates3_4 L hL Q hQ c₀ := by
  ext x i
  change (compound3Matrix4 L *ᵥ x) i / (Q^(3 : ℕ))^normalizedWeights3_4 c₀ i =
    (compound3Matrix4 L *ᵥ x) i / Q^tripleWeights4 c₀ i
  rw [normalized_power3 Q (lt_trans zero_lt_one hQ)]

theorem normalized_body3_eq (L : Matrix (Fin 4) (Fin 4) ℝ)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) :
    originalBody4 (compound3Matrix4 L) (Q^(3 : ℕ)) (normalizedWeights3_4 c₀) =
      originalBody4 (compound3Matrix4 L) Q (tripleWeights4 c₀) := by
  ext x
  simp only [originalBody4,Set.mem_setOf_eq,normalized_power3 Q (lt_trans zero_lt_one hQ)]

def normalizedMinima3_4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) : Fin 4 → ℝ :=
  sourceMinima4 (compound3Matrix4 A₂) (compound3Matrix4 A₃) (compound3Matrix4 L) (compound3_unit L hL)
    (Q^(3 : ℕ)) (cube_gt_one3 Q hQ) (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃)

theorem coordinateGauge4_thirtysix3 (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (x : Fin 4 → ℝ) :
    coordinateGauge4 e ((36 : ℝ) • x) = 36*coordinateGauge4 e x := by
  simp only [coordinateGauge4,map_smul,norm_smul,Real.norm_eq_abs,show |(36 : ℝ)| = 36 by norm_num]

theorem integerReal_thirtysix3 (x : Fin 4 → ℤ) :
    integerReal ((36 : ℤ) • x) = (36 : ℝ) • integerReal x := by
  ext i
  simp [integerReal,Pi.smul_apply,zsmul_eq_mul]

theorem compoundMinima3_prefix_admissible (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 4) :
    ∃ v : Fin (j.val+1) → (Fin 4 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge4 (compoundCoordinates3_4 L hL Q hQ c₀) (v i) ≤
        compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  obtain ⟨u,hu,_,hmono,hatt,_⟩ := exists_compoundMinima3_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let f : Fin (j.val+1) → Fin 4 := Fin.castLE (by omega)
  refine ⟨(fun k => integerReal (u k : Fin 4 → ℤ)) ∘ f,hu.comp f (Fin.castLE_injective _),?_,?_⟩
  · intro i
    exact ⟨(u (f i) : Fin 4 → ℤ),(u (f i)).property,rfl⟩
  · intro i
    exact (hatt (f i)).le.trans (hmono (show f i ≤ j from (by change i.val ≤ j.val; omega)))

theorem normalized_minima3_comparison (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    ∀ j, normalizedMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤ compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ∧
      compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤ 36*normalizedMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  intro j
  constructor
  · obtain ⟨v,hv,hm,hb⟩ := compoundMinima3_prefix_admissible A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
    apply (sourceMinima4_radius_set_properties (compound3Matrix4 A₂) (compound3Matrix4 A₃)
      (compound3Matrix4 L) (compound3_unit L hL) (Q^(3 : ℕ)) (cube_gt_one3 Q hQ)
      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) j).2.2.2
    refine ⟨v,hv,?_,?_⟩
    · intro i
      obtain ⟨z,hz,he⟩ := hm i
      exact ⟨z,summed_le_normalized_group3 A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ hz,he⟩
    · intro i
      rw [normalized_coordinates3_eq]
      exact hb i
  · obtain ⟨v,hv,hm,hb⟩ := sourceMinima4_admissible (compound3Matrix4 A₂) (compound3Matrix4 A₃)
      (compound3Matrix4 L) (compound3_unit L hL) (Q^(3 : ℕ)) (cube_gt_one3 Q hQ)
      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) j
    have hi := hv.units_smul (fun _ => Units.mk0 (36 : ℝ) (by norm_num))
    change LinearIndependent ℝ (fun i => (36 : ℝ) • v i) at hi
    apply successiveRadius4_le_family (compoundBasis3_4 A₂ A₃ Q c₂ c₃) (compoundCoordinates3_4 L hL Q hQ c₀)
      j (fun i => (36 : ℝ) • v i) hi
    · intro i
      rw [compoundBasis3_span]
      obtain ⟨z,hz,he⟩ := hm i
      refine ⟨(36 : ℤ) • z,normalized_thirtysix_mem3 A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ z hz,?_⟩
      rw [integerReal_thirtysix3,he]
    · intro i
      rw [coordinateGauge4_thirtysix3]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hh : coordinateGauge4 (originalCoordinates4 (compound3Matrix4 L) (compound3_unit L hL)
          (Q^(3 : ℕ)) (cube_gt_one3 Q hQ) (normalizedWeights3_4 c₀)) (v i) ≤
          normalizedMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := hb i
      rw [normalized_coordinates3_eq L hL Q hQ c₀] at hh
      exact hh

theorem normalizedMinima3_pos_mono (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    (∀ j, 0 < normalizedMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (normalizedMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) :=
  sourceMinima4_pos_mono (compound3Matrix4 A₂) (compound3Matrix4 A₃) (compound3Matrix4 L) (compound3_unit L hL)
    (Q^(3 : ℕ)) (cube_gt_one3 Q hQ) (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃)

theorem normalized_gap_power3 (Q : ℝ) (hQ : 0 < Q) (delta : ℝ) :
    Q^(-delta/4) = (Q^(3 : ℕ))^(-delta/12) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hQ.le]
  congr 1
  ring

theorem normalized_top_gap3 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (delta : ℝ) (hcut : 36 < Q^(delta/4))
    (hgap : compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 <
      compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 3*Q^(-delta/2)) :
    normalizedMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 <
      normalizedMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 3*(Q^(3 : ℕ))^(-delta/12) := by
  let nuD := normalizedMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have hc := normalized_minima3_comparison A₂ A₃ L hL Q hQ c₀ c₂ c₃ hc₂ hc₃
  have hraw : nuD 2 < 36*nuD 3*Q^(-delta/2) := by
    calc
      _ ≤ compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 := (hc 2).1
      _ < compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 3*Q^(-delta/2) := hgap
      _ ≤ _ := mul_le_mul_of_nonneg_right (hc 3).2 (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _).le
  have hcut' : 36 < Q^((delta/2)/2) := by
    simpa only [div_div,show (2 : ℝ)*2 = 4 by norm_num] using hcut
  have hraw' : nuD 2 < 36*nuD 3*Q^(-(delta/2)) := by simpa only [neg_div] using hraw
  have h := absorb_compound_gap42 (nuD 2) (nuD 3) 36 Q (delta/2)
    ((normalizedMinima3_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1 3) hQ hcut' hraw'
  rw [show -(delta/2)/2 = -delta/4 by ring,normalized_gap_power3 Q (lt_trans zero_lt_one hQ)] at h
  exact h

theorem normalization_cutoff3 (delta : ℝ) (hd : 0 < delta) (Told : ℝ) :
    ∃ T : ℝ, 1 < T ∧ Told ≤ T ∧ ∀ Q : ℝ, T < Q → 36 < Q^(delta/4) := by
  obtain ⟨S,hS,hcut⟩ := compound_gap_cutoff42 36 (delta/2) (by linarith)
  refine ⟨max Told S,hS.trans_le (le_max_right _ _),le_max_left _ _,?_⟩
  intro Q hQ
  simpa only [div_div,show (2 : ℝ)*2 = 4 by norm_num] using hcut Q ((le_max_right _ _).trans_lt hQ)

def cubeImage3_4 (V : Set ℝ) : Set ℝ := {R | ∃ Q ∈ V, R = Q^(3 : ℕ)}

theorem cubeImage3_unbounded (V : Set ℝ) (hV : ¬ BddAbove V) : ¬ BddAbove (cubeImage3_4 V) := by
  apply not_bddAbove_iff.mpr
  intro B
  obtain ⟨Q,hQV,hQB⟩ := not_bddAbove_iff.mp hV (max B 1)
  have hQ1 : 1 < Q := (le_max_right _ _).trans_lt hQB
  refine ⟨Q^(3 : ℕ),⟨Q,hQV,rfl⟩,?_⟩
  exact ((le_max_left _ _).trans_lt hQB).trans_le (le_self_pow₀ hQ1.le (by decide))

def normalizationTransport3_4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) : Prop :=
  originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃ = sourceLattice4 (compound3Matrix4 A₂) (compound3Matrix4 A₃)
    (summedExponents3_4 2 Q c₂) (summedExponents3_4 3 Q c₃) ∧
  normalizedGroup3_4 A₂ A₃ Q c₂ c₃ = sourceLattice4 (compound3Matrix4 A₂) (compound3Matrix4 A₃)
    (directExponents3_4 2 Q c₂) (directExponents3_4 3 Q c₃) ∧
  originalBody4 (compound3Matrix4 L) (Q^(3 : ℕ)) (normalizedWeights3_4 c₀) =
    originalBody4 (compound3Matrix4 L) Q (tripleWeights4 c₀) ∧
  originalCoordinates4 (compound3Matrix4 L) (compound3_unit L hL) (Q^(3 : ℕ)) (cube_gt_one3 Q hQ)
    (normalizedWeights3_4 c₀) = compoundCoordinates3_4 L hL Q hQ c₀ ∧
  (∀ s, JSP000334.qThreshold 2 (Q^(3 : ℕ)) (normalizedWeights3_4 c₂ s) =
    JSP000334.qThreshold 2 Q (tripleWeights4 c₂ s) ∧
    directExponents3_4 2 Q c₂ s ≤ summedExponents3_4 2 Q c₂ s ∧
    summedExponents3_4 2 Q c₂ s ≤ directExponents3_4 2 Q c₂ s+2) ∧
  (∀ s, JSP000334.qThreshold 3 (Q^(3 : ℕ)) (normalizedWeights3_4 c₃ s) =
    JSP000334.qThreshold 3 Q (tripleWeights4 c₃ s) ∧
    directExponents3_4 3 Q c₃ s ≤ summedExponents3_4 3 Q c₃ s ∧
    summedExponents3_4 3 Q c₃ s ≤ directExponents3_4 3 Q c₃ s+2) ∧
  originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃ ≤ normalizedGroup3_4 A₂ A₃ Q c₂ c₃ ∧
  (∀ x ∈ normalizedGroup3_4 A₂ A₃ Q c₂ c₃, (36 : ℤ) • x ∈ originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃) ∧
  ∀ j, normalizedMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤ compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ∧
    compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤ 36*normalizedMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j

theorem source_normalizationTransport3 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    normalizationTransport3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ := by
  refine ⟨compound_group3_eq A₂ A₃ Q c₂ c₃,normalized_group3_eq A₂ A₃ Q c₂ c₃,
    normalized_body3_eq L Q hQ c₀,normalized_coordinates3_eq L hL Q hQ c₀,?_,?_,
    summed_le_normalized_group3 A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃,
    fun x hx => normalized_thirtysix_mem3 A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ x hx,
    normalized_minima3_comparison A₂ A₃ L hL Q hQ c₀ c₂ c₃ hc₂ hc₃⟩
  · intro s
    exact ⟨normalized_threshold3 2 Q c₂ s,direct_summed_exponents3 2 (by decide) Q hQ c₂ hc₂ s⟩
  · intro s
    exact ⟨normalized_threshold3 3 Q c₃ s,direct_summed_exponents3 3 (by decide) Q hQ c₃ hc₃ s⟩

theorem source_exterior3_normalized_gap4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    let B₂ := compound3Matrix4 A₂
    let B₃ := compound3Matrix4 A₃
    let B₀ := compound3Matrix4 L
    let hBdet : B₀.det = 1 := by dsimp [B₀]; rw [compound3_det,hL,one_pow]
    let hBunit := sourceUnit42 B₀ hBdet
    ∃ Told T : ℝ, 1 < Told ∧ 1 < T ∧ Told ≤ T ∧ 0 < delta/12 ∧
      (∀ Q : ℝ, T < Q → 36 < Q^(delta/4)) ∧
      B₂.det = 1 ∧ B₃.det = 1 ∧ B₀.det = 1 ∧ IsUnit B₂ ∧ IsUnit B₃ ∧ IsUnit B₀ ∧
      (∀ s t, IsAlgebraic ℚ (B₀ s t)) ∧
      ∀ (c₀ c₂ c₃ : Fin 4 → ℝ) (_hc₀ : ∀ i, |c₀ i| ≤ 1)
        (_hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (_hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
        (_hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0),
        (∀ s, |normalizedWeights3_4 c₀ s| ≤ 1) ∧
        (∀ s, -1 ≤ normalizedWeights3_4 c₂ s ∧ normalizedWeights3_4 c₂ s ≤ 0) ∧
        (∀ s, -1 ≤ normalizedWeights3_4 c₃ s ∧ normalizedWeights3_4 c₃ s ≤ 0) ∧
        (∑ s, (normalizedWeights3_4 c₀ s+normalizedWeights3_4 c₂ s+normalizedWeights3_4 c₃ s) = 0) ∧
        ∀ (U : Set ℝ) (_hU : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q),
          (∀ (Q : ℝ) (hq : Q ∈ U), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ 0 <
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ 1*Q^(-delta)) →
          ∃ (V : Set ℝ) (hVU : V ⊆ U), V = {Q | Q ∈ U ∧ Told < Q} ∧ ¬ BddAbove V ∧
            ∃ u : (q : V) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
              (∀ q : V, originalFrameControl3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                (hQU q.val (hVU q.property)) c₀ c₂ c₃ (u q) ∧ Told < q.val ∧
                compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ 2 <
                  compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ 3*q.val^(-delta/2)) ∧
              ∃ (Vprime : Set ℝ) (hVpV : Vprime ⊆ V), Vprime = {Q | Q ∈ V ∧ T < Q} ∧ ¬ BddAbove Vprime ∧
                ∃ (W : Set ℝ) (hWR : ∀ R ∈ W, 1 < R), W = cubeImage3_4 Vprime ∧ ¬ BddAbove W ∧
                  (∀ q : Vprime,
                    normalizationTransport3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                      (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ ∧
                    (∀ s, tripleFrame4 (fun j => (u ⟨q.val,hVpV q.property⟩ j : Fin 4 → ℤ)) s ∈
                      normalizedGroup3_4 A₂ A₃ q.val c₂ c₃) ∧
                    normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                      (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ 2 <
                      normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                        (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ 3*(q.val^(3 : ℕ))^(-delta/12)) ∧
                  ∀ (R : ℝ) (hR : R ∈ W), ∃ q : Vprime, R = q.val^(3 : ℕ) ∧
                    sourceMinima4 B₂ B₃ B₀ hBunit R (hWR R hR)
                      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) 2 <
                    sourceMinima4 B₂ B₃ B₀ hBunit R (hWR R hR)
                      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) 3*R^(-delta/12) := by
  classical
  dsimp only
  let hLu := sourceUnit42 L hL
  obtain ⟨_,_,Told,_,_,hTold,_,_,_,htails⟩ := source_exterior3_top_gap4 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  obtain ⟨T,hT,hTT,hcut⟩ := normalization_cutoff3 delta hd Told
  refine ⟨Told,T,hTold,hT,hTT,by linarith,hcut,?_,?_,?_,
    compound3_unit A₂ (sourceUnit42 A₂ h₂),compound3_unit A₃ (sourceUnit42 A₃ h₃),
    compound3_unit L hLu,compound3_algebraic L hAlg,?_⟩
  · rw [compound3_det,h₂,one_pow]
  · rw [compound3_det,h₃,one_pow]
  · rw [compound3_det,hL,one_pow]
  · intro c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
    obtain ⟨ha₀,ha₂,ha₃,hab⟩ := normalizedWeights3_conditions c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
    refine ⟨ha₀,ha₂,ha₃,hab,?_⟩
    intro U hU hQU hgap
    obtain ⟨V,hVU,hVeq,hV,u,hu⟩ := htails c₀ c₂ c₃ hc₀ hc₂ hc₃ hb U hU hQU hgap
    have hOriginal (q : V) : originalFrameControl3_4 A₂ A₃ L hLu q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ (u q) ∧
        Told < q.val ∧ compoundMinima3_4 A₂ A₃ L hLu q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ 2 <
          compoundMinima3_4 A₂ A₃ L hLu q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ 3*q.val^(-delta/2) :=
      ⟨(hu q).1,(hu q).2.2.1,(hu q).2.2.2⟩
    let Vprime : Set ℝ := {Q | Q ∈ V ∧ T < Q}
    have hVpV : Vprime ⊆ V := fun _ h => h.1
    let W := cubeImage3_4 Vprime
    have hWR : ∀ R ∈ W, 1 < R := by
      rintro R ⟨Q,hQ,rfl⟩
      exact cube_gt_one3 Q (hQU Q (hVU (hVpV hQ)))
    refine ⟨V,hVU,hVeq,hV,u,hOriginal,Vprime,hVpV,rfl,
      JSP000334.sourceDual_unbounded_tail3 V hV T,W,hWR,rfl,
      cubeImage3_unbounded Vprime (JSP000334.sourceDual_unbounded_tail3 V hV T),?_,?_⟩
    · intro q
      let qV : V := ⟨q.val,hVpV q.property⟩
      have hQ := hQU q.val (hVU (hVpV q.property))
      refine ⟨source_normalizationTransport3 A₂ A₃ L hLu q.val hQ c₀ c₂ c₃
        (fun i => (hc₂ i).2) (fun i => (hc₃ i).2),?_,?_⟩
      · intro s
        exact summed_le_normalized_group3 A₂ A₃ q.val hQ c₂ c₃ (fun i => (hc₂ i).2) (fun i => (hc₃ i).2)
          ((hOriginal qV).1.2.2.1 s)
      · exact normalized_top_gap3 A₂ A₃ L hLu q.val hQ c₀ c₂ c₃
          (fun i => (hc₂ i).2) (fun i => (hc₃ i).2) delta (hcut q.val q.property.2) (hOriginal qV).2.2
    · rintro R ⟨Q,hQ,rfl⟩
      refine ⟨⟨Q,hQ⟩,rfl,?_⟩
      exact normalized_top_gap3 A₂ A₃ L hLu Q (hQU Q (hVU (hVpV hQ))) c₀ c₂ c₃
        (fun i => (hc₂ i).2) (fun i => (hc₃ i).2) delta (hcut Q hQ.2) (hOriginal ⟨Q,hVpV hQ⟩).2.2

end
end CompoundFeasibility.Exterior3NormalizationLiteral183

#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalizedWeights3_4
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.cube_gt_one3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalizedWeights3_conditions
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalized_power3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalized_threshold3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.directExponents3_4
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.direct_summed_exponents3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalizedGroup3_4
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalized_group3_eq
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.lattice4_antitone3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.summed_le_normalized_group3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.thirtysix_norm2_3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.thirtysix_norm3_3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.lattice4_scale_loss2_3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalized_thirtysix_mem3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalized_coordinates3_eq
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalized_body3_eq
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalizedMinima3_4
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.coordinateGauge4_thirtysix3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.integerReal_thirtysix3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.compoundMinima3_prefix_admissible
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalized_minima3_comparison
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalizedMinima3_pos_mono
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalized_gap_power3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalized_top_gap3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalization_cutoff3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.cubeImage3_4
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.cubeImage3_unbounded
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.normalizationTransport3_4
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.source_normalizationTransport3
#print axioms CompoundFeasibility.Exterior3NormalizationLiteral183.source_exterior3_normalized_gap4
