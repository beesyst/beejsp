import SubspaceBridge.SchlickeweiReference6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiReference6

def publishedFloor6 (p : ℕ) (Q : ℝ) (c : Fin 6 → ℝ) (i : Fin 6) : ℤ :=
  ⌊Real.log Q / Real.log (p : ℝ) * (∑ k : Fin 5, c (i.succAbove k))⌋

def supportFloor6 (p : ℕ) (Q : ℝ) (c : Fin 6 → ℝ)
    (T : Finset (Fin 6)) (hT : T.Nonempty) : ℤ := T.inf' hT (publishedFloor6 p Q c)

theorem support_floor_spec6 (p : ℕ) (Q : ℝ) (c : Fin 6 → ℝ)
    (T : Finset (Fin 6)) (hT : T.Nonempty) :
    (∃ i ∈ T, supportFloor6 p Q c T hT = publishedFloor6 p Q c i) ∧
      ∀ i ∈ T, supportFloor6 p Q c T hT ≤ publishedFloor6 p Q c i := by
  exact ⟨T.exists_mem_eq_inf' hT _, fun i hi => Finset.inf'_le _ hi⟩

theorem five_floor_error6 (t : Fin 5 → ℝ) :
    (∑ i, ⌊t i⌋) ≤ ⌊∑ i, t i⌋ ∧ ⌊∑ i, t i⌋ ≤ (∑ i, ⌊t i⌋) + 4 := by
  have hlo : ((∑ i, ⌊t i⌋ : ℤ) : ℝ) ≤ ∑ i, t i := by
    push_cast
    exact Finset.sum_le_sum (fun i _ => Int.floor_le _)
  have hhi : (∑ i, t i) < ((∑ i, ⌊t i⌋ : ℤ) : ℝ) + 5 := by
    calc
      _ < ∑ i : Fin 5, (((⌊t i⌋ : ℤ) : ℝ) + 1) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => Int.lt_floor_add_one _)
      _ = _ := by simp [Finset.sum_add_distrib]
  have hg : (⌊∑ i, t i⌋ : ℝ) < ((∑ i, ⌊t i⌋ : ℤ) : ℝ) + 5 :=
    lt_of_le_of_lt (Int.floor_le _) hhi
  have hgZ : ⌊∑ i, t i⌋ < (∑ i, ⌊t i⌋) + 5 := by exact_mod_cast hg
  exact ⟨Int.le_floor.mpr hlo, by omega⟩

theorem five_floor_natceil_error6 (t : Fin 5 → ℝ) (ht : ∀ i, t i ≤ 0) :
    (∑ i, -(Nat.ceil (-t i) : ℤ)) ≤ ⌊∑ i, t i⌋ ∧
      ⌊∑ i, t i⌋ ≤ (∑ i, -(Nat.ceil (-t i) : ℤ)) + 4 := by
  have he (i : Fin 5) : -(Nat.ceil (-t i) : ℤ) = ⌊t i⌋ := by
    rw [Int.natCast_ceil_eq_ceil (neg_nonneg.mpr (ht i)), Int.ceil_neg, neg_neg]
  simp_rw [he]
  exact five_floor_error6 t

theorem published_floor_nonpos6 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q)
    (c : Fin 6 → ℝ) (hc : ∀ i, c i ≤ 0) (i : Fin 6) : publishedFloor6 p Q c i ≤ 0 := by
  apply Int.floor_nonpos
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact (div_pos (Real.log_pos hQ) (Real.log_pos hpR)).le
  · exact Finset.sum_nonpos (fun k _ => hc (i.succAbove k))


theorem support_floor_nonpos6 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q)
    (c : Fin 6 → ℝ) (hc : ∀ i, c i ≤ 0) (T : Finset (Fin 6)) (hT : T.Nonempty) :
    supportFloor6 p Q c T hT ≤ 0 := by
  obtain ⟨i, hi⟩ := hT
  exact (Finset.inf'_le _ hi).trans (published_floor_nonpos6 p hp Q hQ c hc i)

def rescaleMultiplier6 (g2 g3 : ℤ) : ℤ :=
  6 ^ (5 : ℕ) * 2 ^ (-g2).toNat * 3 ^ (-g3).toNat

def integerRescale6 (g2 g3 : ℤ) (b : Fin 6 → ℤ) : Fin 6 → ℤ := rescaleMultiplier6 g2 g3 • b

theorem rescale_multiplier_pos6 (g2 g3 : ℤ) : 0 < rescaleMultiplier6 g2 g3 := by
  unfold rescaleMultiplier6
  positivity

theorem integer_rescale_nonzero6 (g2 g3 : ℤ) (b : Fin 6 → ℤ) (hb : b ≠ 0) :
    integerRescale6 g2 g3 b ≠ 0 :=
  smul_ne_zero (ne_of_gt (rescale_multiplier_pos6 g2 g3)) hb

theorem integer_rescale_line6 (g2 g3 : ℤ) (b : Fin 6 → ℤ) :
    Submodule.span ℚ {fun i => (integerRescale6 g2 g3 b i : ℚ)} =
      Submodule.span ℚ {fun i => (b i : ℚ)} := by
  have he : (fun i => (integerRescale6 g2 g3 b i : ℚ)) =
      (rescaleMultiplier6 g2 g3 : ℚ) • (fun i => (b i : ℚ)) := by
    funext i
    simp only [integerRescale6, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  have hne : (rescaleMultiplier6 g2 g3 : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (rescale_multiplier_pos6 g2 g3))
  rw [he]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hne) _

theorem integer_rescale_published6 (g2 g3 : ℤ) (hg2 : g2 ≤ 0) (hg3 : g3 ≤ 0)
    (b : Fin 6 → ℤ) :
    (fun i => (integerRescale6 g2 g3 b i : ℚ)) =
      ((6 : ℚ) ^ (5 : ℕ) * 2 ^ (-g2) * 3 ^ (-g3)) • (fun i => (b i : ℚ)) := by
  have he2 : (2 : ℚ) ^ (-g2).toNat = (2 : ℚ) ^ (-g2) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (neg_nonneg.mpr hg2)]
  have he3 : (3 : ℚ) ^ (-g3).toNat = (3 : ℚ) ^ (-g3) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (neg_nonneg.mpr hg3)]
  funext i
  simp only [integerRescale6, rescaleMultiplier6, Pi.smul_apply, smul_eq_mul,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  rw [he2, he3]


theorem rescale_multiplier_factor6 (g2 g3 : ℤ) :
    rescaleMultiplier6 g2 g3 =
      (2 : ℤ) ^ (5 + (-g2).toNat) * (3 : ℤ) ^ (5 + (-g3).toNat) := by
  unfold rescaleMultiplier6
  rw [show (6 : ℤ) = 2 * 3 by norm_num, mul_pow, pow_add, pow_add]
  ring

theorem rescale_p2_norm6 (g2 g3 : ℤ) (hg2 : g2 ≤ 0) :
    ‖(rescaleMultiplier6 g2 g3 : ℚ_[2])‖ ≤ (2 : ℝ) ^ (g2 - 5) := by
  have hd : (2 : ℤ) ^ (5 + (-g2).toNat) ∣ rescaleMultiplier6 g2 g3 := by
    rw [rescale_multiplier_factor6]
    exact dvd_mul_right _ _
  have hn := (SchlickeweiIntegerPairing6.integer_norm_dvd6 2
    (rescaleMultiplier6 g2 g3) (5 + (-g2).toNat)).mpr hd
  have hc : ((-g2).toNat : ℤ) = -g2 := Int.toNat_of_nonneg (neg_nonneg.mpr hg2)
  have he : -((5 + (-g2).toNat : ℕ) : ℤ) = g2 - 5 := by
    simp only [Nat.cast_add, Nat.cast_ofNat, hc]
    ring
  simpa only [he] using hn

theorem rescale_p3_norm6 (g2 g3 : ℤ) (hg3 : g3 ≤ 0) :
    ‖(rescaleMultiplier6 g2 g3 : ℚ_[3])‖ ≤ (3 : ℝ) ^ (g3 - 5) := by
  have hd : (3 : ℤ) ^ (5 + (-g3).toNat) ∣ rescaleMultiplier6 g2 g3 := by
    rw [rescale_multiplier_factor6]
    exact dvd_mul_left _ _
  have hn := (SchlickeweiIntegerPairing6.integer_norm_dvd6 3
    (rescaleMultiplier6 g2 g3) (5 + (-g3).toNat)).mpr hd
  have hc : ((-g3).toNat : ℤ) = -g3 := Int.toNat_of_nonneg (neg_nonneg.mpr hg3)
  have he : -((5 + (-g3).toNat : ℕ) : ℤ) = g3 - 5 := by
    simp only [Nat.cast_add, Nat.cast_ofNat, hc]
    ring
  simpa only [he] using hn


open SchlickeweiDualVanishing6 SchlickeweiIntegerPairing6 Auxiliary6.SourceExpansion

theorem floor_rounded_exponents6 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q)
    (c : Fin 6 → ℝ) (hc : ∀ i, c i ≤ 0) (f : Fin 6 → ℤ)
    (hf : ∀ i, f i = -(Nat.ceil (JSP000334.qThreshold p Q (c i)) : ℤ)) (i : Fin 6) :
    (∑ k : Fin 5, f (i.succAbove k)) ≤ publishedFloor6 p Q c i ∧
      publishedFloor6 p Q c i ≤ (∑ k : Fin 5, f (i.succAbove k)) + 4 := by
  let t : Fin 6 → ℝ := fun j => Real.log Q / Real.log (p : ℝ) * c j
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have ht (j : Fin 6) : t j ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_pos (Real.log_pos hQ) (Real.log_pos hpR)).le (hc j)
  have he (j : Fin 6) : JSP000334.qThreshold p Q (c j) = -t j := by
    unfold JSP000334.qThreshold t
    ring
  have hsum : (∑ k : Fin 5, f (i.succAbove k)) =
      ∑ k : Fin 5, -(Nat.ceil (-t (i.succAbove k)) : ℤ) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hf, he]
  have hr := five_floor_natceil_error6 (fun k => t (i.succAbove k)) (fun k => ht _)
  have hreal : (∑ k : Fin 5, t (i.succAbove k)) =
      Real.log Q / Real.log (p : ℝ) * (∑ k : Fin 5, c (i.succAbove k)) := by
    simp only [t, Finset.mul_sum]
  rw [hreal, ← hsum] at hr
  exact hr

theorem integer_rescale_dual_norm6 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (g2 g3 : ℤ) (b : Fin 6 → ℤ) (i : Fin 6) :
    ‖dualFormValue6 B (fun k => (integerRescale6 g2 g3 b k : ℚ)) i‖ =
      ‖(rescaleMultiplier6 g2 g3 : ℚ_[p])‖ * ‖dualFormValue6 B (fun k => (b k : ℚ)) i‖ := by
  have he : (fun k => (integerRescale6 g2 g3 b k : ℚ)) =
      (rescaleMultiplier6 g2 g3 : ℚ) • (fun k => (b k : ℚ)) := by
    funext k
    simp only [integerRescale6, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  rw [he, dual_scalar_value6, norm_mul, map_intCast]

theorem integer_rescale_finite_bound6 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (g2 g3 g : ℤ) (b : Fin 6 → ℤ)
    (r : Fin 6 → ℤ)
    (hcoef : ‖(rescaleMultiplier6 g2 g3 : ℚ_[p])‖ ≤ (p : ℝ) ^ (g - 5))
    (hb : ∀ i, ‖dualFormValue6 B (fun k => (b k : ℚ)) i‖ ≤ 1)
    (hg : ∀ i ∈ finiteSupport6 p B b, g ≤ r i + 4) (i : Fin 6) :
    ‖dualFormValue6 B (fun k => (integerRescale6 g2 g3 b k : ℚ)) i‖ ≤ (p : ℝ) ^ r i := by
  rw [integer_rescale_dual_norm6]
  by_cases hz : dualFormValue6 B (fun k => (b k : ℚ)) i = 0
  · rw [hz, norm_zero, mul_zero]
    positivity
  · have hi : i ∈ finiteSupport6 p B b := by
      simp only [finiteSupport6, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hz
    have hex : g - 5 ≤ r i := by have h := hg i hi; omega
    have hpbase : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    calc
      _ ≤ (p : ℝ) ^ (g - 5) * 1 := mul_le_mul hcoef (hb i) (norm_nonneg _) (by positivity)
      _ = (p : ℝ) ^ (g - 5) := mul_one _
      _ ≤ _ := zpow_le_zpow_right₀ hpbase hex


open SourceReadiness6 SourceMixed6 SchlickeweiEquation4116 SchlickeweiSatz51Selected6

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

def sourceFloor2 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V) : ℤ :=
  supportFloor6 2 (q.val ^ (11 : ℕ)) (R.c 1)
    (finiteSupport6 2 (finiteMatrix 2 A2) (sourceReference6 R q1))
    (source_reference_supports6 R h2 h3 q1).1

def sourceFloor3 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V) : ℤ :=
  supportFloor6 3 (q.val ^ (11 : ℕ)) (R.c 2)
    (finiteSupport6 3 (finiteMatrix 3 A3) (sourceReference6 R q1))
    (source_reference_supports6 R h2 h3 q1).2

def rescaledReference6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V) : Fin 6 → ℤ :=
  integerRescale6 (sourceFloor2 R h2 h3 q1 q) (sourceFloor3 R h2 h3 q1 q) (sourceReference6 R q1)

theorem source_floor_nonpos6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (q1 q : V) : sourceFloor2 R h2 h3 q1 q ≤ 0 ∧ sourceFloor3 R h2 h3 q1 q ≤ 0 := by
  have hcf2 : ∀ i, R.c 1 i ≤ 0 := by
    intro i
    rw [(R.finite_weights i).1]
    exact (SourceWeights.finiteWeight_bounds c2 hc2 i).2
  have hcf3 : ∀ i, R.c 2 i ≤ 0 := by
    intro i
    rw [(R.finite_weights i).2]
    exact (SourceWeights.finiteWeight_bounds c3 hc3 i).2
  exact ⟨support_floor_nonpos6 2 (by decide) _ (source_parameter_gt_one6 R q) _ hcf2 _ _,
    support_floor_nonpos6 3 (by decide) _ (source_parameter_gt_one6 R q) _ hcf3 _ _⟩

theorem rescaled_reference_nonzero6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V) : rescaledReference6 R h2 h3 q1 q ≠ 0 :=
  integer_rescale_nonzero6 _ _ _ (source_reference_nonzero6 R q1)

theorem rescaled_reference_line6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V) :
    Submodule.span ℚ {fun i => (rescaledReference6 R h2 h3 q1 q i : ℚ)} =
      Submodule.span ℚ {fun i => (sourceReference6 R q1 i : ℚ)} :=
  integer_rescale_line6 _ _ _

theorem rescaled_reference_p2_6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (q1 q : V) (i : Fin 6) :
    ‖dualFormValue6 (finiteMatrix 2 A2) (fun k => (rescaledReference6 R h2 h3 q1 q k : ℚ)) i‖ ≤
      (2 : ℝ) ^ (∑ k : Fin 5, sourceExponent6 2 q.val c2 (i.succAbove k)) := by
  let B := finiteMatrix 2 A2
  let b := sourceReference6 R q1
  let g2 := sourceFloor2 R h2 h3 q1 q
  let g3 := sourceFloor3 R h2 h3 q1 q
  let r : Fin 6 → ℤ := fun i => ∑ k : Fin 5, sourceExponent6 2 q.val c2 (i.succAbove k)
  have hneg := source_floor_nonpos6 R h2 h3 hc2 hc3 q1 q
  have hb : ∀ i, ‖dualFormValue6 B (fun k => (b k : ℚ)) i‖ ≤ 1 := by
    intro i
    let r1 : ℤ := ∑ k : Fin 5, sourceExponent6 2 q1.val c2 (i.succAbove k)
    have hex : r1 ≤ 0 := Finset.sum_nonpos (fun k _ => source_exponent_nonpos6 _ _ _ _)
    have hp : (2 : ℝ) ^ r1 ≤ 1 := by
      simpa only [zpow_zero] using zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hex
    exact (source_reference_p2_bound6 R h2 h3 q1 i).trans hp
  have hcf : ∀ i, R.c 1 i ≤ 0 := by
    intro i
    rw [(R.finite_weights i).1]
    exact (SourceWeights.finiteWeight_bounds c2 hc2 i).2
  have hg : ∀ i ∈ finiteSupport6 2 B b, g2 ≤ r i + 4 := by
    intro i hi
    have hmin := (support_floor_spec6 2 (q.val ^ (11 : ℕ)) (R.c 1)
      (finiteSupport6 2 B b) (source_reference_supports6 R h2 h3 q1).1).2 i hi
    have hr := floor_rounded_exponents6 2 (by decide) _ (source_parameter_gt_one6 R q)
      (R.c 1) hcf (sourceExponent6 2 q.val c2)
      (fun k => (source_exponent_rescaling6 R q k).1) i
    exact hmin.trans hr.2
  exact integer_rescale_finite_bound6 2 B g2 g3 g2 b r
    (rescale_p2_norm6 g2 g3 hneg.1) hb hg i

theorem rescaled_reference_p3_6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (q1 q : V) (i : Fin 6) :
    ‖dualFormValue6 (finiteMatrix 3 A3) (fun k => (rescaledReference6 R h2 h3 q1 q k : ℚ)) i‖ ≤
      (3 : ℝ) ^ (∑ k : Fin 5, sourceExponent6 3 q.val c3 (i.succAbove k)) := by
  let B := finiteMatrix 3 A3
  let b := sourceReference6 R q1
  let g2 := sourceFloor2 R h2 h3 q1 q
  let g3 := sourceFloor3 R h2 h3 q1 q
  let r : Fin 6 → ℤ := fun i => ∑ k : Fin 5, sourceExponent6 3 q.val c3 (i.succAbove k)
  have hneg := source_floor_nonpos6 R h2 h3 hc2 hc3 q1 q
  have hb : ∀ i, ‖dualFormValue6 B (fun k => (b k : ℚ)) i‖ ≤ 1 := by
    intro i
    let r1 : ℤ := ∑ k : Fin 5, sourceExponent6 3 q1.val c3 (i.succAbove k)
    have hex : r1 ≤ 0 := Finset.sum_nonpos (fun k _ => source_exponent_nonpos6 _ _ _ _)
    have hp : (3 : ℝ) ^ r1 ≤ 1 := by
      simpa only [zpow_zero] using zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 3 by norm_num) hex
    exact (source_reference_p3_bound6 R h2 h3 q1 i).trans hp
  have hcf : ∀ i, R.c 2 i ≤ 0 := by
    intro i
    rw [(R.finite_weights i).2]
    exact (SourceWeights.finiteWeight_bounds c3 hc3 i).2
  have hg : ∀ i ∈ finiteSupport6 3 B b, g3 ≤ r i + 4 := by
    intro i hi
    have hmin := (support_floor_spec6 3 (q.val ^ (11 : ℕ)) (R.c 2)
      (finiteSupport6 3 B b) (source_reference_supports6 R h2 h3 q1).2).2 i hi
    have hr := floor_rounded_exponents6 3 (by decide) _ (source_parameter_gt_one6 R q)
      (R.c 2) hcf (sourceExponent6 3 q.val c3)
      (fun k => (source_exponent_rescaling6 R q k).2) i
    exact hmin.trans hr.2
  exact integer_rescale_finite_bound6 3 B g2 g3 g3 b r
    (rescale_p3_norm6 g2 g3 hneg.2) hb hg i


theorem rescaled_reference_published6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (q1 q : V) :
    (fun i => (rescaledReference6 R h2 h3 q1 q i : ℚ)) =
      ((6 : ℚ) ^ (5 : ℕ) * 2 ^ (-sourceFloor2 R h2 h3 q1 q) *
        3 ^ (-sourceFloor3 R h2 h3 q1 q)) • (fun i => (sourceReference6 R q1 i : ℚ)) := by
  have hn := source_floor_nonpos6 R h2 h3 hc2 hc3 q1 q
  exact integer_rescale_published6 _ _ hn.1 hn.2 _

theorem supported_product_real_zero6
    (b : Fin 6 → ℤ) (s : MixedIndex6)
    (h2s : s 1 ∈ finiteSupport6 2 (finiteMatrix 2 A2) b)
    (h3s : s 2 ∈ finiteSupport6 3 (finiteMatrix 3 A3) b)
    (hz : SchlickeweiEquation4126.publishedDualProduct6 A2 A3 L
      (fun k => (b k : ℚ)) s = 0) :
    dualFormValue6 (compound L) (fun k => (b k : ℚ)) (s 0) = 0 := by
  have h2n : dualFormValue6 (finiteMatrix 2 A2) (fun k => (b k : ℚ)) (s 1) ≠ 0 := by
    simpa only [finiteSupport6, Finset.mem_filter, Finset.mem_univ, true_and] using h2s
  have h3n : dualFormValue6 (finiteMatrix 3 A3) (fun k => (b k : ℚ)) (s 2) ≠ 0 := by
    simpa only [finiteSupport6, Finset.mem_filter, Finset.mem_univ, true_and] using h3s
  have hreal : ‖dualFormValue6 (compound L) (fun k => (b k : ℚ)) (s 0)‖ = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (norm_ne_zero_iff.mpr h3n))).resolve_right
      (norm_ne_zero_iff.mpr h2n)
  exact norm_eq_zero.mp hreal

theorem rescaled_reference_case1_zero6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V) (s : MixedIndex6)
    (h2s : s 1 ∈ finiteSupport6 2 (finiteMatrix 2 A2) (sourceReference6 R q1))
    (h3s : s 2 ∈ finiteSupport6 3 (finiteMatrix 3 A3) (sourceReference6 R q1))
    (hz : SchlickeweiEquation4126.publishedDualProduct6 A2 A3 L
      (fun k => (sourceReference6 R q1 k : ℚ)) s = 0) :
    dualFormValue6 (compound L) (fun k => (rescaledReference6 R h2 h3 q1 q k : ℚ)) (s 0) = 0 := by
  have he : (fun k => (rescaledReference6 R h2 h3 q1 q k : ℚ)) =
      (rescaleMultiplier6 (sourceFloor2 R h2 h3 q1 q) (sourceFloor3 R h2 h3 q1 q) : ℚ) •
        (fun k => (sourceReference6 R q1 k : ℚ)) := by
    funext k
    simp only [rescaledReference6, integerRescale6, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  rw [he, dual_scalar_value6, supported_product_real_zero6 _ s h2s h3s hz, mul_zero]


theorem source_reference_rescaling6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) :
    ∃ (Bzero Bpoint T : ℝ) (q1 : V),
      max Bzero (max Bpoint T) < q1.val ∧
      (120 * (q1.val ^ (11 : ℕ)) ^ (-5 * R.delta) ≤ 1) ∧
      sourceReference6 R q1 ≠ 0 ∧
      sourceAuxiliaryInteger6 R q1 (sourceReference6 R q1) ∧
      (Submodule.span ℚ {fun i => (sourceReference6 R q1 i : ℚ)} =
        Submodule.span ℚ {fun i => (R.M q1 i : ℚ)}) ∧
      (finiteSupport6 2 (finiteMatrix 2 A2) (sourceReference6 R q1)).Nonempty ∧
      (finiteSupport6 3 (finiteMatrix 3 A3) (sourceReference6 R q1)).Nonempty ∧
      (∀ s ∈ admissibleMixed6 R.c (R.delta/2),
        SchlickeweiEquation4126.publishedDualProduct6 A2 A3 L
          (fun k => (sourceReference6 R q1 k : ℚ)) s = 0) ∧
      ∀ q : V, rescaledReference6 R h2 h3 q1 q ≠ 0 ∧
        (Submodule.span ℚ {fun i => (rescaledReference6 R h2 h3 q1 q i : ℚ)} =
          Submodule.span ℚ {fun i => (sourceReference6 R q1 i : ℚ)}) ∧
        (∀ i, ‖dualFormValue6 (finiteMatrix 2 A2)
          (fun k => (rescaledReference6 R h2 h3 q1 q k : ℚ)) i‖ ≤
          (2 : ℝ) ^ (∑ k : Fin 5, sourceExponent6 2 q.val c2 (i.succAbove k))) ∧
        (∀ i, ‖dualFormValue6 (finiteMatrix 3 A3)
          (fun k => (rescaledReference6 R h2 h3 q1 q k : ℚ)) i‖ ≤
          (3 : ℝ) ^ (∑ k : Fin 5, sourceExponent6 3 q.val c3 (i.succAbove k))) := by
  obtain ⟨Bzero, Bpoint, T, q1, hq1, hsmall, hb, haux, hline, _, hzero⟩ :=
    source_fixed_reference6 R h2 h3 hLdet
  have hs := source_reference_supports6 R h2 h3 q1
  refine ⟨Bzero, Bpoint, T, q1, hq1, hsmall, hb, haux, hline, hs.1, hs.2,
    fun s hs => source_reference_product_zero6 R q1 s (hzero s hs), ?_⟩
  intro q
  exact ⟨rescaled_reference_nonzero6 R h2 h3 q1 q, rescaled_reference_line6 R h2 h3 q1 q,
    rescaled_reference_p2_6 R h2 h3 hc2 hc3 q1 q,
    rescaled_reference_p3_6 R h2 h3 hc2 hc3 q1 q⟩

end CompoundFeasibility.SchlickeweiReference6
