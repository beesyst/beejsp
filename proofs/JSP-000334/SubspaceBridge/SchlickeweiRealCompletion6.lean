import SubspaceBridge.SchlickeweiRealReference6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiRealCompletion6
open Auxiliary6.SourceExpansion SourceReadiness6 SourceMixed6 SchlickeweiReference6 SchlickeweiDualVanishing6
open SchlickeweiRealReference6 SchlickeweiSatz51Selected6 SchlickeweiEquation4106 SchlickeweiIntegerPairing6
variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem attained_tuple6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V) (i : Fin 6) :
    ∃ s : MixedIndex6, s 0 = i ∧
      s 1 ∈ finiteSupport6 2 (finiteMatrix 2 A2) (sourceReference6 R q1) ∧
      s 2 ∈ finiteSupport6 3 (finiteMatrix 3 A3) (sourceReference6 R q1) ∧
      sourceFloor2 R h2 h3 q1 q = publishedFloor6 2 (q.val ^ (11 : ℕ)) (R.c 1) (s 1) ∧
      sourceFloor3 R h2 h3 q1 q = publishedFloor6 3 (q.val ^ (11 : ℕ)) (R.c 2) (s 2) := by
  obtain ⟨⟨j2, hj2, he2⟩, j3, hj3, he3⟩ := source_floor_attained6 R h2 h3 q1 q
  exact ⟨![i, j2, j3], rfl, hj2, hj3, he2, he3⟩

theorem omitted_balance_gap6 (c : Fin 3 → Fin 6 → ℝ) (delta : ℝ)
    (hb : (∑ tau, ∑ i, c tau i) = 0) (s : MixedIndex6)
    (hs : s ∉ admissibleMixed6 c (delta/2)) :
    -(∑ k : Fin 5, c 1 ((s 1).succAbove k)) - (∑ k : Fin 5, c 2 ((s 2).succAbove k)) <
      (∑ i : Fin 6, c 0 i) - c 0 (s 0) - 3*delta/8 := by
  have hgap := selected_complement_gap6 delta c s hs
  have h1 := Fin.sum_univ_succAbove (c 1) (s 1)
  have h2 := Fin.sum_univ_succAbove (c 2) (s 2)
  simp only [Fin.sum_univ_three] at hb hgap
  linarith

theorem source_power_covolume6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q : V) (i : Fin 6) :
    (q.val ^ (11 : ℕ)) ^ ((∑ j : Fin 6, R.c 0 j) - R.c 0 i - 3*R.delta/8) ≤
      (ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) /
        (q.val ^ (11 : ℕ)) ^ (R.c 0 i)) * (q.val ^ (11 : ℕ)) ^ (-3*R.delta/8) := by
  have hQ := zero_lt_one.trans (source_parameter_gt_one6 R q)
  have hw : (q.val ^ (11 : ℕ)) ^ (∑ j : Fin 6, R.c 0 j) ≤
      ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) := by
    rw [Real.rpow_sum_of_pos hQ]
    exact source_width_product_le_covolume6 R h2 h3 q
  calc
    _ = ((q.val ^ (11 : ℕ)) ^ (∑ j : Fin 6, R.c 0 j) /
        (q.val ^ (11 : ℕ)) ^ (R.c 0 i)) * (q.val ^ (11 : ℕ)) ^ (-3*R.delta/8) := by
      rw [Real.rpow_sub hQ, Real.rpow_sub hQ,
        show -3*R.delta/8 = -(3*R.delta/8) by ring, Real.rpow_neg hQ.le, div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hw (Real.rpow_pos_of_pos hQ _).le) (by positivity)

def referenceRealConstant6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q1 : V) : ℝ :=
  (6 : ℝ) ^ (6 : ℕ) * (1 + ∑ i : Fin 6,
    ‖dualFormValue6 (compound L) (fun k => (sourceReference6 R q1 k : ℚ)) i‖)

theorem reference_real_constant_pos6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q1 : V) :
    0 < referenceRealConstant6 R q1 := by
  unfold referenceRealConstant6
  positivity

theorem reference_real_constant_bound6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q1 : V) (i : Fin 6) :
    (6 : ℝ) ^ (6 : ℕ) *
      ‖dualFormValue6 (compound L) (fun k => (sourceReference6 R q1 k : ℚ)) i‖ ≤
        referenceRealConstant6 R q1 := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := Finset.single_le_sum (f := fun j : Fin 6 =>
    ‖dualFormValue6 (compound L) (fun k => (sourceReference6 R q1 k : ℚ)) j‖)
    (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  exact h.trans (le_add_of_nonneg_left zero_le_one)

theorem rescaled_reference_attained_complement6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (q1 q : V) (s : MixedIndex6)
    (he2 : sourceFloor2 R h2 h3 q1 q = publishedFloor6 2 (q.val ^ (11 : ℕ)) (R.c 1) (s 1))
    (he3 : sourceFloor3 R h2 h3 q1 q = publishedFloor6 3 (q.val ^ (11 : ℕ)) (R.c 2) (s 2))
    (hnot : s ∉ admissibleMixed6 R.c (R.delta/2)) :
    ‖dualFormValue6 (compound L) (fun k => (rescaledReference6 R h2 h3 q1 q k : ℚ)) (s 0)‖ ≤
      referenceRealConstant6 R q1 *
        (ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) /
          (q.val ^ (11 : ℕ)) ^ (R.c 0 (s 0))) * (q.val ^ (11 : ℕ)) ^ (-3*R.delta/8) := by
  have hQ := zero_lt_one.trans (source_parameter_gt_one6 R q)
  have hgap := omitted_balance_gap6 R.c R.delta R.weights_balance s hnot
  have hpow := Real.rpow_le_rpow_of_exponent_le (source_parameter_gt_one6 R q).le hgap.le
  have hle := hpow.trans (source_power_covolume6 R h2 h3 q (s 0))
  calc
    _ ≤ ((6 : ℝ) ^ (6 : ℕ) * (q.val ^ (11 : ℕ)) ^
        (-(∑ k : Fin 5, R.c 1 ((s 1).succAbove k)) - (∑ k : Fin 5, R.c 2 ((s 2).succAbove k)))) *
        ‖dualFormValue6 (compound L) (fun k => (sourceReference6 R q1 k : ℚ)) (s 0)‖ :=
      rescaled_reference_real_growth6 R h2 h3 hc2 hc3 q1 q (s 0) (s 1) (s 2) he2 he3
    _ = ((6 : ℝ) ^ (6 : ℕ) *
        ‖dualFormValue6 (compound L) (fun k => (sourceReference6 R q1 k : ℚ)) (s 0)‖) *
        (q.val ^ (11 : ℕ)) ^
          (-(∑ k : Fin 5, R.c 1 ((s 1).succAbove k)) - (∑ k : Fin 5, R.c 2 ((s 2).succAbove k))) := by ring
    _ ≤ referenceRealConstant6 R q1 * _ :=
      mul_le_mul_of_nonneg_right (reference_real_constant_bound6 R q1 (s 0))
        (Real.rpow_pos_of_pos hQ _).le
    _ ≤ referenceRealConstant6 R q1 *
        ((ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) /
          (q.val ^ (11 : ℕ)) ^ (R.c 0 (s 0))) * (q.val ^ (11 : ℕ)) ^ (-3*R.delta/8)) :=
      mul_le_mul_of_nonneg_left hle (reference_real_constant_pos6 R q1).le
    _ = _ := by ring

theorem rescaled_reference_real_cases6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (q1 q : V)
    (hz : ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
      SchlickeweiEquation4126.publishedDualProduct6 A2 A3 L
        (fun k => (sourceReference6 R q1 k : ℚ)) s = 0) (i : Fin 6) :
    dualFormValue6 (compound L) (fun k => (rescaledReference6 R h2 h3 q1 q k : ℚ)) i = 0 ∨
    ‖dualFormValue6 (compound L) (fun k => (rescaledReference6 R h2 h3 q1 q k : ℚ)) i‖ ≤
      referenceRealConstant6 R q1 *
        (ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) /
          (q.val ^ (11 : ℕ)) ^ (R.c 0 i)) * (q.val ^ (11 : ℕ)) ^ (-3*R.delta/8) := by
  obtain ⟨s, hi, hj2, hj3, he2, he3⟩ := attained_tuple6 R h2 h3 q1 q i
  subst i
  by_cases hs : s ∈ admissibleMixed6 R.c (R.delta/2)
  · exact Or.inl (rescaled_reference_case1_zero6 R h2 h3 q1 q s hj2 hj3 (hz s hs))
  · exact Or.inr (rescaled_reference_attained_complement6 R h2 h3 hc2 hc3 q1 q s he2 he3 hs)

theorem reference_real_cutoff6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q1 : V) :
    ∃ T : ℝ, 1 < T ∧ ∀ q : V, T < q.val →
      referenceRealConstant6 R q1 * (q.val ^ (11 : ℕ)) ^ (-3*R.delta/8) ≤ 1 := by
  obtain ⟨T, hT, hcut⟩ := SchlickeweiAuxiliaryLine6.pairing_power_cutoff6
    (referenceRealConstant6 R q1 / 6) (3*R.delta/8)
    (div_pos (reference_real_constant_pos6 R q1) (by norm_num)) (by linarith [R.delta_pos])
  refine ⟨T, hT, ?_⟩
  intro q hq
  have hle : q.val ≤ q.val ^ (11 : ℕ) :=
    le_self_pow₀ (hQV q.val q.property).le (by decide)
  have h := (hcut _ (lt_of_lt_of_le hq hle) (source_parameter_gt_one6 R q)).le
  simpa only [show (6 : ℝ) * (referenceRealConstant6 R q1 / 6) = referenceRealConstant6 R q1 by ring,
    show -(3*R.delta/8) = -3*R.delta/8 by ring] using h

theorem rescaled_reference_real_bound6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (q1 : V)
    (hz : ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
      SchlickeweiEquation4126.publishedDualProduct6 A2 A3 L
        (fun k => (sourceReference6 R q1 k : ℚ)) s = 0) :
    ∃ T : ℝ, 1 < T ∧ ∀ q : V, T < q.val → ∀ i : Fin 6,
      ‖dualFormValue6 (compound L) (fun k => (rescaledReference6 R h2 h3 q1 q k : ℚ)) i‖ ≤
        ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) /
          (q.val ^ (11 : ℕ)) ^ (R.c 0 i) := by
  obtain ⟨T, hT, hcut⟩ := reference_real_cutoff6 R q1
  refine ⟨T, hT, ?_⟩
  intro q hq i
  have hQ := zero_lt_one.trans (source_parameter_gt_one6 R q)
  have hd := (SourceRelativeIndex6.source_frame_normalization6 R q).2.2.2.2.2
  have hpos : 0 ≤ ZLattice.covolume (integerRealImage
      (directCompoundGroup42 A2 A3 q.val c2 c3)) / (q.val ^ (11 : ℕ)) ^ (R.c 0 i) :=
    div_nonneg hd.le (Real.rpow_pos_of_pos hQ _).le
  rcases rescaled_reference_real_cases6 R h2 h3 hc2 hc3 q1 q hz i with he | hb
  · rw [he, norm_zero]
    exact hpos
  · calc
      _ ≤ referenceRealConstant6 R q1 *
          (ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) /
            (q.val ^ (11 : ℕ)) ^ (R.c 0 i)) * (q.val ^ (11 : ℕ)) ^ (-3*R.delta/8) := hb
      _ = (ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) /
            (q.val ^ (11 : ℕ)) ^ (R.c 0 i)) *
          (referenceRealConstant6 R q1 * (q.val ^ (11 : ℕ)) ^ (-3*R.delta/8)) := by ring
      _ ≤ _ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hcut q hq) hpos

theorem rescaled_reference_auxiliary6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (q1 : V)
    (hz : ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
      SchlickeweiEquation4126.publishedDualProduct6 A2 A3 L
        (fun k => (sourceReference6 R q1 k : ℚ)) s = 0) :
    ∃ T : ℝ, 1 < T ∧ ∀ q : V, T < q.val →
      sourceAuxiliaryInteger6 R q (rescaledReference6 R h2 h3 q1 q) := by
  obtain ⟨T, hT, hreal⟩ := rescaled_reference_real_bound6 R h2 h3 hc2 hc3 q1 hz
  exact ⟨T, hT, fun q hq => ⟨hreal q hq,
    rescaled_reference_p2_6 R h2 h3 hc2 hc3 q1 q,
    rescaled_reference_p3_6 R h2 h3 hc2 hc3 q1 q⟩⟩

theorem nonzero_mem_line_span6 (x y : Fin 6 → ℚ) (hx : x ≠ 0)
    (hxy : x ∈ Submodule.span ℚ {y}) :
    Submodule.span ℚ {x} = Submodule.span ℚ {y} := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxy
  have hne : a ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at ha
    exact hx ha.symm
  rw [← ha]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hne) y

theorem source_satz51_selected6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) :
    ∃ (B : ℝ) (q1 : V), 1 < B ∧
      ¬ BddAbove {q : ℝ | q ∈ V ∧ B < q} ∧ sourceReference6 R q1 ≠ 0 ∧
      ∀ q : V, B < q.val →
        rescaledReference6 R h2 h3 q1 q ≠ 0 ∧
        sourceAuxiliaryInteger6 R q (rescaledReference6 R h2 h3 q1 q) ∧
        (Submodule.span ℚ {fun i => (rescaledReference6 R h2 h3 q1 q i : ℚ)} =
          Submodule.span ℚ {fun i => (sourceReference6 R q1 i : ℚ)}) ∧
        (Submodule.span ℚ {fun i => (R.M q i : ℚ)} =
          Submodule.span ℚ {fun i => (sourceReference6 R q1 i : ℚ)}) ∧
        (Submodule.span ℚ {dualVector6 (fun j => (R.w q j : Fin 6 → ℤ))
          (sourceFrameIndependent6 R q)} =
          Submodule.span ℚ {fun i => (sourceReference6 R q1 i : ℚ)}) := by
  obtain ⟨Bzero, Bpoint, T, q1, _, _, hb, _, _, hpoint, hzero⟩ :=
    source_fixed_reference6 R h2 h3 hLdet
  have hz : ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
      SchlickeweiEquation4126.publishedDualProduct6 A2 A3 L
        (fun k => (sourceReference6 R q1 k : ℚ)) s = 0 :=
    fun s hs => source_reference_product_zero6 R q1 s (hzero s hs)
  obtain ⟨Treal, hTr, haux⟩ := rescaled_reference_auxiliary6 R h2 h3 hc2 hc3 q1 hz
  let B := max Bzero (max Bpoint (max T Treal))
  have hreal : Treal ≤ B := (le_max_right T Treal).trans
    ((le_max_right Bpoint (max T Treal)).trans (le_max_right Bzero _))
  have hpt : Bpoint ≤ B := (le_max_left Bpoint _).trans (le_max_right Bzero _)
  refine ⟨B, q1, hTr.trans_le hreal, JSP000334.sourceDual_unbounded_tail3 V R.unbounded B, hb, ?_⟩
  intro q hq
  have hy := haux q (hreal.trans_lt hq)
  have hn := rescaled_reference_nonzero6 R h2 h3 q1 q
  have hl := rescaled_reference_line6 R h2 h3 q1 q
  have hmem := hpoint q (hpt.trans_lt hq) _ hy
  have hrat : (fun i => (rescaledReference6 R h2 h3 q1 q i : ℚ)) ≠ 0 := by
    intro he
    apply hn
    funext i
    have hi := congrFun he i
    change (rescaledReference6 R h2 h3 q1 q i : ℚ) = 0 at hi
    change rescaledReference6 R h2 h3 q1 q i = 0
    exact_mod_cast hi
  have hm := (nonzero_mem_line_span6 _ _ hrat hmem).symm.trans hl
  exact ⟨hn, hy, hl, hm, (source_primitive_dual_span6 R q).2.2.2.trans hm⟩

theorem source_original_satz51_selected6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (delta4 : ℝ) (hd : 0 < delta4) (c0 c2 c3 : Fin 4 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hbalance : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ q ∈ U, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ U),
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQU q hq) c0 c2 c3 1 <
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQU q hq) c0 c2 c3 2 * q^(-delta4)) :
    ∃ (V : Set ℝ) (hVU : V ⊆ U)
      (R : SourceReadiness42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V
        (fun q hq => hQU q (hVU hq))) (B : ℝ) (q1 : V),
      1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ V ∧ B < q} ∧ sourceReference6 R q1 ≠ 0 ∧
      ∀ q : V, B < q.val →
        Submodule.span ℚ {dualVector6 (fun j => (R.w q j : Fin 6 → ℤ))
          (sourceFrameIndependent6 R q)} =
          Submodule.span ℚ {fun i => (sourceReference6 R q1 i : ℚ)} := by
  obtain ⟨V, hVU, _, _, hR⟩ := source_compound_unbounded_readiness42 A2 A3 L h2 h3 hL hAlg
    delta4 hd c0 c2 c3 hc0 hc2 hc3 hbalance U hU hQU hgap
  obtain ⟨R⟩ := hR
  obtain ⟨B, q1, hB, htail, hb, hline⟩ := source_satz51_selected6 R h2 h3 hL hc2 hc3
  exact ⟨V, hVU, R, B, q1, hB, htail, hb, fun q hq => (hline q hq).2.2.2.2⟩

end CompoundFeasibility.SchlickeweiRealCompletion6
