import SubspaceBridge.SchlickeweiSatz41Selected6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiSatz51Selected6
open SourceReadiness6 SourceMixed6 SourceWeights SchlickeweiDualVanishing6

theorem unrounded_normalization6 (Q : ℝ) (hQ : 0 < Q)
    (c : Fin 3 → Fin 6 → ℝ) (hbal : (∑ tau, ∑ i, c tau i) = 0) :
    (∏ i : Fin 6, Q ^ (c 0 i) * (Q ^ (c 1 i) * Q ^ (c 2 i))) = 1 := by
  simp_rw [← Real.rpow_add hQ]
  rw [← Real.rpow_sum_of_pos hQ]
  have hb : (∑ i, (c 0 i + (c 1 i + c 2 i))) = 0 := by
    simpa only [Fin.sum_univ_three, Finset.sum_add_distrib, add_assoc] using hbal
  rw [hb, Real.rpow_zero]

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem source_parameter_gt_one6
    (_R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    1 < q.val ^ (11 : ℕ) :=
  one_lt_pow₀ (hQV q.val q.property) (by decide)

theorem source_unrounded_normalization6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    (∏ i : Fin 6, (q.val ^ (11 : ℕ)) ^ (R.c 0 i) *
      ((q.val ^ (11 : ℕ)) ^ (R.c 1 i) *
        (q.val ^ (11 : ℕ)) ^ (R.c 2 i))) = 1 :=
  unrounded_normalization6 _ (lt_trans zero_lt_one (source_parameter_gt_one6 R q))
    R.c R.weights_balance


def publishedIndexSet6 (Q delta : ℝ) (c : Fin 3 → Fin 6 → ℝ) :
    Finset MixedIndex6 :=
  Finset.univ.filter (fun s =>
    1 ≤ Q ^ (c 0 (s 0)) * (Q ^ (c 1 (s 1)) * Q ^ (c 2 (s 2))) *
      Q ^ (delta/2))

theorem published_index_exponent6 (Q delta : ℝ) (hQ : 1 < Q)
    (c : Fin 3 → Fin 6 → ℝ) (s : MixedIndex6) :
    s ∈ publishedIndexSet6 Q delta c ↔ -delta/2 ≤ ∑ tau, c tau (s tau) := by
  simp only [publishedIndexSet6, Finset.mem_filter, Finset.mem_univ, true_and]
  simp_rw [← Real.rpow_add (lt_trans zero_lt_one hQ)]
  rw [← Real.rpow_zero Q, Real.rpow_le_rpow_left_iff hQ]
  simp only [Fin.sum_univ_three]
  constructor <;> intro h <;> linarith

theorem selected_exponent_margin6 (x delta : ℝ) (hd : 0 < delta)
    (hx : -(3*delta)/8 ≤ x) : delta/8 ≤ x+delta/2 ∧ 0 < x+delta/2 := by
  constructor <;> linarith

theorem selected_width_product_ge_one6 (Q delta x : ℝ)
    (hQ : 1 < Q) (hd : 0 < delta) (hx : -(3*delta)/8 ≤ x) :
    1 ≤ Q ^ (x+delta/2) := by
  have h := (selected_exponent_margin6 x delta hd hx).2.le
  simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hQ.le h

theorem selected_index_published6 (Q delta : ℝ) (hQ : 1 < Q) (hd : 0 < delta)
    (c : Fin 3 → Fin 6 → ℝ) (s : MixedIndex6)
    (hs : s ∈ admissibleMixed6 c (delta/2)) :
    s ∈ publishedIndexSet6 Q delta c := by
  apply (published_index_exponent6 Q delta hQ c s).mpr
  have h := source_half_margin6 c delta s hs
  linarith

theorem selected_index_exact_slack6 (Q delta : ℝ) (hQ : 1 < Q)
    (c : Fin 3 → Fin 6 → ℝ) :
    admissibleMixed6 c (delta/2) = publishedIndexSet6 Q (3*delta/4) c := by
  ext s
  rw [mem_admissibleMixed6, published_index_exponent6 Q (3*delta/4) hQ]
  constructor <;> intro h <;> linarith

theorem selected_complement_gap6 (delta : ℝ) (c : Fin 3 → Fin 6 → ℝ)
    (s : MixedIndex6) (hs : s ∉ admissibleMixed6 c (delta/2)) :
    (∑ tau, c tau (s tau)) + (3*delta/4)/2 < 0 := by
  have h := lt_of_not_ge (fun h => hs ((mem_admissibleMixed6 c (delta/2) s).mpr h))
  linarith

theorem source_selected_index_published6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V)
    (s : MixedIndex6) (hs : s ∈ admissibleMixed6 R.c (R.delta/2)) :
    s ∈ publishedIndexSet6 (q.val ^ (11 : ℕ)) R.delta R.c :=
  selected_index_published6 _ _ (source_parameter_gt_one6 R q) R.delta_pos R.c s hs


def sourceWidthCoordinates6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ) :=
  weightedCoordinates6 (compoundFormEquiv42 L hL)
    (fun i => (q.val ^ (11 : ℕ)) ^ (R.c 0 i))
    (fun _ => Real.rpow_pos_of_pos
      (lt_trans zero_lt_one (source_parameter_gt_one6 R q)) _)

theorem source_first_five_width_gauge6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V)
    (j : Fin 5) :
    coordinateGauge6 (sourceWidthCoordinates6 R q)
      (integerReal (R.w q j.castSucc : Fin 6 → ℤ)) ≤
        (q.val ^ (11 : ℕ)) ^ (-R.delta) := by
  let Q := q.val ^ (11 : ℕ)
  have hQ : 0 < Q := lt_trans zero_lt_one (source_parameter_gt_one6 R q)
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  change ‖(compound L *ᵥ integerReal (R.w q j.castSucc : Fin 6 → ℤ)) i /
    Q ^ (R.c 0 i)‖ ≤ Q ^ (-R.delta)
  rw [norm_div, Real.norm_of_nonneg (Real.rpow_pos_of_pos hQ _).le,
    div_le_iff₀ (Real.rpow_pos_of_pos hQ _)]
  have hi := (R.frames q).2.2.2.2.1 j i
  calc
    _ ≤ Q ^ (R.c 0 i - R.delta) := hi
    _ = Q ^ (-R.delta) * Q ^ (R.c 0 i) := by
      rw [← Real.rpow_add hQ]
      congr 1
      ring

theorem source_penultimate_minimum_le6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    successiveRadius6 (directRealBasis42 A2 A3 q.val c2 c3)
      (sourceWidthCoordinates6 R q) 4 ≤ (q.val ^ (11 : ℕ)) ^ (-R.delta) := by
  apply successiveRadius6_le_family _ _ 4
    (fun j : Fin 5 => integerReal (R.w q j.castSucc : Fin 6 → ℤ))
    ((R.frames q).1.comp Fin.castSucc (Fin.castSucc_injective 5))
  · intro j
    rw [directRealBasis42_span]
    exact ⟨_, (R.w q j.castSucc).property, rfl⟩
  · exact source_first_five_width_gauge6 R q

theorem source_penultimate_minimum_strict_slack6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    0 < 3*R.delta/4 ∧
    successiveRadius6 (directRealBasis42 A2 A3 q.val c2 c3)
      (sourceWidthCoordinates6 R q) 4 <
        (q.val ^ (11 : ℕ)) ^ (-(3*R.delta/4)) := by
  refine ⟨by linarith [R.delta_pos], (source_penultimate_minimum_le6 R q).trans_lt ?_⟩
  exact Real.rpow_lt_rpow_of_exponent_lt (source_parameter_gt_one6 R q)
    (by linarith [R.delta_pos])


theorem source_primitive_dual_span6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    R.M q ≠ 0 ∧ (∑ i, R.a q i * R.M q i) = 1 ∧
    Ideal.span (Set.range (R.M q)) = ⊤ ∧
    Submodule.span ℚ {dualVector6 (fun j => (R.w q j : Fin 6 → ℤ))
      (sourceFrameIndependent6 R q)} =
      Submodule.span ℚ {fun i => (R.M q i : ℚ)} := by
  obtain ⟨a, ha, _, _, hi⟩ := source_normal_dual6 R q
  refine ⟨(R.normals q).1, (R.normals q).2.1, (R.normals q).2.2.1, ?_⟩
  have he : dualVector6 (fun j => (R.w q j : Fin 6 → ℤ))
      (sourceFrameIndependent6 R q) = a⁻¹ • (fun i => (R.M q i : ℚ)) := by
    ext i
    exact hi i
  rw [he]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero ha)) _

theorem source_dual_nonzero6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q) ≠ 0 := by
  obtain ⟨a, _, _, hs, _⟩ := source_normal_dual6 R q
  intro hz
  apply (R.normals q).1
  ext i
  have hi := hs i
  rw [hz, Pi.zero_apply, mul_zero] at hi
  exact_mod_cast hi


theorem source_parameter_unbounded6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) :
    ¬ BddAbove ((fun q : ℝ => q ^ (11 : ℕ)) '' V) :=
  power11_unbounded V R.unbounded

theorem source_satz51_preliminary6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    let Q := q.val ^ (11 : ℕ)
    let delta := 3*R.delta/4
    1 < Q ∧ 0 < delta ∧
    (∏ i : Fin 6, Q ^ (R.c 0 i) * (Q ^ (R.c 1 i) * Q ^ (R.c 2 i))) = 1 ∧
    admissibleMixed6 R.c (R.delta/2) = publishedIndexSet6 Q delta R.c ∧
    successiveRadius6 (directRealBasis42 A2 A3 q.val c2 c3)
      (sourceWidthCoordinates6 R q) 4 < Q ^ (-delta) ∧
    R.M q ≠ 0 ∧ (∑ i, R.a q i * R.M q i) = 1 ∧
    Ideal.span (Set.range (R.M q)) = ⊤ ∧
    dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q) ≠ 0 ∧
    Submodule.span ℚ {dualVector6 (fun j => (R.w q j : Fin 6 → ℤ))
      (sourceFrameIndependent6 R q)} =
      Submodule.span ℚ {fun i => (R.M q i : ℚ)} := by
  dsimp only
  have hm := source_penultimate_minimum_strict_slack6 R q
  have hn := source_primitive_dual_span6 R q
  exact ⟨source_parameter_gt_one6 R q, hm.1, source_unrounded_normalization6 R q,
    selected_index_exact_slack6 _ _ (source_parameter_gt_one6 R q) R.c,
    hm.2, hn.1, hn.2.1, hn.2.2.1, source_dual_nonzero6 R q, hn.2.2.2⟩

end CompoundFeasibility.SchlickeweiSatz51Selected6
