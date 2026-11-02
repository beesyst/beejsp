import SubspaceBridge.SchlickeweiRealPairing6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiAuxiliaryLine6
open SourceReadiness6 SchlickeweiAuxiliaryDual6 SchlickeweiIntegerPairing6
open SchlickeweiRealPairing6 SchlickeweiDualVanishing6 SchlickeweiSatz51Selected6

theorem pairing_power_cutoff6 (C delta : ℝ) (_hC : 0 < C) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ Q : ℝ, T < Q → 1 < Q → 6 * C * Q ^ (-delta) < 1 := by
  obtain ⟨T, hT, hcut⟩ := compound_gap_cutoff42 (6 * C) (2 * delta) (by linarith)
  refine ⟨T, hT, ?_⟩
  intro Q hTQ hQ
  have hQp : 0 < Q := lt_trans zero_lt_one hQ
  have hp : 0 < Q ^ delta := Real.rpow_pos_of_pos hQp _
  have hg : 6 * C < Q ^ delta := by simpa using hcut Q hTQ
  rw [Real.rpow_neg hQp.le]
  simpa only [div_eq_mul_inv] using (div_lt_one hp).mpr hg


theorem divisible_small_integer_zero6 (N : ℕ) (_hN : 0 < N) (z : ℤ)
    (hdiv : (N : ℤ) ∣ z) (hsmall : ‖(z : ℝ)‖ < (N : ℝ)) : z = 0 := by
  by_contra hz
  have hab : N ≤ z.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_le_of_dvd_ne_zero hdiv hz
  have hr : (N : ℝ) ≤ ‖(z : ℝ)‖ := by
    simpa only [Int.cast_natAbs, Int.cast_abs, Real.norm_eq_abs] using
      (show (N : ℝ) ≤ (z.natAbs : ℝ) by exact_mod_cast hab)
  exact (not_lt_of_ge hr) hsmall


variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem source_pairing_cutoff6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (C : ℝ) (hC : 0 < C) :
    ∃ B : ℝ, 1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ V ∧ B < q} ∧
      ∀ q : V, B < q.val → 6 * C * (q.val ^ (11 : ℕ)) ^ (-R.delta) < 1 := by
  obtain ⟨T, hT, hcut⟩ := pairing_power_cutoff6 C R.delta hC R.delta_pos
  refine ⟨T, hT, JSP000334.sourceDual_unbounded_tail3 V R.unbounded T, ?_⟩
  intro q hq
  have hq1 : 1 < q.val := hQV q.val q.property
  have hle : q.val ≤ q.val ^ (11 : ℕ) := le_self_pow₀ hq1.le (by decide)
  exact hcut _ (lt_of_lt_of_le hq hle) (source_parameter_gt_one6 R q)

theorem source_pairing_uniform_bound6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (C : ℝ) (hC : ∀ q : V,
      ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) ≤
        C * (primeProduct6 q.val c2 c3 : ℝ))
    (q : V) (y : Fin 6 → ℤ) (hy : sourceAuxiliaryInteger6 R q y) (j : Fin 5) :
    ‖(integerPairing6 (R.w q j.castSucc : Fin 6 → ℤ) y : ℝ)‖ ≤
      6 * C * (primeProduct6 q.val c2 c3 : ℝ) *
        (q.val ^ (11 : ℕ)) ^ (-R.delta) := by
  have hp : 0 ≤ (q.val ^ (11 : ℕ)) ^ (-R.delta) :=
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one (source_parameter_gt_one6 R q)) _).le
  calc
    _ ≤ 6 * ZLattice.covolume (integerRealImage
        (directCompoundGroup42 A2 A3 q.val c2 c3)) *
          (q.val ^ (11 : ℕ)) ^ (-R.delta) := source_real_pairing_bound6 R q y hy j
    _ ≤ 6 * (C * (primeProduct6 q.val c2 c3 : ℝ)) *
        (q.val ^ (11 : ℕ)) ^ (-R.delta) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC q) (by norm_num)) hp
    _ = _ := by ring

theorem source_auxiliary_pairings_zero6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) :
    ∃ B : ℝ, 1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ V ∧ B < q} ∧
      ∀ q : V, B < q.val → ∀ y : Fin 6 → ℤ,
        sourceAuxiliaryInteger6 R q y → ∀ j : Fin 5,
          integerPairing6 (R.w q j.castSucc : Fin 6 → ℤ) y = 0 := by
  obtain ⟨C, hCpos, hC⟩ := direct_uniform_covolume_upper6 A2 A3 h2 h3
  obtain ⟨B, hB, htail, hcut⟩ := source_pairing_cutoff6 R C hCpos
  refine ⟨B, hB, htail, ?_⟩
  intro q hq y hy j
  have hP : 0 < primeProduct6 q.val c2 c3 := primeProduct_pos6 _ _ _
  have hPR : (0 : ℝ) < primeProduct6 q.val c2 c3 := by exact_mod_cast hP
  have hsmall : ‖(integerPairing6 (R.w q j.castSucc : Fin 6 → ℤ) y : ℝ)‖ <
      (primeProduct6 q.val c2 c3 : ℝ) := by
    calc
      _ ≤ 6 * C * (primeProduct6 q.val c2 c3 : ℝ) *
          (q.val ^ (11 : ℕ)) ^ (-R.delta) :=
        source_pairing_uniform_bound6 R C (fun q => hC q.val c2 c3) q y hy j
      _ = (6 * C * (q.val ^ (11 : ℕ)) ^ (-R.delta)) *
          (primeProduct6 q.val c2 c3 : ℝ) := by ring
      _ < 1 * (primeProduct6 q.val c2 c3 : ℝ) := mul_lt_mul_of_pos_right (hcut q hq) hPR
      _ = _ := one_mul _
  exact divisible_small_integer_zero6 _ hP _
    (source_pairing_primeProduct6 R h2 h3 q y hy j) hsmall


theorem rational_annihilator_line6 (u : Fin 6 → Fin 6 → ℚ)
    (hu : LinearIndependent ℚ u) (y : Fin 6 → ℚ)
    (hann : ∀ j : Fin 5, (∑ i, u j.castSucc i * y i) = 0) :
    y ∈ Submodule.span ℚ {fun i => rationalFrameDual42 u hu 5 (Pi.single i 1)} := by
  let fy : Module.Dual ℚ (Fin 6 → ℚ) := ∑ i, y i • LinearMap.proj i
  have hf : ∀ j : Fin 5, fy (u j.castSucc) = 0 := by
    intro j
    simpa only [fy, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul, mul_comm] using hann j
  have he := functional_lastDual42 u hu fy hf
  have hc (i : Fin 6) : y i = fy (u 5) * rationalFrameDual42 u hu 5 (Pi.single i 1) := by
    have hi := congrArg (fun f : Module.Dual ℚ (Fin 6 → ℚ) => f (Pi.single i 1)) he
    simpa [fy, Pi.single_apply] using hi
  have hy : y = fy (u 5) • (fun i => rationalFrameDual42 u hu 5 (Pi.single i 1)) := by
    funext i
    exact hc i
  rw [hy]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))


theorem source_zero_pairings_line6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (q : V) (y : Fin 6 → ℤ)
    (hz : ∀ j : Fin 5, integerPairing6 (R.w q j.castSucc : Fin 6 → ℤ) y = 0) :
    (fun i => (y i : ℚ)) ∈ Submodule.span ℚ {fun i => (R.M q i : ℚ)} := by
  have hrat : ∀ j : Fin 5,
      (∑ i, ((R.w q j.castSucc : Fin 6 → ℤ) i : ℚ) * (y i : ℚ)) = 0 := by
    intro j
    have hi : (∑ i, (R.w q j.castSucc : Fin 6 → ℤ) i * y i) = 0 := hz j
    exact_mod_cast hi
  have hh := rational_annihilator_line6
    (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) (sourceFrameIndependent6 R q)
    (fun i => (y i : ℚ)) hrat
  change (fun i => (y i : ℚ)) ∈ Submodule.span ℚ
    {dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q)} at hh
  rw [(source_primitive_dual_span6 R q).2.2.2] at hh
  exact hh


theorem source_auxiliary_pointwise6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) :
    ∃ B : ℝ, 1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ V ∧ B < q} ∧
      ∀ q : V, B < q.val → R.M q ≠ 0 ∧ ∀ y : Fin 6 → ℤ,
        sourceAuxiliaryInteger6 R q y →
          (∀ j : Fin 5, integerPairing6 (R.w q j.castSucc : Fin 6 → ℤ) y = 0) ∧
          (fun i => (y i : ℚ)) ∈ Submodule.span ℚ {fun i => (R.M q i : ℚ)} := by
  obtain ⟨B, hB, htail, hz⟩ := source_auxiliary_pairings_zero6 R h2 h3
  refine ⟨B, hB, htail, ?_⟩
  intro q hq
  refine ⟨(source_primitive_dual_span6 R q).1, ?_⟩
  intro y hy
  have hzero := hz q hq y hy
  exact ⟨hzero, source_zero_pairings_line6 R q y hzero⟩

theorem source_auxiliary_line6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) :
    ∃ B : ℝ, 1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ V ∧ B < q} ∧
      ∀ q : V, B < q.val → ∀ y : Fin 6 → ℤ,
        sourceAuxiliaryInteger6 R q y →
          (fun i => (y i : ℚ)) ∈ Submodule.span ℚ {fun i => (R.M q i : ℚ)} := by
  obtain ⟨B, hB, htail, hpoint⟩ := source_auxiliary_pointwise6 R h2 h3
  exact ⟨B, hB, htail, fun q hq y hy => ((hpoint q hq).2 y hy).2⟩

end CompoundFeasibility.SchlickeweiAuxiliaryLine6
