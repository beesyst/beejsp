import SubspaceBridge.SourceRelativeIndex6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiEquation4106
open SourceReadiness6 SourceHeightBounds6 SourceLocalUpper6 SourceNormalHeight
open SchlickeweiDualVanishing6 SourceProper6 SourceNormalIndex SourceWeights

theorem last_dual_adjugate6 (v : Matrix (Fin 6) (Fin 6) ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (k : Fin 6) :
    (rawNormal6 v k : ℚ) = (v.det : ℚ) * dualVector6 v hv k := by
  have hf := functional_lastDual42 (fun j i => (v j i : ℚ)) hv
    (normalForm6 (rawNormal6 v)) (by
      intro j
      rw [normalForm6_apply]
      change (∑ i, (rawNormal6 v i : ℚ) * (v j.castSucc i : ℚ)) = 0
      exact_mod_cast rawNormal6_annihilates v j)
  have hlast : normalForm6 (rawNormal6 v) (fun i => (v 5 i : ℚ)) = (v.det : ℚ) := by
    rw [normalForm6_apply]
    exact_mod_cast (show (∑ i, rawNormal6 v i * v 5 i) = v.det by
      simpa using rawNormal6_pairing v 5)
  rw [hlast] at hf
  have hc := congrArg (fun f : Module.Dual ℚ (Fin 6 → ℚ) => f (Pi.single k 1)) hf
  simpa [normalForm6, Pi.single_apply, dualVector6] using hc

theorem last_dual_real_minor6 (B : Matrix (Fin 6) (Fin 6) ℝ) (hB : B.det = 1)
    (v : Matrix (Fin 6) (Fin 6) ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (i : Fin 6) :
    |(v.det : ℝ)| * ‖dualFormValue6 B (dualVector6 v hv) i‖ =
      ‖((transformedFrame6 B v).submatrix Fin.castSucc i.succAbove).det‖ := by
  have hc (k : Fin 6) : (rawNormal6 v k : ℝ) =
      (v.det : ℝ) * algebraMap ℚ ℝ (dualVector6 v hv k) := by
    have h := congrArg (algebraMap ℚ ℝ) (last_dual_adjugate6 v hv k)
    simpa only [map_mul, map_intCast] using h
  have hs := transformed_minor_cofactor6 B v (rawNormal6 v) 1
    (fun k => by simp) i
  have hvv : cofactorValue6 B (rawNormal6 v) i =
      (v.det : ℝ) * rationalValue6 B (dualVector6 v hv) i := by
    simp only [cofactorValue6, rationalValue6, hc, Finset.mul_sum, mul_assoc]
  let D : Fin 6 → ℚ := dualVector6 v hv
  have he : rationalValue6 B (dualVector6 v hv) i = dualFormValue6 B (dualVector6 v hv) i := by
    with_reducible exact cofactor_dualForm6 B hB D i
  rw [Int.cast_one, one_mul, hvv, he] at hs
  have hn := congrArg (fun x : ℝ => ‖x‖) hs
  simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_eq_abs] using hn.symm

theorem direct_covolume_prime_bound6
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (q : ℝ) (c2 c3 : Fin 4 → ℝ) :
    (2 : ℝ) ^ (∑ i : Fin 6, Nat.ceil (JSP000334.qThreshold 2 q (pairWeights42 c2 i))) *
      3 ^ (∑ i : Fin 6, Nat.ceil (JSP000334.qThreshold 3 q (pairWeights42 c3 i))) ≤
      ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q c2 c3)) := by
  obtain ⟨b⟩ := directCompoundGroup42_has_basis A2 A3 q c2 c3
  have h := integerRealImage_padic_covolume_lower
    (directCompoundGroup42 A2 A3 q c2 c3) b (compound A2) (compound A3)
    (fun i => Nat.ceil (JSP000334.qThreshold 2 q (pairWeights42 c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 q (pairWeights42 c3 i)))
    (by
      intro x hx i
      have hi := (directLocal42_spec 2 A2 _ x).mp hx.1 i
      rw [← qThreshold_add42] at hi
      simpa only [pairWeights42, zpow_neg, zpow_natCast] using hi)
    (by
      intro x hx i
      have hi := (directLocal42_spec 3 A3 _ x).mp hx.2 i
      rw [← qThreshold_add42] at hi
      simpa only [pairWeights42, zpow_neg, zpow_natCast] using hi)
  simpa only [compound42_det_one A2 h2, compound42_det_one A3 h3,
    padicNorm.one, Rat.cast_one, one_mul] using h

theorem omitted_width_product6 (Q delta : ℝ) (hQ : 0 < Q) (c : Fin 6 → ℝ) (i : Fin 6) :
    (∏ k : Fin 5, Q ^ (c (i.succAbove k) - delta)) =
      (Q ^ (c i))⁻¹ * (∏ k : Fin 6, Q ^ (c k)) * Q ^ (-5 * delta) := by
  have hp : (∏ k : Fin 5, Q ^ c (i.succAbove k)) =
      (Q ^ c i)⁻¹ * (∏ k : Fin 6, Q ^ c k) := by
    rw [Fin.prod_univ_succAbove (fun k => Q ^ c k) i]
    rw [← mul_assoc, inv_mul_cancel₀ (Real.rpow_pos_of_pos hQ _).ne', one_mul]
  simp_rw [sub_eq_add_neg, Real.rpow_add hQ]
  rw [Finset.prod_mul_distrib, hp]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.rpow_mul_natCast hQ.le]
  congr 1
  ring

theorem real_dual_scale6 (B : Matrix (Fin 6) (Fin 6) ℝ) (D : Fin 6 → ℚ)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin 6) :
    ‖∑ k, (t * algebraMap ℚ ℝ (D k)) * B⁻¹.transpose i k‖ =
      t * ‖dualFormValue6 B D i‖ := by
  have he : (∑ k, (t * algebraMap ℚ ℝ (D k)) * B⁻¹.transpose i k) =
      t * dualFormValue6 B D i := by
    simp only [dualFormValue6, Finset.mul_sum, mul_assoc]
  rw [he, norm_mul, Real.norm_of_nonneg ht]

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem source_real_minor_bound6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) (i : Fin 6) :
    let Q := q.val ^ (11 : ℕ)
    let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
    ‖((transformedFrame6 (compound L) v).submatrix Fin.castSucc i.succAbove).det‖ ≤
      120 * ∏ k : Fin 5, Q ^ (R.c 0 (i.succAbove k) - R.delta) := by
  dsimp only
  apply real_det5_le
  · intro k
    exact (Real.rpow_pos_of_pos (pow_pos (lt_trans zero_lt_one (hQV q.val q.property)) _) _).le
  · intro j k
    change ‖transformedFrame6 (compound L)
      (Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))) j.castSucc (i.succAbove k)‖ ≤ _
    rw [transformedFrame6_apply]
    exact (R.frames q).2.2.2.2.1 j (i.succAbove k)

theorem source_width_product_le_covolume6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q : V) :
    (∏ i : Fin 6, (q.val ^ (11 : ℕ)) ^ (R.c 0 i)) ≤
      ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) := by
  let Q := q.val ^ (11 : ℕ)
  have hq : 1 < q.val := hQV q.val q.property
  have hqp : 0 < q.val := lt_trans zero_lt_one hq
  have hQp : 0 < Q := pow_pos hqp _
  have hb : (∑ i, R.c 0 i) + (∑ i, R.c 1 i) + (∑ i, R.c 2 i) = 0 := by
    simpa only [Fin.sum_univ_three] using R.weights_balance
  have heq : (∏ i : Fin 6, Q ^ (-R.c 1 i) * Q ^ (-R.c 2 i)) =
      ∏ i : Fin 6, Q ^ (R.c 0 i) := by
    simp_rw [← Real.rpow_add hQp]
    rw [← Real.rpow_sum_of_pos hQp _ Finset.univ, ← Real.rpow_sum_of_pos hQp _ Finset.univ]
    congr 1
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    linarith
  have hfinite (c : Fin 4 → ℝ) (i : Fin 6) :
      Q ^ (-finiteWeight c i) = q.val ^ (-pairWeights42 c i) := by
    dsimp only [Q, finiteWeight]
    rw [show -(pairWeights42 c i / 11) = (-pairWeights42 c i) / 11 by ring]
    exact davenport_rescaled_power42 _ _ hqp
  have hprod : (∏ i : Fin 6, Q ^ (R.c 0 i)) =
      ∏ i : Fin 6, q.val ^ (-pairWeights42 c2 i) * q.val ^ (-pairWeights42 c3 i) := by
    rw [← heq]
    apply Finset.prod_congr rfl
    intro i _
    rw [(R.finite_weights i).1, (R.finite_weights i).2, hfinite, hfinite]
  have hi (p : ℕ) (hp : 1 < p) (c : ℝ) :
      q.val ^ (-c) ≤ (p : ℝ) ^ Nat.ceil (JSP000334.qThreshold p q.val c) := by
    rw [← JSP000334.qThreshold_rpow p hp q.val c hq, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.le) (Nat.le_ceil _)
  calc
    _ = ∏ i : Fin 6, q.val ^ (-pairWeights42 c2 i) * q.val ^ (-pairWeights42 c3 i) := hprod
    _ ≤ ∏ i : Fin 6, (2 : ℝ) ^ Nat.ceil (JSP000334.qThreshold 2 q.val (pairWeights42 c2 i)) *
        3 ^ Nat.ceil (JSP000334.qThreshold 3 q.val (pairWeights42 c3 i)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact mul_nonneg (Real.rpow_pos_of_pos hqp _).le (Real.rpow_pos_of_pos hqp _).le
      · intro i _
        exact mul_le_mul (hi 2 (by decide) _) (hi 3 (by decide) _)
          (Real.rpow_pos_of_pos hqp _).le (by positivity)
    _ = (2 : ℝ) ^ (∑ i : Fin 6, Nat.ceil (JSP000334.qThreshold 2 q.val (pairWeights42 c2 i))) *
        3 ^ (∑ i : Fin 6, Nat.ceil (JSP000334.qThreshold 3 q.val (pairWeights42 c3 i))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
    _ ≤ _ := direct_covolume_prime_bound6 A2 A3 h2 h3 q.val c2 c3

theorem source_equation4106
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1) (q : V) (i : Fin 6) :
    let G := directCompoundGroup42 A2 A3 q.val c2 c3
    let Q := q.val ^ (11 : ℕ)
    let J := SourceRelativeIndex6.frameRelativeIndex G (R.w q)
    let d := ZLattice.covolume (integerRealImage G)
    let D := dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q)
    ‖∑ k, ((J : ℝ) * d * algebraMap ℚ ℝ (D k)) * (compound L)⁻¹.transpose i k‖ ≤
      120 * (Q ^ (R.c 0 i))⁻¹ * d * Q ^ (-5 * R.delta) := by
  let G := directCompoundGroup42 A2 A3 q.val c2 c3
  let Q := q.val ^ (11 : ℕ)
  let J := SourceRelativeIndex6.frameRelativeIndex G (R.w q)
  let d := ZLattice.covolume (integerRealImage G)
  let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
  let D := dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q)
  change ‖∑ k, ((J : ℝ) * d * algebraMap ℚ ℝ (D k)) * (compound L)⁻¹.transpose i k‖ ≤
    120 * (Q ^ (R.c 0 i))⁻¹ * d * Q ^ (-5 * R.delta)
  have hn := SourceRelativeIndex6.source_frame_normalization6 R q
  have hnorm : |(v.det : ℝ)| = (J : ℝ) * d := by
    with_reducible exact hn.2.2.2.1
  have hd : 0 < d := hn.2.2.2.2.2
  have hJ : (0 : ℝ) < J := by exact_mod_cast hn.2.1
  have hQp : 0 < Q := pow_pos (lt_trans zero_lt_one (hQV q.val q.property)) _
  have hA : 0 < Q ^ (R.c 0 i) := Real.rpow_pos_of_pos hQp _
  have hdecay : 0 < Q ^ (-5 * R.delta) := Real.rpow_pos_of_pos hQp _
  have hB : (compound L).det = 1 := by
    apply compound42_det_one
    exact hLdet
  have hdual := last_dual_real_minor6 (compound L) hB v (sourceFrameIndependent6 R q) i
  have hminor := source_real_minor_bound6 R q i
  have hwidth := source_width_product_le_covolume6 R h2 h3 q
  calc
    _ = ((J : ℝ) * d) * ‖dualFormValue6 (compound L) D i‖ :=
      real_dual_scale6 _ D _ (mul_pos hJ hd).le i
    _ = ‖((transformedFrame6 (compound L) v).submatrix Fin.castSucc i.succAbove).det‖ := by
      rw [← hnorm]
      exact hdual
    _ ≤ 120 * ∏ k : Fin 5, Q ^ (R.c 0 (i.succAbove k) - R.delta) := by
      with_reducible exact hminor
    _ = 120 * (Q ^ (R.c 0 i))⁻¹ * (∏ k : Fin 6, Q ^ (R.c 0 k)) * Q ^ (-5 * R.delta) := by
      rw [omitted_width_product6 Q R.delta hQp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hwidth (mul_nonneg (by norm_num) (inv_nonneg.mpr hA.le))) hdecay.le

end CompoundFeasibility.SchlickeweiEquation4106
