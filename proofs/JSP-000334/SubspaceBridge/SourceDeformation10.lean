import SubspaceBridge.OriginalDeformation10
import SubspaceBridge.SourceBounds10
open scoped BigOperators Matrix
namespace CompoundFeasibility.OriginalDeformation10
noncomputable section

theorem deformation_decay_absorb10 (r C Q delta : ℝ) (hQ : 1 < Q)
    (hroot : r^(10 : ℕ) < C*Q^(-delta))
    (hcut : (1024 : ℝ)^10*C < Q^(delta/6)) :
    1024*r < Q^(-5*delta/60) := by
  have hq : 0 < Q := zero_lt_one.trans hQ
  have he : (Q^(-5*delta/60))^(10 : ℕ) = Q^(-5*delta/6) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hq.le]
    congr 1
    ring
  have hmul : Q^(delta/6)*Q^(-delta) = Q^(-5*delta/6) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  have hh : (1024*r)^(10 : ℕ) < (Q^(-5*delta/60))^(10 : ℕ) := by
    rw [mul_pow,he]
    calc
      _ < (1024 : ℝ)^10*(C*Q^(-delta)) := mul_lt_mul_of_pos_left hroot (by norm_num)
      _ = ((1024 : ℝ)^10*C)*Q^(-delta) := by ring
      _ < Q^(delta/6)*Q^(-delta) :=
        mul_lt_mul_of_pos_right hcut (Real.rpow_pos_of_pos hq _)
      _ = _ := hmul
  exact lt_of_pow_lt_pow_left₀ 10 (Real.rpow_pos_of_pos hq _).le hh

theorem rescaled_small10 (Q delta x : ℝ) (hQ : 0 < Q)
    (hx : x < Q^(-5*delta/60)) : x < (Q^(5 : ℕ))^(-(delta/60)) := by
  have he : (Q^(5 : ℕ))^(-(delta/60)) = Q^(-5*delta/60) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hQ.le]
    congr 1
    ring
  rw [he]
  exact hx

theorem source_uniform_radius10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ C K T : ℝ, 0 < C ∧ 0 < K ∧ K = C^((1 : ℝ)/10) ∧ 1 < T ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ),
      (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i) = 0) → T < Q →
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 8 <
        sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9*Q^(-delta) →
      let lam := sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3
      gapRadius10 lam^(10 : ℕ) < C*Q^(-delta) ∧
      gapRadius10 lam < K*Q^(-delta/10) ∧ 1024*gapRadius10 lam < Q^(-5*delta/60) := by
  obtain ⟨_,C,_,hC,hbounds⟩ :=
    source_original_uniform_minima_two_sided10 A2 A3 L h2 h3 hL
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 ((1024 : ℝ)^10*C) (delta/3) (by positivity)
  refine ⟨C,C^((1 : ℝ)/10),T,hC,Real.rpow_pos_of_pos hC _,rfl,hT,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb hTQ hgap
  have hp := (sourceMinima10_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1
  have hroot := gapRadius10_quantitative _ hp C Q delta hQ (hbounds Q hQ c0 c2 c3 hc2 hc3 hb).2 hgap
  have hcut' : (1024 : ℝ)^10*C < Q^(delta/6) := by
    convert hcut Q hTQ using 1 <;> congr 1 <;> ring
  exact ⟨hroot,gapRadius10_root_bound _ hp C Q delta hC hQ hroot,
    deformation_decay_absorb10 _ C Q delta hQ hroot hcut'⟩

theorem integerReal_norm_lower10 (z : Fin 10 → ℤ) (hz : z ≠ 0) : 1 ≤ ‖integerReal z‖ := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hz
  have hi' : z i ≠ 0 := by simpa only [Pi.zero_apply] using hi
  have ha : (1 : ℝ) ≤ |(z i : ℝ)| := by exact_mod_cast Int.one_le_abs hi'
  exact ha.trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (integerReal z) i)

theorem original_unweighted_bound10 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 10 → ℝ) (hc : ∀ i, |c0 i| ≤ 1) (x : Fin 10 → ℝ) :
    ‖originalFormEquiv10 L hL x‖ ≤ coordinateGauge10 (originalCoordinates10 L hL Q hQ c0) x * Q := by
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  have hh := (originalCoordinates10_bounds L hL Q hQ c0 x _).mp le_rfl i
  have he : Q^(c0 i) ≤ Q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ.le (abs_le.mp (hc i)).2
  exact hh.trans (mul_le_mul_of_nonneg_left he (norm_nonneg _))

theorem source_first_lower10 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) :
    ∃ D : ℝ, 0 < D ∧ ∀ (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
      (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ), (∀ i, |c0 i| ≤ 1) →
      1/(D*Q) ≤ sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 0 := by
  let E := (originalFormEquiv10 L hL).toContinuousLinearEquiv
  let D := max 1 ‖E.symm.toContinuousLinearMap‖
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨D,hD,?_⟩
  intro A2 A3 Q hQ c0 c2 c3 hc
  obtain ⟨u,hu,_,_,hatt,_⟩ := exists_sourceMinima10_attaining A2 A3 L hL Q hQ c0 c2 c3
  have hz : (u 0 : Fin 10 → ℤ) ≠ 0 := by
    intro hz
    apply hu.ne_zero 0
    rw [hz,map_zero]
  have hnorm := integerReal_norm_lower10 (u 0) hz
  have hinv : ‖integerReal (u 0 : Fin 10 → ℤ)‖ ≤ D*‖originalFormEquiv10 L hL
      (integerReal (u 0 : Fin 10 → ℤ))‖ := by
    have hi := E.symm.toContinuousLinearMap.le_opNorm (E (integerReal (u 0 : Fin 10 → ℤ)))
    simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at hi
    exact hi.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hg := original_unweighted_bound10 L hL Q hQ c0 hc (integerReal (u 0 : Fin 10 → ℤ))
  rw [hatt] at hg
  apply (div_le_iff₀ (mul_pos hD (zero_lt_one.trans hQ))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hg hD.le,hnorm.trans hinv]

theorem source_uniform_basic_bounds10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ c C D K : ℝ, 0 < c ∧ 0 < C ∧ 0 < D ∧ 0 < K ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ),
      (∀ i, |c0 i| ≤ 1) → (∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) →
      (∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i)) = 0 →
      let lam := sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3
      c ≤ (∏ i, lam i) ∧ (∏ i, lam i) ≤ C ∧ 1/(D*Q) ≤ lam 0 ∧ lam 9 ≤ K*Q^3 := by
  obtain ⟨c,C,hc,hC,hbounds⟩ := source_original_uniform_minima_two_sided10 A2 A3 L h2 h3 hL
  obtain ⟨D,hD,hfirst⟩ := source_first_lower10 L hL
  obtain ⟨K,hK,hlast⟩ := source_last_upper10 A2 A3 L hL
  refine ⟨c,C,D,K,hc,hC,hD,hK,?_⟩
  intro Q hQ c0 c2 c3 hc0 hc2 hc3 hb
  have hbd := hbounds Q hQ c0 c2 c3 (fun i => (hc2 i).2) (fun i => (hc3 i).2) hb
  exact ⟨hbd.1,hbd.2,hfirst A2 A3 Q hQ c0 c2 c3 hc0,hlast Q hQ c0 c2 c3 hc0 hc2 hc3⟩

theorem gapRadius10_le_root (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (C : ℝ) (hC : 0 < C) (hprod : (∏ i, lam i) ≤ C) : gapRadius10 lam ≤ C^((1 : ℝ)/10) := by
  have hb : gapRadius10 lam^(10 : ℕ) ≤ C := by
    rw [gapRadius10_source_formula lam hp,mul_div_assoc]
    have hr : lam 8/lam 9 ≤ 1 := (div_le_one (hp 9)).mpr (hm (by decide))
    exact (mul_le_mul_of_nonneg_left hr (Finset.prod_pos (fun i _ => hp i)).le).trans
      (by simpa only [mul_one] using hprod)
  apply le_of_pow_le_pow_left₀ (by decide : (10 : ℕ) ≠ 0) (Real.rpow_pos_of_pos hC _).le
  rw [fourthRoot10_power C hC]
  exact hb

theorem gapRadius10_lower_scaled (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (c : ℝ) (hc : 0 < c) (hprod : c ≤ ∏ i, lam i) :
    c^((1 : ℝ)/10)*lam 8 ≤ gapRadius10 lam*lam 9 := by
  have hmul : c*(lam 8)^10 ≤ (∏ i, lam i)*lam 8*(lam 9)^9 := by
    calc
      _ ≤ (∏ i, lam i)*(lam 8)^10 := mul_le_mul_of_nonneg_right hprod (by positivity)
      _ = ((∏ i, lam i)*lam 8)*(lam 8)^9 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hp 8).le (hm (by decide : (8 : Fin 10) ≤ 9)) 9)
        (mul_pos (Finset.prod_pos (fun j _ => hp j)) (hp 8)).le
  have he : (gapRadius10 lam*lam 9)^(10 : ℕ) = (∏ i, lam i)*lam 8*(lam 9)^9 := by
    rw [mul_pow,gapRadius10_source_formula lam hp]
    field_simp [(hp 9).ne']
    ring
  apply le_of_pow_le_pow_left₀ (by decide : (10 : ℕ) ≠ 0)
    (mul_pos (gapRadius10_pos lam hp) (hp 9)).le
  rw [mul_pow,fourthRoot10_power c hc,he]
  exact hmul

theorem gapDeformation10_polynomial_bounds (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) (c C D K Q : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hD : 0 < D) (hQ : 0 < Q) (hprodlo : c ≤ ∏ i, lam i) (hprodhi : (∏ i, lam i) ≤ C)
    (hfirst : 1/(D*Q) ≤ lam 0) (hlast : lam 9 ≤ K*Q^3) :
    ∀ i, gapDeformation10 lam i ≤ (D*C^((1 : ℝ)/10))*Q ∧
      (gapDeformation10 lam i)⁻¹ ≤ (K/c^((1 : ℝ)/10))*Q^3 := by
  have hr := gapRadius10_le_root lam hp hm C hC hprodhi
  have hlo := gapRadius10_lower_scaled lam hp hm c hc hprodlo
  have hcp : 0 < c^((1 : ℝ)/10) := Real.rpow_pos_of_pos hc _
  have hfirst' : 1 ≤ D*Q*lam 0 := by
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos hD hQ)).mp hfirst
  intro i
  constructor
  · apply (div_le_iff₀ (hp (min i 8))).mpr
    have hfi : 1 ≤ D*Q*lam (min i 8) :=
      hfirst'.trans (mul_le_mul_of_nonneg_left (hm (Fin.zero_le _)) (mul_pos hD hQ).le)
    have hmul := mul_le_mul_of_nonneg_left hfi (Real.rpow_pos_of_pos hC ((1 : ℝ)/10)).le
    nlinarith
  · change (gapRadius10 lam/lam (min i 8))⁻¹ ≤ _
    rw [inv_div]
    have hmini : lam (min i 8) ≤ lam 8 := hm (min_le_right _ _)
    have hdiv : lam 8/gapRadius10 lam ≤ lam 9/c^((1 : ℝ)/10) :=
      (div_le_div_iff₀ (gapRadius10_pos lam hp) hcp).mpr (by nlinarith [hlo])
    calc
      _ ≤ lam 8/gapRadius10 lam := div_le_div_of_nonneg_right hmini (gapRadius10_pos lam hp).le
      _ ≤ lam 9/c^((1 : ℝ)/10) := hdiv
      _ ≤ (K*Q^3)/c^((1 : ℝ)/10) := div_le_div_of_nonneg_right hlast hcp.le
      _ = _ := by ring

theorem deformedWidths10_polynomial_bounds (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) (c C D K Q : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hD : 0 < D) (hK : 0 < K) (hQ : 1 < Q) (c0 : Fin 10 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hprodlo : c ≤ ∏ i, lam i) (hprodhi : (∏ i, lam i) ≤ C)
    (hfirst : 1/(D*Q) ≤ lam 0) (hlast : lam 9 ≤ K*Q^3)
    (sigma : Equiv.Perm (Fin 10)) :
    ∀ i, deformedWidths10 Q c0 (gapDeformation10 lam) sigma i ≤
        max (D*C^((1 : ℝ)/10)) (K/c^((1 : ℝ)/10))*Q^4 ∧
      (deformedWidths10 Q c0 (gapDeformation10 lam) sigma i)⁻¹ ≤
        max (D*C^((1 : ℝ)/10)) (K/c^((1 : ℝ)/10))*Q^4 := by
  have hq : 0 < Q := zero_lt_one.trans hQ
  have hb := gapDeformation10_polynomial_bounds lam hp hm c C D K Q hc hC hD hq
    hprodlo hprodhi hfirst hlast
  have hd := gapDeformation10_pos lam hp
  let B := max (D*C^((1 : ℝ)/10)) (K/c^((1 : ℝ)/10))
  have hB : 0 < B := (mul_pos hD (Real.rpow_pos_of_pos hC _)).trans_le (le_max_left _ _)
  intro i
  have hw : 0 < Q^(c0 i) := Real.rpow_pos_of_pos hq _
  have ha : Q^(c0 i) ≤ Q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ.le (abs_le.mp (hc0 i)).2
  have hai : (Q^(c0 i))⁻¹ ≤ Q := by
    rw [← Real.rpow_neg hq.le]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ.le
      (show -c0 i ≤ 1 by linarith [(abs_le.mp (hc0 i)).1])
  have hdi : (gapDeformation10 lam (sigma i))⁻¹ ≤ B*Q^3 :=
    (hb (sigma i)).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hdhi : gapDeformation10 lam (sigma i) ≤ B*Q^3 := by
    have hq3 : Q ≤ Q^3 := le_self_pow₀ hQ.le (by decide)
    exact ((hb (sigma i)).1.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hq.le)).trans
        (mul_le_mul_of_nonneg_left hq3 hB.le)
  constructor
  · change Q^(c0 i)/gapDeformation10 lam (sigma i) ≤ _
    rw [div_eq_mul_inv]
    have h := mul_le_mul ha hdi (inv_nonneg.mpr (hd _).le) hq.le
    convert h using 1 <;> ring
  · change (Q^(c0 i)/gapDeformation10 lam (sigma i))⁻¹ ≤ _
    rw [inv_div,div_eq_mul_inv]
    have h := mul_le_mul hdhi hai (inv_nonneg.mpr hw.le) (mul_pos hB (pow_pos hq 3)).le
    convert h using 1 <;> ring

theorem originalDeformedBody10_mem (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 10 → ℝ) (d : Fin 10 → ℝ)
    (sigma : Equiv.Perm (Fin 10)) (hd : ∀ i, 0 < d i) (x : Fin 10 → ℝ) :
    x ∈ parallelepipedBody10 (originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd) ↔
      ∀ i, |(L *ᵥ x) i| ≤ deformedWidths10 Q c0 d sigma i := by
  rw [mem_parallelepipedBody10_iff]
  change ‖originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd x‖ ≤ 1 ↔ _
  rw [pi_norm_le_iff_of_nonempty]
  apply forall_congr'
  intro i
  rw [Real.norm_eq_abs,originalDeformedCoordinates10_apply,abs_div,abs_mul,
    abs_of_pos (hd _),abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _)]
  change d (sigma i)*|(L *ᵥ x) i|/Q^(c0 i) ≤ 1 ↔ |(L *ᵥ x) i| ≤ Q^(c0 i)/d (sigma i)
  rw [div_le_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _),
    le_div_iff₀ (hd _),one_mul]
  constructor <;> intro h <;> simpa only [mul_comm] using h

theorem originalBody_gauge10 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 10 → ℝ) :
    parallelepipedBody10 (originalCoordinates10 L hL Q hQ c0) = originalBody10 L Q c0 := by
  ext x
  rw [mem_parallelepipedBody10_iff,originalBody10_mem_iff L hL Q hQ c0 x]
  rfl

theorem rescaled_power10 (Q c : ℝ) (hQ : 0 < Q) : (Q^(5 : ℕ))^(c/5) = Q^c := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hQ.le]
  congr 1
  ring

theorem rescaled_threshold10 (p : ℕ) (Q c : ℝ) :
    JSP000334.qThreshold p (Q^(5 : ℕ)) (c/5) = JSP000334.qThreshold p Q c := by
  unfold JSP000334.qThreshold
  rw [Real.log_pow]
  ring

theorem source_finite_cutoff10 (Q : ℝ) (hQ : 1 < Q) (c : Fin 10 → ℝ)
    (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 0) : ∀ i, Q^(-c i) < Q^(5 : ℕ) := by
  intro i
  have hb : Q^(-c i) ≤ Q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ.le
      (show -c i ≤ 1 by linarith [(hc i).1])
  exact hb.trans_lt (by simpa only [pow_one] using pow_lt_pow_right₀ hQ (by decide : (1 : ℕ) < 5))

def deformationReady10 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 10 → ℝ) (delta : ℝ)
    (u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3) : Prop :=
  let lam := sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3
  let d := gapDeformation10 lam
  0 < gapRadius10 lam ∧ gapRadius10 lam^10 = (∏ i, lam i)*lam 8/lam 9 ∧
  ∃ hd : ∀ i, 0 < d i, (∏ i, d i) = 1 ∧ Antitone d ∧ Monotone (fun i => d i*lam i) ∧
  ∃ sigma : Equiv.Perm (Fin 10),
    (∀ i, 0 < deformedWidths10 Q c0 d sigma i) ∧
    (∏ i, deformedWidths10 Q c0 d sigma i)*(∏ i, Q^(c2 i+c3 i)) = 1 ∧
    (∀ j, d j*lam j/1024 ≤ originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j ∧
      originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j ≤ 1024*(d j*lam j)) ∧
    MeasureTheory.volume.real (parallelepipedBody10 (originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd)) =
      MeasureTheory.volume.real (originalBody10 L Q c0) ∧
    (∀ j : Fin 10, ∀ z : originalSourceGroup10 A2 A3 Q c2 c3,
      integerReal (z : Fin 10 → ℤ) ∉ minimaFlag10 (fun i => integerReal (u i : Fin 10 → ℤ)) j →
      d j*lam j/1024 ≤ coordinateGauge10 (originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd)
        (integerReal (z : Fin 10 → ℤ))) ∧
    originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd 8 ≤ 1024*gapRadius10 lam ∧
    originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd 8 < Q^(-5*delta/60) ∧
    originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd 8 < (Q^(5 : ℕ))^(-(delta/60)) ∧
    (∀ i, deformedWidths10 Q c0 d sigma i < Q^(5 : ℕ) ∧
      (deformedWidths10 Q c0 d sigma i)⁻¹ < Q^(5 : ℕ) ∧
      Q^(-c2 i) < Q^(5 : ℕ) ∧ Q^(-c3 i) < Q^(5 : ℕ)) ∧
    (∀ x, x ∈ parallelepipedBody10 (originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd) ↔
      ∀ i, |(L *ᵥ x) i| ≤ deformedWidths10 Q c0 d sigma i) ∧
    (∀ i, (Q^(5 : ℕ))^(c2 i/5) = Q^(c2 i) ∧ (Q^(5 : ℕ))^(c3 i/5) = Q^(c3 i)) ∧
    (∀ (p : ℕ) i, JSP000334.qThreshold p (Q^(5 : ℕ)) (c2 i/5) = JSP000334.qThreshold p Q (c2 i) ∧
      JSP000334.qThreshold p (Q^(5 : ℕ)) (c3 i/5) = JSP000334.qThreshold p Q (c3 i))

theorem source_uniform_deformation10 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ),
      (∀ i, |c0 i| ≤ 1) → (∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) → (∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) →
      (∑ i, (c0 i+c2 i+c3 i)) = 0 → T < Q →
      ∀ u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun i => integerReal (u i : Fin 10 → ℤ)) →
      (∀ i, coordinateGauge10 (originalCoordinates10 L hL Q hQ c0)
        (integerReal (u i : Fin 10 → ℤ)) = sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 i) →
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 8 <
        sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9*Q^(-delta) →
      deformationReady10 A2 A3 L hL Q hQ c0 c2 c3 delta u := by
  obtain ⟨c,C,D,K,hc,hC,hD,hK,hbasic⟩ := source_uniform_basic_bounds10 A2 A3 L h2 h3 hL
  let B := max (D*C^((1 : ℝ)/10)) (K/c^((1 : ℝ)/10))
  obtain ⟨T0,hT0,hcut⟩ := compound_gap_cutoff42 ((1024 : ℝ)^10*C) (delta/3) (by positivity)
  let T := max T0 (B+1)
  refine ⟨T,hT0.trans_le (le_max_left _ _),?_⟩
  intro Q hQ c0 c2 c3 hc0 hc2 hc3 hb hTQ u hu hatt hgap
  let lam := sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3
  obtain ⟨hp,hm⟩ := sourceMinima10_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  obtain ⟨hlo,hhi,hfirst,hlast⟩ := hbasic Q hQ c0 c2 c3 hc0 hc2 hc3 hb
  have hroot := gapRadius10_quantitative lam hp C Q delta hQ hhi hgap
  have hcuteq : (1024 : ℝ)^10*C < Q^(delta/6) := by
    convert hcut Q ((le_max_left _ _).trans_lt hTQ) using 1 <;> congr 1 <;> ring
  have hrsmall := deformation_decay_absorb10 _ C Q delta hQ hroot hcuteq
  obtain ⟨hdp,hprod,hanti,hscaled,sigma,hbounds,hvol,hsep⟩ :=
    source_original_davenport10 A2 A3 L hL Q hQ c0 c2 c3 u hu hatt
  have hu2 : originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3
      (gapDeformation10 lam) sigma hdp 8 ≤ 1024*gapRadius10 lam := by
    have h := (hbounds 8).2
    rw [gapDeformation10_first lam hp 8 le_rfl] at h
    exact h
  have hsmall := hu2.trans_lt hrsmall
  have hwidth := deformedWidths10_polynomial_bounds lam hp hm c C D K Q hc hC hD hK hQ
    c0 hc0 hlo hhi hfirst hlast sigma
  have hBQ : B < Q := by
    have hBT : B+1 ≤ T := le_max_right _ _
    linarith
  have hlarge : B*Q^4 < Q^(5 : ℕ) := by
    calc
      _ < Q*Q^4 := mul_lt_mul_of_pos_right hBQ (pow_pos (zero_lt_one.trans hQ) 4)
      _ = _ := by ring
  refine ⟨gapRadius10_pos lam hp,gapRadius10_source_formula lam hp,hdp,hprod,hanti,hscaled,sigma,
    deformedWidths10_pos Q (zero_lt_one.trans hQ) c0 _ hdp sigma,
    deformedWidths10_balance Q (zero_lt_one.trans hQ) c0 c2 c3 _ hprod sigma hb,
    hbounds,hvol.trans (congrArg (fun S => MeasureTheory.volume.real S) (originalBody_gauge10 L hL Q hQ c0)),hsep,hu2,hsmall,rescaled_small10 Q delta _ (zero_lt_one.trans hQ) hsmall,?_,
    originalDeformedBody10_mem L hL Q hQ c0 _ sigma hdp,?_,?_⟩
  · intro i
    exact ⟨(hwidth i).1.trans_lt hlarge,(hwidth i).2.trans_lt hlarge,
      source_finite_cutoff10 Q hQ c2 hc2 i,source_finite_cutoff10 Q hQ c3 hc3 i⟩
  · intro i
    exact ⟨rescaled_power10 Q (c2 i) (zero_lt_one.trans hQ),rescaled_power10 Q (c3 i) (zero_lt_one.trans hQ)⟩
  · intro p i
    exact ⟨rescaled_threshold10 p Q (c2 i),rescaled_threshold10 p Q (c3 i)⟩


end
end CompoundFeasibility.OriginalDeformation10
