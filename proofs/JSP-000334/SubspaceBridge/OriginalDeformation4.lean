import SubspaceBridge.OriginalMinimaProduct4
import SubspaceBridge.OriginalVariableGap4
import SubspaceBridge.Davenport4
import SubspaceBridge.OriginalLastDual4
open scoped BigOperators Matrix
namespace CompoundFeasibility.OriginalDeformation4
noncomputable section

def gapRadius4 (lam : Fin 4 → ℝ) : ℝ :=
  (lam 0 * lam 1 * lam 2 ^ 2) ^ ((1 : ℝ) / 4)

def gapDeformation4 (lam : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  gapRadius4 lam / lam (min i 2)

theorem gapRadius4_pos (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) : 0 < gapRadius4 lam :=
  Real.rpow_pos_of_pos (mul_pos (mul_pos (hp 0) (hp 1)) (pow_pos (hp 2) 2)) _

theorem gapRadius4_power (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    gapRadius4 lam ^ (4 : ℕ) = lam 0 * lam 1 * lam 2 ^ 2 := by
  unfold gapRadius4
  have hpos : 0 < lam 0 * lam 1 * lam 2 ^ 2 :=
    mul_pos (mul_pos (hp 0) (hp 1)) (pow_pos (hp 2) 2)
  rw [← Real.rpow_natCast,← Real.rpow_mul hpos.le]
  norm_num

theorem gapRadius4_source_formula (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    gapRadius4 lam ^ (4 : ℕ) = (∏ i, lam i) * lam 2 / lam 3 := by
  rw [gapRadius4_power lam hp]
  rw [Fin.prod_univ_four]
  field_simp [(hp 3).ne']
  ring

theorem gapDeformation4_pos (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    ∀ i, 0 < gapDeformation4 lam i := fun i => div_pos (gapRadius4_pos lam hp) (hp _)

theorem gapDeformation4_product (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    (∏ i, gapDeformation4 lam i) = 1 := by
  change (∏ i, gapRadius4 lam / lam (min i 2)) = 1
  rw [Finset.prod_div_distrib]
  have hn : (∏ _i : Fin 4, gapRadius4 lam) = gapRadius4 lam ^ (4 : ℕ) := by simp
  have hden : (∏ i : Fin 4, lam (min i 2)) = lam 0 * lam 1 * lam 2 ^ 2 := by
    simp only [Fin.prod_univ_succ]
    change lam 0 * (lam 1 * (lam 2 * (lam 2 * 1))) = _
    ring
  rw [hn,hden,gapRadius4_power lam hp]
  exact div_self (ne_of_gt (mul_pos (mul_pos (hp 0) (hp 1)) (pow_pos (hp 2) 2)))

theorem gapDeformation4_antitone (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) : Antitone (gapDeformation4 lam) := by
  intro i j hij
  exact div_le_div_of_nonneg_left (gapRadius4_pos lam hp).le (hp _)
    (hm (min_le_min hij le_rfl))

theorem gapDeformation4_first (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (i : Fin 4) (hi : i ≤ 2) : gapDeformation4 lam i * lam i = gapRadius4 lam := by
  unfold gapDeformation4
  rw [min_eq_left hi]
  exact div_mul_cancel₀ _ (hp i).ne'

theorem gapDeformation4_last (lam : Fin 4 → ℝ) :
    gapDeformation4 lam 3 * lam 3 = gapRadius4 lam * lam 3 / lam 2 := by
  change (gapRadius4 lam / lam 2) * lam 3 = _
  ring

theorem gapDeformation4_scaled (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) : Monotone (fun i => gapDeformation4 lam i * lam i) := by
  have hlast : gapRadius4 lam ≤ gapDeformation4 lam 3 * lam 3 := by
    calc
      _ = (gapRadius4 lam / lam 2) * lam 2 := (div_mul_cancel₀ _ (hp 2).ne').symm
      _ ≤ (gapRadius4 lam / lam 2) * lam 3 :=
        mul_le_mul_of_nonneg_left (hm (by decide : (2 : Fin 4) ≤ 3))
          (div_pos (gapRadius4_pos lam hp) (hp 2)).le
      _ = _ := rfl
  intro i j hij
  change gapDeformation4 lam i * lam i ≤ gapDeformation4 lam j * lam j
  by_cases hj : j ≤ 2
  · rw [gapDeformation4_first lam hp i (hij.trans hj),gapDeformation4_first lam hp j hj]
  · have hj3 : j = 3 := by omega
    subst j
    by_cases hi : i ≤ 2
    · rw [gapDeformation4_first lam hp i hi]
      exact hlast
    · have hi3 : i = 3 := by omega
      subst i
      exact le_rfl

theorem gapRadius4_quantitative (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (C Q delta : ℝ) (hQ : 1 < Q) (hprod : (∏ i, lam i) ≤ C)
    (hgap : lam 2 < lam 3 * Q^(-delta)) :
    gapRadius4 lam ^ (4 : ℕ) < C*Q^(-delta) := by
  rw [gapRadius4_source_formula lam hp,mul_div_assoc]
  have hratio : lam 2 / lam 3 < Q^(-delta) := (div_lt_iff₀ (hp 3)).mpr (by simpa only [mul_comm] using hgap)
  exact (mul_lt_mul_of_pos_left hratio (Finset.prod_pos (fun i _ => hp i))).trans_le
    (mul_le_mul_of_nonneg_right hprod (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _).le)

theorem fourthRoot4_power (C : ℝ) (hC : 0 < C) :
    (C^((1 : ℝ)/4))^(4 : ℕ) = C := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hC.le]
  norm_num

theorem gapRadius4_root_bound (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (C Q delta : ℝ) (hC : 0 < C) (hQ : 1 < Q)
    (hroot : gapRadius4 lam^(4 : ℕ) < C*Q^(-delta)) :
    gapRadius4 lam < C^((1 : ℝ)/4)*Q^(-delta/4) := by
  have hq : 0 < Q := zero_lt_one.trans hQ
  have hpow : (Q^(-delta/4))^(4 : ℕ) = Q^(-delta) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hq.le]
    congr 1
    ring
  apply lt_of_pow_lt_pow_left₀ 4
    (mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hq _)).le
  rw [mul_pow,fourthRoot4_power C hC,hpow]
  exact hroot

theorem deformation_decay_absorb4 (r C Q delta : ℝ) (hQ : 1 < Q)
    (hroot : r^(4 : ℕ) < C*Q^(-delta))
    (hcut : (16 : ℝ)^4*C < Q^(delta/6)) :
    16*r < Q^(-5*delta/24) := by
  have hq : 0 < Q := zero_lt_one.trans hQ
  have he : (Q^(-5*delta/24))^(4 : ℕ) = Q^(-5*delta/6) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hq.le]
    congr 1
    ring
  have hmul : Q^(delta/6)*Q^(-delta) = Q^(-5*delta/6) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  have hh : (16*r)^(4 : ℕ) < (Q^(-5*delta/24))^(4 : ℕ) := by
    rw [mul_pow,he]
    calc
      _ < (16 : ℝ)^4*(C*Q^(-delta)) := mul_lt_mul_of_pos_left hroot (by norm_num)
      _ = ((16 : ℝ)^4*C)*Q^(-delta) := by ring
      _ < Q^(delta/6)*Q^(-delta) :=
        mul_lt_mul_of_pos_right hcut (Real.rpow_pos_of_pos hq _)
      _ = _ := hmul
  exact lt_of_pow_lt_pow_left₀ 4 (Real.rpow_pos_of_pos hq _).le hh

theorem rescaled_small4 (Q delta x : ℝ) (hQ : 0 < Q)
    (hx : x < Q^(-5*delta/24)) : x < (Q^(5 : ℕ))^(-(delta/24)) := by
  have he : (Q^(5 : ℕ))^(-(delta/24)) = Q^(-5*delta/24) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hQ.le]
    congr 1
    ring
  rw [he]
  exact hx

theorem source_uniform_radius4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ C K T : ℝ, 0 < C ∧ 0 < K ∧ K = C^((1 : ℝ)/4) ∧ 1 < T ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ),
      (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i) = 0) → T < Q →
      sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 2 <
        sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 3*Q^(-delta) →
      let lam := sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3
      gapRadius4 lam^(4 : ℕ) < C*Q^(-delta) ∧
      gapRadius4 lam < K*Q^(-delta/4) ∧ 16*gapRadius4 lam < Q^(-5*delta/24) := by
  obtain ⟨_,C,_,hC,hbounds⟩ :=
    OriginalMinimaProduct4.source_original_uniform_minima_two_sided4 A2 A3 L h2 h3 hL
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 ((16 : ℝ)^4*C) (delta/3) (by positivity)
  refine ⟨C,C^((1 : ℝ)/4),T,hC,Real.rpow_pos_of_pos hC _,rfl,hT,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb hTQ hgap
  have hp := (sourceMinima4_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1
  have hroot := gapRadius4_quantitative _ hp C Q delta hQ (hbounds Q hQ c0 c2 c3 hc2 hc3 hb).2 hgap
  have hcut' : (16 : ℝ)^4*C < Q^(delta/6) := by
    convert hcut Q hTQ using 1 <;> congr 1 <;> ring
  exact ⟨hroot,gapRadius4_root_bound _ hp C Q delta hC hQ hroot,
    deformation_decay_absorb4 _ C Q delta hQ hroot hcut'⟩

def deformedWidths4 (Q : ℝ) (c0 : Fin 4 → ℝ) (d : Fin 4 → ℝ)
    (sigma : Equiv.Perm (Fin 4)) : Fin 4 → ℝ := fun i => Q^(c0 i)/d (sigma i)

def originalDeformedCoordinates4 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 4 → ℝ) (d : Fin 4 → ℝ)
    (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < d i) :
    (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  davenportCoordinates4 (originalCoordinates4 L hL Q hQ c0) d sigma hd

theorem originalDeformedCoordinates4_apply (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 4 → ℝ) (d : Fin 4 → ℝ)
    (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < d i) (x : Fin 4 → ℝ) (i : Fin 4) :
    originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd x i =
      d (sigma i)*(L *ᵥ x) i/Q^(c0 i) := by
  rw [originalDeformedCoordinates4,davenportCoordinates4_apply]
  change d (sigma i)*((L *ᵥ x) i/Q^(c0 i)) = _
  ring

theorem deformedWidths4_pos (Q : ℝ) (hQ : 0 < Q) (c0 : Fin 4 → ℝ)
    (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i) (sigma : Equiv.Perm (Fin 4)) :
    ∀ i, 0 < deformedWidths4 Q c0 d sigma i := fun i =>
  div_pos (Real.rpow_pos_of_pos hQ _) (hd _)

theorem deformedWidths4_balance (Q : ℝ) (hQ : 0 < Q) (c0 c2 c3 : Fin 4 → ℝ)
    (d : Fin 4 → ℝ) (hp : (∏ i, d i) = 1) (sigma : Equiv.Perm (Fin 4))
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0) :
    (∏ i, deformedWidths4 Q c0 d sigma i)*(∏ i, Q^(c2 i+c3 i)) = 1 := by
  simp only [deformedWidths4,Finset.prod_div_distrib,Equiv.prod_comp,hp,div_one]
  rw [← Real.rpow_sum_of_pos hQ,← Real.rpow_sum_of_pos hQ,← Real.rpow_add hQ]
  have he : (∑ i, c0 i)+(∑ i, (c2 i+c3 i)) = 0 := by
    simpa only [Finset.sum_add_distrib,add_assoc] using hb
  rw [he,Real.rpow_zero]

def originalDeformedMinima4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 4 → ℝ) (d : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4))
    (hd : ∀ i, 0 < d i) (j : Fin 4) : ℝ :=
  successiveRadius4 (sourceRealBasis4 A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))))
    (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd) j

theorem source_original_davenport4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 4 → ℝ) (u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3)
    (hu : LinearIndependent ℝ (fun i => integerReal (u i : Fin 4 → ℤ)))
    (hatt : ∀ i, coordinateGauge4 (originalCoordinates4 L hL Q hQ c0)
      (integerReal (u i : Fin 4 → ℤ)) = sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 i) :
    let lam := sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3
    let d := gapDeformation4 lam
    ∃ hd : ∀ i, 0 < d i, (∏ i, d i) = 1 ∧ Antitone d ∧ Monotone (fun i => d i*lam i) ∧
      ∃ sigma : Equiv.Perm (Fin 4),
      (∀ j, d j*lam j/16 ≤ originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j ∧
        originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j ≤ 16*(d j*lam j)) ∧
      MeasureTheory.volume.real (parallelepipedBody4
        (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)) =
          MeasureTheory.volume.real (parallelepipedBody4 (originalCoordinates4 L hL Q hQ c0)) ∧
      ∀ j : Fin 4, ∀ z : originalSourceGroup4 A2 A3 Q c2 c3,
        integerReal (z : Fin 4 → ℤ) ∉ minimaFlag4 (fun i => integerReal (u i : Fin 4 → ℤ)) j →
        d j*lam j/16 ≤ coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)
          (integerReal (z : Fin 4 → ℤ)) := by
  dsimp only
  let b := sourceRealBasis4 A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))
  let e := originalCoordinates4 L hL Q hQ c0
  let lam := sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3
  let d := gapDeformation4 lam
  obtain ⟨hp,hm⟩ := sourceMinima4_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  have hd : ∀ i, 0 < d i := gapDeformation4_pos lam hp
  have hprod : (∏ i, d i) = 1 := gapDeformation4_product lam hp
  have hanti : Antitone d := gapDeformation4_antitone lam hp hm
  have hscaled : Monotone (fun i => d i*lam i) := gapDeformation4_scaled lam hp hm
  have hrad (i : Fin 4) : lam i = successiveRadius4 b e i :=
    sourceMinima4_eq_radius A2 A3 L hL Q hQ c0 c2 c3 i
  have hmem (z : originalSourceGroup4 A2 A3 Q c2 c3) : integerReal (z : Fin 4 → ℤ) ∈ lattice4Span b := by
    rw [sourceRealBasis4_span]
    exact ⟨(z : Fin 4 → ℤ),z.property,rfl⟩
  have hatt' (i : Fin 4) : coordinateGauge4 e (integerReal (u i : Fin 4 → ℤ)) =
      successiveRadius4 b e i := (hatt i).trans (hrad i)
  have hscaled' : Monotone (fun i => d i*successiveRadius4 b e i) := by
    simpa only [← hrad] using hscaled
  obtain ⟨sigma,hbounds,hvol,hsep⟩ := davenport_lemma4 b e
    (fun i => integerReal (u i : Fin 4 → ℤ)) hu (fun i => hmem (u i)) hatt' d hd hprod hanti hscaled'
  refine ⟨hd,hprod,hanti,hscaled,sigma,?_,hvol,?_⟩
  · intro j
    change d j*lam j/16 ≤ successiveRadius4 b (davenportCoordinates4 e d sigma hd) j ∧
      successiveRadius4 b (davenportCoordinates4 e d sigma hd) j ≤ 16*(d j*lam j)
    rw [hrad]
    exact hbounds j
  · intro j z hout
    change d j*lam j/16 ≤ coordinateGauge4 (davenportCoordinates4 e d sigma hd) (integerReal (z : Fin 4 → ℤ))
    rw [hrad]
    exact hsep j _ (hmem z) hout

theorem integerReal_norm_lower4 (z : Fin 4 → ℤ) (hz : z ≠ 0) : 1 ≤ ‖integerReal z‖ := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hz
  have hi' : z i ≠ 0 := by simpa only [Pi.zero_apply] using hi
  have ha : (1 : ℝ) ≤ |(z i : ℝ)| := by exact_mod_cast Int.one_le_abs hi'
  exact ha.trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (integerReal z) i)

theorem original_unweighted_bound4 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 4 → ℝ) (hc : ∀ i, |c0 i| ≤ 1) (x : Fin 4 → ℝ) :
    ‖originalFormEquiv4 L hL x‖ ≤ coordinateGauge4 (originalCoordinates4 L hL Q hQ c0) x * Q := by
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  have hh := (originalCoordinates4_bounds L hL Q hQ c0 x _).mp le_rfl i
  have he : Q^(c0 i) ≤ Q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ.le (abs_le.mp (hc i)).2
  exact hh.trans (mul_le_mul_of_nonneg_left he (norm_nonneg _))

theorem source_first_lower4 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) :
    ∃ D : ℝ, 0 < D ∧ ∀ (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
      (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ), (∀ i, |c0 i| ≤ 1) →
      1/(D*Q) ≤ sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 0 := by
  let E := (originalFormEquiv4 L hL).toContinuousLinearEquiv
  let D := max 1 ‖E.symm.toContinuousLinearMap‖
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨D,hD,?_⟩
  intro A2 A3 Q hQ c0 c2 c3 hc
  obtain ⟨u,hu,_,_,hatt,_⟩ := exists_sourceMinima4_attaining A2 A3 L hL Q hQ c0 c2 c3
  have hz : (u 0 : Fin 4 → ℤ) ≠ 0 := by
    intro hz
    apply hu.ne_zero 0
    rw [hz,map_zero]
  have hnorm := integerReal_norm_lower4 (u 0) hz
  have hinv : ‖integerReal (u 0 : Fin 4 → ℤ)‖ ≤ D*‖originalFormEquiv4 L hL
      (integerReal (u 0 : Fin 4 → ℤ))‖ := by
    have hi := E.symm.toContinuousLinearMap.le_opNorm (E (integerReal (u 0 : Fin 4 → ℤ)))
    simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at hi
    exact hi.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hg := original_unweighted_bound4 L hL Q hQ c0 hc (integerReal (u 0 : Fin 4 → ℤ))
  rw [hatt] at hg
  apply (div_le_iff₀ (mul_pos hD (zero_lt_one.trans hQ))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hg hD.le,hnorm.trans hinv]

theorem last_upper_from_first4 (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) (C D Q : ℝ) (hD : 0 < D) (hQ : 0 < Q)
    (hprod : (∏ i, lam i) ≤ C) (hfirst : 1/(D*Q) ≤ lam 0) :
    lam 3 ≤ (C*D^3)*Q^3 := by
  have hlo : (lam 0)^3*lam 3 ≤ ∏ i, lam i := by
    have hi : (∏ i : Fin 4, if i = 3 then lam 3 else lam 0) ≤ ∏ i, lam i :=
      Finset.prod_le_prod (fun i _ => by split_ifs; exact (hp 3).le; exact (hp 0).le)
        (fun i _ => by split_ifs with h; subst i; exact le_rfl; exact hm (Fin.zero_le i))
    have he : (∏ i : Fin 4, if i = 3 then lam 3 else lam 0) = (lam 0)^3*lam 3 := by
      rw [Fin.prod_univ_four]
      change lam 0*lam 0*lam 0*lam 3 = (lam 0)^3*lam 3
      ring
    rw [he] at hi
    exact hi
  have hf : 1 ≤ D*Q*lam 0 := by
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos hD hQ)).mp hfirst
  have hf3 : 1 ≤ (D*Q*lam 0)^3 := one_le_pow₀ hf
  calc
    lam 3 ≤ (D*Q*lam 0)^3*lam 3 := le_mul_of_one_le_left (hp 3).le hf3
    _ = (D*Q)^3*((lam 0)^3*lam 3) := by ring
    _ ≤ (D*Q)^3*C := mul_le_mul_of_nonneg_left (hlo.trans hprod) (by positivity)
    _ = _ := by ring

theorem source_uniform_basic_bounds4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ c C D K : ℝ, 0 < c ∧ 0 < C ∧ 0 < D ∧ 0 < K ∧ K = C*D^3 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ),
      (∀ i, |c0 i| ≤ 1) → (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) →
      (∑ i, (c0 i+c2 i+c3 i)) = 0 →
      let lam := sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3
      c ≤ (∏ i, lam i) ∧ (∏ i, lam i) ≤ C ∧ 1/(D*Q) ≤ lam 0 ∧ lam 3 ≤ K*Q^3 := by
  obtain ⟨c,C,hc,hC,hbounds⟩ :=
    OriginalMinimaProduct4.source_original_uniform_minima_two_sided4 A2 A3 L h2 h3 hL
  obtain ⟨D,hD,hfirst⟩ := source_first_lower4 L hL
  refine ⟨c,C,D,C*D^3,hc,hC,hD,by positivity,rfl,?_⟩
  intro Q hQ c0 c2 c3 hc0 hc2 hc3 hb
  obtain ⟨hp,hm⟩ := sourceMinima4_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  have hf := hfirst A2 A3 Q hQ c0 c2 c3 hc0
  have hbd := hbounds Q hQ c0 c2 c3 hc2 hc3 hb
  exact ⟨hbd.1,hbd.2,hf,last_upper_from_first4 _ hp hm C D Q hD (zero_lt_one.trans hQ) hbd.2 hf⟩

theorem gapRadius4_le_root (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (C : ℝ) (hC : 0 < C) (hprod : (∏ i, lam i) ≤ C) : gapRadius4 lam ≤ C^((1 : ℝ)/4) := by
  have hb : gapRadius4 lam^(4 : ℕ) ≤ C := by
    rw [gapRadius4_source_formula lam hp,mul_div_assoc]
    have hr : lam 2/lam 3 ≤ 1 := (div_le_one (hp 3)).mpr (hm (by decide))
    exact (mul_le_mul_of_nonneg_left hr (Finset.prod_pos (fun i _ => hp i)).le).trans
      (by simpa only [mul_one] using hprod)
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (Real.rpow_pos_of_pos hC _).le
  rw [fourthRoot4_power C hC]
  exact hb

theorem gapRadius4_lower_scaled (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (c : ℝ) (hc : 0 < c) (hprod : c ≤ ∏ i, lam i) :
    c^((1 : ℝ)/4)*lam 2 ≤ gapRadius4 lam*lam 3 := by
  have hmul : c*(lam 2)^4 ≤ (∏ i, lam i)*lam 2*(lam 3)^3 := by
    calc
      _ ≤ (∏ i, lam i)*(lam 2)^4 := mul_le_mul_of_nonneg_right hprod (by positivity)
      _ = ((∏ i, lam i)*lam 2)*(lam 2)^3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hp 2).le (hm (by decide : (2 : Fin 4) ≤ 3)) 3)
        (mul_pos (Finset.prod_pos (fun j _ => hp j)) (hp 2)).le
  have he : (gapRadius4 lam*lam 3)^(4 : ℕ) = (∏ i, lam i)*lam 2*(lam 3)^3 := by
    rw [mul_pow,gapRadius4_source_formula lam hp]
    field_simp [(hp 3).ne']
    ring
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0)
    (mul_pos (gapRadius4_pos lam hp) (hp 3)).le
  rw [mul_pow,fourthRoot4_power c hc,he]
  exact hmul

theorem gapDeformation4_polynomial_bounds (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) (c C D K Q : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hD : 0 < D) (hQ : 0 < Q) (hprodlo : c ≤ ∏ i, lam i) (hprodhi : (∏ i, lam i) ≤ C)
    (hfirst : 1/(D*Q) ≤ lam 0) (hlast : lam 3 ≤ K*Q^3) :
    ∀ i, gapDeformation4 lam i ≤ (D*C^((1 : ℝ)/4))*Q ∧
      (gapDeformation4 lam i)⁻¹ ≤ (K/c^((1 : ℝ)/4))*Q^3 := by
  have hr := gapRadius4_le_root lam hp hm C hC hprodhi
  have hlo := gapRadius4_lower_scaled lam hp hm c hc hprodlo
  have hcp : 0 < c^((1 : ℝ)/4) := Real.rpow_pos_of_pos hc _
  have hfirst' : 1 ≤ D*Q*lam 0 := by
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos hD hQ)).mp hfirst
  intro i
  constructor
  · apply (div_le_iff₀ (hp (min i 2))).mpr
    have hfi : 1 ≤ D*Q*lam (min i 2) :=
      hfirst'.trans (mul_le_mul_of_nonneg_left (hm (Fin.zero_le _)) (mul_pos hD hQ).le)
    have hmul := mul_le_mul_of_nonneg_left hfi (Real.rpow_pos_of_pos hC ((1 : ℝ)/4)).le
    nlinarith
  · change (gapRadius4 lam/lam (min i 2))⁻¹ ≤ _
    rw [inv_div]
    have hmini : lam (min i 2) ≤ lam 2 := hm (min_le_right _ _)
    have hdiv : lam 2/gapRadius4 lam ≤ lam 3/c^((1 : ℝ)/4) :=
      (div_le_div_iff₀ (gapRadius4_pos lam hp) hcp).mpr (by nlinarith [hlo])
    calc
      _ ≤ lam 2/gapRadius4 lam := div_le_div_of_nonneg_right hmini (gapRadius4_pos lam hp).le
      _ ≤ lam 3/c^((1 : ℝ)/4) := hdiv
      _ ≤ (K*Q^3)/c^((1 : ℝ)/4) := div_le_div_of_nonneg_right hlast hcp.le
      _ = _ := by ring

theorem deformedWidths4_polynomial_bounds (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) (c C D K Q : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hD : 0 < D) (hK : 0 < K) (hQ : 1 < Q) (c0 : Fin 4 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hprodlo : c ≤ ∏ i, lam i) (hprodhi : (∏ i, lam i) ≤ C)
    (hfirst : 1/(D*Q) ≤ lam 0) (hlast : lam 3 ≤ K*Q^3)
    (sigma : Equiv.Perm (Fin 4)) :
    ∀ i, deformedWidths4 Q c0 (gapDeformation4 lam) sigma i ≤
        max (D*C^((1 : ℝ)/4)) (K/c^((1 : ℝ)/4))*Q^4 ∧
      (deformedWidths4 Q c0 (gapDeformation4 lam) sigma i)⁻¹ ≤
        max (D*C^((1 : ℝ)/4)) (K/c^((1 : ℝ)/4))*Q^4 := by
  have hq : 0 < Q := zero_lt_one.trans hQ
  have hb := gapDeformation4_polynomial_bounds lam hp hm c C D K Q hc hC hD hq
    hprodlo hprodhi hfirst hlast
  have hd := gapDeformation4_pos lam hp
  let B := max (D*C^((1 : ℝ)/4)) (K/c^((1 : ℝ)/4))
  have hB : 0 < B := (mul_pos hD (Real.rpow_pos_of_pos hC _)).trans_le (le_max_left _ _)
  intro i
  have hw : 0 < Q^(c0 i) := Real.rpow_pos_of_pos hq _
  have ha : Q^(c0 i) ≤ Q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ.le (abs_le.mp (hc0 i)).2
  have hai : (Q^(c0 i))⁻¹ ≤ Q := by
    rw [← Real.rpow_neg hq.le]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ.le
      (show -c0 i ≤ 1 by linarith [(abs_le.mp (hc0 i)).1])
  have hdi : (gapDeformation4 lam (sigma i))⁻¹ ≤ B*Q^3 :=
    (hb (sigma i)).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hdhi : gapDeformation4 lam (sigma i) ≤ B*Q^3 := by
    have hq3 : Q ≤ Q^3 := le_self_pow₀ hQ.le (by decide)
    exact ((hb (sigma i)).1.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hq.le)).trans
        (mul_le_mul_of_nonneg_left hq3 hB.le)
  constructor
  · change Q^(c0 i)/gapDeformation4 lam (sigma i) ≤ _
    rw [div_eq_mul_inv]
    have h := mul_le_mul ha hdi (inv_nonneg.mpr (hd _).le) hq.le
    convert h using 1 <;> ring
  · change (Q^(c0 i)/gapDeformation4 lam (sigma i))⁻¹ ≤ _
    rw [inv_div,div_eq_mul_inv]
    have h := mul_le_mul hdhi hai (inv_nonneg.mpr hw.le) (mul_pos hB (pow_pos hq 3)).le
    convert h using 1 <;> ring

theorem originalDeformedBody4_mem (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 4 → ℝ) (d : Fin 4 → ℝ)
    (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < d i) (x : Fin 4 → ℝ) :
    x ∈ parallelepipedBody4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd) ↔
      ∀ i, |(L *ᵥ x) i| ≤ deformedWidths4 Q c0 d sigma i := by
  rw [mem_parallelepipedBody4_iff]
  change ‖originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd x‖ ≤ 1 ↔ _
  rw [pi_norm_le_iff_of_nonempty]
  apply forall_congr'
  intro i
  rw [Real.norm_eq_abs,originalDeformedCoordinates4_apply,abs_div,abs_mul,
    abs_of_pos (hd _),abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _)]
  change d (sigma i)*|(L *ᵥ x) i|/Q^(c0 i) ≤ 1 ↔ |(L *ᵥ x) i| ≤ Q^(c0 i)/d (sigma i)
  rw [div_le_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _),
    le_div_iff₀ (hd _),one_mul]
  constructor <;> intro h <;> simpa only [mul_comm] using h

theorem originalBody_gauge4 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 4 → ℝ) :
    parallelepipedBody4 (originalCoordinates4 L hL Q hQ c0) = originalBody4 L Q c0 := by
  ext x
  rw [mem_parallelepipedBody4_iff,originalBody4_mem_iff L hL Q hQ c0 x]
  rfl

theorem rescaled_power4 (Q c : ℝ) (hQ : 0 < Q) : (Q^(5 : ℕ))^(c/5) = Q^c := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hQ.le]
  congr 1
  ring

theorem rescaled_threshold4 (p : ℕ) (Q c : ℝ) :
    JSP000334.qThreshold p (Q^(5 : ℕ)) (c/5) = JSP000334.qThreshold p Q c := by
  unfold JSP000334.qThreshold
  rw [Real.log_pow]
  ring

theorem source_finite_cutoff4 (Q : ℝ) (hQ : 1 < Q) (c : Fin 4 → ℝ)
    (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 0) : ∀ i, Q^(-c i) < Q^(5 : ℕ) := by
  intro i
  have hb : Q^(-c i) ≤ Q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ.le
      (show -c i ≤ 1 by linarith [(hc i).1])
  exact hb.trans_lt (by simpa only [pow_one] using pow_lt_pow_right₀ hQ (by decide : (1 : ℕ) < 5))

def deformationReady4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 4 → ℝ) (delta : ℝ)
    (u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3) : Prop :=
  let lam := sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3
  let d := gapDeformation4 lam
  0 < gapRadius4 lam ∧ gapRadius4 lam^4 = (∏ i, lam i)*lam 2/lam 3 ∧
  ∃ hd : ∀ i, 0 < d i, (∏ i, d i) = 1 ∧ Antitone d ∧ Monotone (fun i => d i*lam i) ∧
  ∃ sigma : Equiv.Perm (Fin 4),
    (∀ i, 0 < deformedWidths4 Q c0 d sigma i) ∧
    (∏ i, deformedWidths4 Q c0 d sigma i)*(∏ i, Q^(c2 i+c3 i)) = 1 ∧
    (∀ j, d j*lam j/16 ≤ originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j ∧
      originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j ≤ 16*(d j*lam j)) ∧
    MeasureTheory.volume.real (parallelepipedBody4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)) =
      MeasureTheory.volume.real (originalBody4 L Q c0) ∧
    (∀ j : Fin 4, ∀ z : originalSourceGroup4 A2 A3 Q c2 c3,
      integerReal (z : Fin 4 → ℤ) ∉ minimaFlag4 (fun i => integerReal (u i : Fin 4 → ℤ)) j →
      d j*lam j/16 ≤ coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)
        (integerReal (z : Fin 4 → ℤ))) ∧
    originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd 2 ≤ 16*gapRadius4 lam ∧
    originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd 2 < Q^(-5*delta/24) ∧
    originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd 2 < (Q^(5 : ℕ))^(-(delta/24)) ∧
    (∀ i, deformedWidths4 Q c0 d sigma i < Q^(5 : ℕ) ∧
      (deformedWidths4 Q c0 d sigma i)⁻¹ < Q^(5 : ℕ) ∧
      Q^(-c2 i) < Q^(5 : ℕ) ∧ Q^(-c3 i) < Q^(5 : ℕ)) ∧
    (∀ x, x ∈ parallelepipedBody4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd) ↔
      ∀ i, |(L *ᵥ x) i| ≤ deformedWidths4 Q c0 d sigma i) ∧
    (∀ i, (Q^(5 : ℕ))^(c2 i/5) = Q^(c2 i) ∧ (Q^(5 : ℕ))^(c3 i/5) = Q^(c3 i)) ∧
    (∀ (p : ℕ) i, JSP000334.qThreshold p (Q^(5 : ℕ)) (c2 i/5) = JSP000334.qThreshold p Q (c2 i) ∧
      JSP000334.qThreshold p (Q^(5 : ℕ)) (c3 i/5) = JSP000334.qThreshold p Q (c3 i))

theorem source_uniform_deformation4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ),
      (∀ i, |c0 i| ≤ 1) → (∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) → (∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) →
      (∑ i, (c0 i+c2 i+c3 i)) = 0 → T < Q →
      ∀ u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun i => integerReal (u i : Fin 4 → ℤ)) →
      (∀ i, coordinateGauge4 (originalCoordinates4 L hL Q hQ c0)
        (integerReal (u i : Fin 4 → ℤ)) = sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 i) →
      sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 2 <
        sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 3*Q^(-delta) →
      deformationReady4 A2 A3 L hL Q hQ c0 c2 c3 delta u := by
  obtain ⟨c,C,D,K,hc,hC,hD,hK,_,hbasic⟩ := source_uniform_basic_bounds4 A2 A3 L h2 h3 hL
  let B := max (D*C^((1 : ℝ)/4)) (K/c^((1 : ℝ)/4))
  obtain ⟨T0,hT0,hcut⟩ := compound_gap_cutoff42 ((16 : ℝ)^4*C) (delta/3) (by positivity)
  let T := max T0 (B+1)
  refine ⟨T,hT0.trans_le (le_max_left _ _),?_⟩
  intro Q hQ c0 c2 c3 hc0 hc2 hc3 hb hTQ u hu hatt hgap
  let lam := sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3
  obtain ⟨hp,hm⟩ := sourceMinima4_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  obtain ⟨hlo,hhi,hfirst,hlast⟩ := hbasic Q hQ c0 c2 c3 hc0 (fun i => (hc2 i).2) (fun i => (hc3 i).2) hb
  have hroot := gapRadius4_quantitative lam hp C Q delta hQ hhi hgap
  have hcuteq : (16 : ℝ)^4*C < Q^(delta/6) := by
    convert hcut Q ((le_max_left _ _).trans_lt hTQ) using 1 <;> congr 1 <;> ring
  have hrsmall := deformation_decay_absorb4 _ C Q delta hQ hroot hcuteq
  obtain ⟨hdp,hprod,hanti,hscaled,sigma,hbounds,hvol,hsep⟩ :=
    source_original_davenport4 A2 A3 L hL Q hQ c0 c2 c3 u hu hatt
  have hu2 : originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3
      (gapDeformation4 lam) sigma hdp 2 ≤ 16*gapRadius4 lam := by
    have h := (hbounds 2).2
    rw [gapDeformation4_first lam hp 2 le_rfl] at h
    exact h
  have hsmall := hu2.trans_lt hrsmall
  have hwidth := deformedWidths4_polynomial_bounds lam hp hm c C D K Q hc hC hD hK hQ
    c0 hc0 hlo hhi hfirst hlast sigma
  have hBQ : B < Q := by
    have hBT : B+1 ≤ T := le_max_right _ _
    linarith
  have hlarge : B*Q^4 < Q^(5 : ℕ) := by
    calc
      _ < Q*Q^4 := mul_lt_mul_of_pos_right hBQ (pow_pos (zero_lt_one.trans hQ) 4)
      _ = _ := by ring
  refine ⟨gapRadius4_pos lam hp,gapRadius4_source_formula lam hp,hdp,hprod,hanti,hscaled,sigma,
    deformedWidths4_pos Q (zero_lt_one.trans hQ) c0 _ hdp sigma,
    deformedWidths4_balance Q (zero_lt_one.trans hQ) c0 c2 c3 _ hprod sigma hb,
    hbounds,hvol.trans (congrArg (fun S => MeasureTheory.volume.real S) (originalBody_gauge4 L hL Q hQ c0)),hsep,hu2,hsmall,rescaled_small4 Q delta _ (zero_lt_one.trans hQ) hsmall,?_,
    originalDeformedBody4_mem L hL Q hQ c0 _ sigma hdp,?_,?_⟩
  · intro i
    exact ⟨(hwidth i).1.trans_lt hlarge,(hwidth i).2.trans_lt hlarge,
      source_finite_cutoff4 Q hQ c2 hc2 i,source_finite_cutoff4 Q hQ c3 hc3 i⟩
  · intro i
    exact ⟨rescaled_power4 Q (c2 i) (zero_lt_one.trans hQ),rescaled_power4 Q (c3 i) (zero_lt_one.trans hQ)⟩
  · intro p i
    exact ⟨rescaled_threshold4 p Q (c2 i),rescaled_threshold4 p Q (c3 i)⟩

theorem rescaled_group4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c2 c3 : Fin 4 → ℝ) :
    originalSourceGroup4 A2 A3 Q c2 c3 = originalSourceGroup4 A2 A3 (Q^(5 : ℕ))
      (fun i => c2 i/5) (fun i => c3 i/5) := by
  simp only [originalSourceGroup4,rescaled_threshold4]

theorem rescaled_finite_weights4 (c : Fin 4 → ℝ) (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 0) :
    ∀ i, -1 ≤ c i/5 ∧ c i/5 ≤ 0 := by
  intro i
  constructor <;> linarith [(hc i).1,(hc i).2]

theorem fifth_image_unbounded4 (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q) :
    ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' V) := by
  rintro ⟨B,hB⟩
  obtain ⟨q,hq,hBq⟩ := not_bddAbove_iff.mp hV B
  have hpow : q ≤ q^(5 : ℕ) := le_self_pow₀ (hQV q hq).le (by decide)
  exact (not_lt_of_ge (hpow.trans (hB ⟨q,hq,rfl⟩))) hBq

theorem source_normalized_unbounded_deformation4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (_hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c0 c2 c3 : Fin 4 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ V),
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQV q hq) c0 c2 c3 2 <
        sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQV q hq) c0 c2 c3 3*q^(-delta)) :
    ∃ T : ℝ, 1 < T ∧
      ∃ u : (q : V) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3,
      ¬ BddAbove V ∧ ¬ BddAbove {q : ℝ | q ∈ V ∧ T < q} ∧
      ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' {q : ℝ | q ∈ V ∧ T < q}) ∧
      (∀ q : V, LinearIndependent ℝ (fun i => integerReal (u q i : Fin 4 → ℤ)) ∧
        ∀ i, coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) q.val
          (hQV q.val q.property) c0) (integerReal (u q i : Fin 4 → ℤ)) =
          sourceMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQV q.val q.property) c0 c2 c3 i) ∧
      ∀ q : V, T < q.val →
        (1 < q.val^(5 : ℕ) ∧ 0 < delta/24) ∧
        originalSourceGroup4 A2 A3 q.val c2 c3 =
          originalSourceGroup4 A2 A3 (q.val^(5 : ℕ)) (fun i => c2 i/5) (fun i => c3 i/5) ∧
        deformationReady4 A2 A3 L (sourceUnit42 L hL) q.val (hQV q.val q.property) c0 c2 c3 delta (u q) := by
  obtain ⟨T,hT,hready⟩ := source_uniform_deformation4 A2 A3 L
    (sourceUnit42 A2 h2) (sourceUnit42 A3 h3) (sourceUnit42 L hL) delta hd
  obtain ⟨u,hVsame,hframes⟩ := OriginalLastDual4.source_original_last_dual_frame4
    A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta V hV hQV hgap
  refine ⟨T,hT,u,hVsame,JSP000334.sourceDual_unbounded_tail3 V hV T,
    fifth_image_unbounded4 _ (JSP000334.sourceDual_unbounded_tail3 V hV T) (fun q hq => hQV q hq.1),?_,?_⟩
  · intro q
    obtain ⟨hu,_,hatt,_,_,_,_,_,_⟩ := hframes q
    exact ⟨hu,hatt⟩
  · intro q hTQ
    obtain ⟨hu,_,hatt,_,_,_,_,_,_⟩ := hframes q
    exact ⟨⟨one_lt_pow₀ (hQV q.val q.property) (by decide),by positivity⟩,
      rescaled_group4 A2 A3 q.val c2 c3,
      hready q.val (hQV q.val q.property) c0 c2 c3 hc0 hc2 hc3 hb hTQ (u q) hu hatt
        (hgap q.val q.property)⟩

end
end CompoundFeasibility.OriginalDeformation4
