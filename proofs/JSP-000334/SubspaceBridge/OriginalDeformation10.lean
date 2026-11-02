import SubspaceBridge.Davenport10
open scoped BigOperators Matrix
namespace CompoundFeasibility.OriginalDeformation10
noncomputable section

def gapRadius10 (lam : Fin 10 → ℝ) : ℝ :=
  (∏ i : Fin 10, lam (min i 8)) ^ ((1 : ℝ) / 10)

def gapDeformation10 (lam : Fin 10 → ℝ) (i : Fin 10) : ℝ :=
  gapRadius10 lam / lam (min i 8)

theorem gapRadius10_pos (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i) : 0 < gapRadius10 lam :=
  Real.rpow_pos_of_pos (Finset.prod_pos (fun i _ => hp _)) _

theorem gapRadius10_power (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i) :
    gapRadius10 lam ^ (10 : ℕ) = ∏ i : Fin 10, lam (min i 8) := by
  unfold gapRadius10
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Finset.prod_pos (fun i _ => hp _)).le]
  norm_num

theorem gapRadius10_source_formula (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i) :
    gapRadius10 lam ^ (10 : ℕ) = (∏ i, lam i) * lam 8 / lam 9 := by
  rw [gapRadius10_power lam hp]
  simp only [Fin.prod_univ_succ]
  change lam 0 * (lam 1 * (lam 2 * (lam 3 * (lam 4 * (lam 5 * (lam 6 * (lam 7 * (lam 8 * (lam 8 * 1))))))))) =
    (lam 0 * (lam 1 * (lam 2 * (lam 3 * (lam 4 * (lam 5 * (lam 6 * (lam 7 * (lam 8 * (lam 9 * 1)))))))))) * lam 8 / lam 9
  field_simp [(hp 9).ne']
  <;> ring

theorem gapDeformation10_pos (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i) :
    ∀ i, 0 < gapDeformation10 lam i := fun i => div_pos (gapRadius10_pos lam hp) (hp _)

theorem gapDeformation10_product (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i) :
    (∏ i, gapDeformation10 lam i) = 1 := by
  change (∏ i, gapRadius10 lam / lam (min i 8)) = 1
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [gapRadius10_power lam hp]
  exact div_self (Finset.prod_pos (fun i _ => hp _)).ne'

theorem gapDeformation10_antitone (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) : Antitone (gapDeformation10 lam) := by
  intro i j hij
  exact div_le_div_of_nonneg_left (gapRadius10_pos lam hp).le (hp _)
    (hm (min_le_min hij le_rfl))

theorem gapDeformation10_first (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i)
    (i : Fin 10) (hi : i ≤ 8) : gapDeformation10 lam i * lam i = gapRadius10 lam := by
  unfold gapDeformation10
  rw [min_eq_left hi]
  exact div_mul_cancel₀ _ (hp i).ne'

theorem gapDeformation10_last (lam : Fin 10 → ℝ) :
    gapDeformation10 lam 9 * lam 9 = gapRadius10 lam * lam 9 / lam 8 := by
  change (gapRadius10 lam / lam 8) * lam 9 = _
  ring

theorem gapDeformation10_scaled (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) : Monotone (fun i => gapDeformation10 lam i * lam i) := by
  have hlast : gapRadius10 lam ≤ gapDeformation10 lam 9 * lam 9 := by
    calc
      _ = (gapRadius10 lam / lam 8) * lam 8 := (div_mul_cancel₀ _ (hp 8).ne').symm
      _ ≤ (gapRadius10 lam / lam 8) * lam 9 :=
        mul_le_mul_of_nonneg_left (hm (by decide : (8 : Fin 10) ≤ 9))
          (div_pos (gapRadius10_pos lam hp) (hp 8)).le
      _ = _ := rfl
  intro i j hij
  change gapDeformation10 lam i * lam i ≤ gapDeformation10 lam j * lam j
  by_cases hj : j ≤ 8
  · rw [gapDeformation10_first lam hp i (hij.trans hj),gapDeformation10_first lam hp j hj]
  · have hj3 : j = 9 := by omega
    subst j
    by_cases hi : i ≤ 8
    · rw [gapDeformation10_first lam hp i hi]
      exact hlast
    · have hi3 : i = 9 := by omega
      subst i
      exact le_rfl

theorem gapRadius10_quantitative (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i)
    (C Q delta : ℝ) (hQ : 1 < Q) (hprod : (∏ i, lam i) ≤ C)
    (hgap : lam 8 < lam 9 * Q^(-delta)) :
    gapRadius10 lam ^ (10 : ℕ) < C*Q^(-delta) := by
  rw [gapRadius10_source_formula lam hp,mul_div_assoc]
  have hratio : lam 8 / lam 9 < Q^(-delta) := (div_lt_iff₀ (hp 9)).mpr (by simpa only [mul_comm] using hgap)
  exact (mul_lt_mul_of_pos_left hratio (Finset.prod_pos (fun i _ => hp i))).trans_le
    (mul_le_mul_of_nonneg_right hprod (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _).le)

theorem fourthRoot10_power (C : ℝ) (hC : 0 < C) :
    (C^((1 : ℝ)/10))^(10 : ℕ) = C := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hC.le]
  norm_num

theorem gapRadius10_root_bound (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i)
    (C Q delta : ℝ) (hC : 0 < C) (hQ : 1 < Q)
    (hroot : gapRadius10 lam^(10 : ℕ) < C*Q^(-delta)) :
    gapRadius10 lam < C^((1 : ℝ)/10)*Q^(-delta/10) := by
  have hq : 0 < Q := zero_lt_one.trans hQ
  have hpow : (Q^(-delta/10))^(10 : ℕ) = Q^(-delta) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hq.le]
    congr 1
    ring
  apply lt_of_pow_lt_pow_left₀ 10
    (mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hq _)).le
  rw [mul_pow,fourthRoot10_power C hC,hpow]
  exact hroot

def deformedWidths10 (Q : ℝ) (c0 : Fin 10 → ℝ) (d : Fin 10 → ℝ)
    (sigma : Equiv.Perm (Fin 10)) : Fin 10 → ℝ := fun i => Q^(c0 i)/d (sigma i)

def originalDeformedCoordinates10 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 10 → ℝ) (d : Fin 10 → ℝ)
    (sigma : Equiv.Perm (Fin 10)) (hd : ∀ i, 0 < d i) :
    (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ) :=
  davenportCoordinates10 (originalCoordinates10 L hL Q hQ c0) d sigma hd

theorem originalDeformedCoordinates10_apply (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 10 → ℝ) (d : Fin 10 → ℝ)
    (sigma : Equiv.Perm (Fin 10)) (hd : ∀ i, 0 < d i) (x : Fin 10 → ℝ) (i : Fin 10) :
    originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd x i =
      d (sigma i)*(L *ᵥ x) i/Q^(c0 i) := by
  rw [originalDeformedCoordinates10,davenportCoordinates10_apply]
  change d (sigma i)*((L *ᵥ x) i/Q^(c0 i)) = _
  ring

theorem deformedWidths10_pos (Q : ℝ) (hQ : 0 < Q) (c0 : Fin 10 → ℝ)
    (d : Fin 10 → ℝ) (hd : ∀ i, 0 < d i) (sigma : Equiv.Perm (Fin 10)) :
    ∀ i, 0 < deformedWidths10 Q c0 d sigma i := fun i =>
  div_pos (Real.rpow_pos_of_pos hQ _) (hd _)

theorem deformedWidths10_balance (Q : ℝ) (hQ : 0 < Q) (c0 c2 c3 : Fin 10 → ℝ)
    (d : Fin 10 → ℝ) (hp : (∏ i, d i) = 1) (sigma : Equiv.Perm (Fin 10))
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0) :
    (∏ i, deformedWidths10 Q c0 d sigma i)*(∏ i, Q^(c2 i+c3 i)) = 1 := by
  simp only [deformedWidths10,Finset.prod_div_distrib,Equiv.prod_comp,hp,div_one]
  rw [← Real.rpow_sum_of_pos hQ,← Real.rpow_sum_of_pos hQ,← Real.rpow_add hQ]
  have he : (∑ i, c0 i)+(∑ i, (c2 i+c3 i)) = 0 := by
    simpa only [Finset.sum_add_distrib,add_assoc] using hb
  rw [he,Real.rpow_zero]

def originalDeformedMinima10 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 10 → ℝ) (d : Fin 10 → ℝ) (sigma : Equiv.Perm (Fin 10))
    (hd : ∀ i, 0 < d i) (j : Fin 10) : ℝ :=
  successiveRadius10 (sourceRealBasis10 A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))))
    (originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd) j

theorem source_original_davenport10 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 10 → ℝ) (u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3)
    (hu : LinearIndependent ℝ (fun i => integerReal (u i : Fin 10 → ℤ)))
    (hatt : ∀ i, coordinateGauge10 (originalCoordinates10 L hL Q hQ c0)
      (integerReal (u i : Fin 10 → ℤ)) = sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 i) :
    let lam := sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3
    let d := gapDeformation10 lam
    ∃ hd : ∀ i, 0 < d i, (∏ i, d i) = 1 ∧ Antitone d ∧ Monotone (fun i => d i*lam i) ∧
      ∃ sigma : Equiv.Perm (Fin 10),
      (∀ j, d j*lam j/1024 ≤ originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j ∧
        originalDeformedMinima10 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j ≤ 1024*(d j*lam j)) ∧
      MeasureTheory.volume.real (parallelepipedBody10
        (originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd)) =
          MeasureTheory.volume.real (parallelepipedBody10 (originalCoordinates10 L hL Q hQ c0)) ∧
      ∀ j : Fin 10, ∀ z : originalSourceGroup10 A2 A3 Q c2 c3,
        integerReal (z : Fin 10 → ℤ) ∉ minimaFlag10 (fun i => integerReal (u i : Fin 10 → ℤ)) j →
        d j*lam j/1024 ≤ coordinateGauge10 (originalDeformedCoordinates10 L hL Q hQ c0 d sigma hd)
          (integerReal (z : Fin 10 → ℤ)) := by
  dsimp only
  let b := sourceRealBasis10 A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))
  let e := originalCoordinates10 L hL Q hQ c0
  let lam := sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3
  let d := gapDeformation10 lam
  obtain ⟨hp,hm⟩ := sourceMinima10_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  have hd : ∀ i, 0 < d i := gapDeformation10_pos lam hp
  have hprod : (∏ i, d i) = 1 := gapDeformation10_product lam hp
  have hanti : Antitone d := gapDeformation10_antitone lam hp hm
  have hscaled : Monotone (fun i => d i*lam i) := gapDeformation10_scaled lam hp hm
  have hrad (i : Fin 10) : lam i = successiveRadius10 b e i :=
    sourceMinima10_eq_radius A2 A3 L hL Q hQ c0 c2 c3 i
  have hmem (z : originalSourceGroup10 A2 A3 Q c2 c3) : integerReal (z : Fin 10 → ℤ) ∈ lattice10Span b := by
    rw [sourceRealBasis10_span]
    exact ⟨(z : Fin 10 → ℤ),z.property,rfl⟩
  have hatt' (i : Fin 10) : coordinateGauge10 e (integerReal (u i : Fin 10 → ℤ)) =
      successiveRadius10 b e i := (hatt i).trans (hrad i)
  have hscaled' : Monotone (fun i => d i*successiveRadius10 b e i) := by
    simpa only [← hrad] using hscaled
  obtain ⟨sigma,hbounds,hvol,hsep⟩ := davenport_lemma10 b e
    (fun i => integerReal (u i : Fin 10 → ℤ)) hu (fun i => hmem (u i)) hatt' d hd hprod hanti hscaled'
  refine ⟨hd,hprod,hanti,hscaled,sigma,?_,hvol,?_⟩
  · intro j
    change d j*lam j/1024 ≤ successiveRadius10 b (davenportCoordinates10 e d sigma hd) j ∧
      successiveRadius10 b (davenportCoordinates10 e d sigma hd) j ≤ 1024*(d j*lam j)
    rw [hrad]
    exact hbounds j
  · intro j z hout
    change d j*lam j/1024 ≤ coordinateGauge10 (davenportCoordinates10 e d sigma hd) (integerReal (z : Fin 10 → ℤ))
    rw [hrad]
    exact hsep j _ (hmem z) hout


end
end CompoundFeasibility.OriginalDeformation10
