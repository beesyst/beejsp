import SubspaceBridge.SourceDeformation10
open scoped BigOperators
namespace CompoundFeasibility.SourceAbsoluteGap10
noncomputable section

theorem absolute_ratio10 (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) (c Q delta : ℝ) (hc : 0 < c) (hQ : 1 < Q)
    (hprod : c ≤ ∏ i, lam i) (hsmall : lam 8 < Q^(-delta)) :
    lam 8 / lam 9 < Q^(-10*delta)/c := by
  have hnine : (∏ j : Fin 9, lam j.castSucc) ≤ (lam 8)^9 := by
    calc
      _ ≤ ∏ _j : Fin 9, lam 8 := Finset.prod_le_prod
        (fun j _ => (hp _).le) (fun j _ => hm (by change j.val ≤ 8; omega))
      _ = _ := by simp
  have htotal : c ≤ (lam 8)^9 * lam 9 := by
    apply hprod.trans
    rw [Fin.prod_univ_castSucc]
    exact mul_le_mul_of_nonneg_right hnine (hp 9).le
  have hmul : c * lam 8 ≤ (lam 8)^10 * lam 9 := by
    nlinarith [mul_le_mul_of_nonneg_right htotal (hp 8).le]
  have hpow : (lam 8)^10 < Q^(-10*delta) := by
    have hh := pow_lt_pow_left₀ hsmall (hp 8).le (by decide : (10 : ℕ) ≠ 0)
    convert hh using 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_lt_one.trans hQ).le]
    congr 1
    ring
  apply (div_lt_div_iff₀ (hp 9) hc).mpr
  simpa only [mul_comm c] using hmul.trans_lt (mul_lt_mul_of_pos_right hpow (hp 9))

theorem absolute_gap_cutoff10 (c delta : ℝ) (hc : 0 < c) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (Q : ℝ), T < Q →
      ∀ (lam : Fin 10 → ℝ), (∀ i, 0 < lam i) → Monotone lam →
      c ≤ (∏ i, lam i) → lam 8 < Q^(-delta) → lam 8 < lam 9*Q^(-delta) := by
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 (1/c) (18*delta) (by positivity)
  refine ⟨T,hT,?_⟩
  intro Q hTQ lam hp hm hprod hsmall
  have hQ : 1 < Q := hT.trans hTQ
  have hq : 0 < Q := zero_lt_one.trans hQ
  have hcut' : 1/c < Q^(9*delta) := by
    convert hcut Q hTQ using 1; congr 1; ring
  have hr := absolute_ratio10 lam hp hm c Q delta hc hQ hprod hsmall
  have hle : Q^(-10*delta)/c ≤ Q^(-delta) := by
    calc
      _ = (1/c)*Q^(-10*delta) := by ring
      _ ≤ Q^(9*delta)*Q^(-10*delta) :=
        mul_le_mul_of_nonneg_right hcut'.le (Real.rpow_pos_of_pos hq _).le
      _ = _ := by rw [← Real.rpow_add hq]; congr 1; ring
  have hh := (div_lt_iff₀ (hp 9)).mp (hr.trans_le hle)
  simpa only [mul_comm] using hh

theorem source_absolute_gap_uniform10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ),
      (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) →
      (∑ i, (c0 i+c2 i+c3 i)) = 0 → T < Q →
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 8 < Q^(-delta) →
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 8 <
        sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9*Q^(-delta) := by
  obtain ⟨c,C,hc,hC,hbounds⟩ :=
    source_original_uniform_minima_two_sided10 A2 A3 L h2 h3 hL
  obtain ⟨T,hT,hgap⟩ := absolute_gap_cutoff10 c delta hc hd
  refine ⟨T,hT,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb hTQ hsmall
  have hp := sourceMinima10_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  exact hgap Q hTQ _ hp.1 hp.2 (hbounds Q hQ c0 c2 c3 hc2 hc3 hb).1 hsmall

end
end CompoundFeasibility.SourceAbsoluteGap10
