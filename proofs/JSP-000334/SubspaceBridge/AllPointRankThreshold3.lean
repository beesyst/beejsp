import SubspaceBridge.CofactorOriginalRankOne3
open scoped BigOperators Matrix
namespace JSP000334

theorem allpoint_rank_cutoff3 (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : ℝ, C < Q →
      6 * (Q ^ (-epsilon)) ^ 3 * (Q ^ (epsilon / 8)) ^ 4 < 1 := by
  obtain ⟨C,hC⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < 5*epsilon/2 by linarith)).eventually
      (Filter.eventually_gt_atTop 6))
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro Q hQ
  have hq : 0 < Q := lt_of_lt_of_le zero_lt_one ((le_max_left 1 C).trans hQ.le)
  have hh : 6 < Q^(5*epsilon/2) := hC Q (lt_of_le_of_lt (le_max_right 1 C) hQ).le
  have hp : 0 < Q^(-(5*epsilon/2)) := Real.rpow_pos_of_pos hq _
  have hmul := mul_lt_mul_of_pos_right hh hp
  rw [← Real.rpow_add hq,add_neg_cancel,Real.rpow_zero] at hmul
  have heq : (Q^(-epsilon))^3*(Q^(epsilon/8))^4 = Q^(-(5*epsilon/2)) := by
    rw [← Real.rpow_mul_natCast hq.le,← Real.rpow_mul_natCast hq.le,← Real.rpow_add hq]
    congr 1
    ring
  simpa only [mul_assoc,heq] using hmul

theorem allpoint_rank_scalar3 (a b c g t q : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (ht : 0 < t) (hq : 1 ≤ q)
    (hab : a ≤ b) (hbc : b ≤ c) (hag : a ≤ g) (hgt : g ≤ t)
    (hp : (1 : ℝ)/6 ≤ a*b*c) (hcut : 6*t^3*q^4 < 1) :
    (b < c/q ∧ g < c) ∨ (c/q ≤ b ∧ a < b/q ∧ g < b) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hprod : a*b*c ≤ t*c^2 := by
    have h1 := mul_le_mul_of_nonneg_right (hag.trans hgt) hb.le
    have h2 := mul_le_mul_of_nonneg_left hbc ht.le
    nlinarith [mul_le_mul_of_nonneg_right (h1.trans h2) hc.le]
  have hbig : t*q^2 < c := by
    by_contra h
    have hle : c ≤ t*q^2 := le_of_not_gt h
    have hsq := mul_self_le_mul_self hc.le hle
    have hm := mul_le_mul_of_nonneg_left hsq ht.le
    have htprod : t*(t*q^2*(t*q^2)) = t^3*q^4 := by ring
    rw [htprod] at hm
    nlinarith
  have hq2 : 1 ≤ q^2 := by nlinarith
  have htc : t < c := (by nlinarith : t ≤ t*q^2).trans_lt hbig
  by_cases hgap : b < c/q
  · exact Or.inl ⟨hgap,hgt.trans_lt htc⟩
  · have hbq : c ≤ b*q := (div_le_iff₀ hq0).mp (le_of_not_gt hgap)
    have htb : t*q < b := by
      have hh : t*q^2 < b*q := hbig.trans_le hbq
      nlinarith
    have hgb : g < b := hgt.trans_lt ((by nlinarith : t ≤ t*q).trans_lt htb)
    have haq : a*q < b := (mul_le_mul_of_nonneg_right (hag.trans hgt) hq0.le).trans_lt htb
    exact Or.inr ⟨le_of_not_gt hgap,(lt_div_iff₀ hq0).mpr haq,hgb⟩

end JSP000334

namespace JSP000334

theorem allpoint_rank_threshold3 (epsilon Q : ℝ) (he : 0 < epsilon) (hQ : 1 < Q)
    (hcut : 6*(Q^(-epsilon))^3*(Q^(epsilon/8))^4 < 1)
    (B : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (v : Fin 3 → RealTriple) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice3 B)
    (hatt : ∀ i, coordinateGauge3 e (v i) = successiveRadius3 B e i)
    (z : RealTriple) (hz : z ∈ lattice3 B) (hnz : z ≠ 0)
    (hshort : coordinateGauge3 e z ≤ Q^(-epsilon))
    (hprod : (1 : ℝ)/6 ≤ ∏ i, successiveRadius3 B e i) :
    ∃ k : Fin 3, (k = 1 ∨ k = 2) ∧
      successiveRadius3 B e (k-1) < successiveRadius3 B e k*Q^(-(epsilon/8)) ∧
      coordinateGauge3 e z < successiveRadius3 B e k ∧ z ∈ minimaFlag3 v k := by
  have hQ0 := lt_trans zero_lt_one hQ
  let l := successiveRadius3 B e
  obtain ⟨_,_,_,hl,hm,_⟩ := exists_successive_minima3 B e
  have hfirst : l 0 ≤ coordinateGauge3 e z := by
    apply successiveRadius3_le_family B e 0 (fun _ : Fin 1 => z)
    · exact linearIndependent_unique (fun _ : Fin 1 => z) hnz
    · intro i; exact hz
    · intro i; exact le_rfl
  have hq : 1 ≤ Q^(epsilon/8) :=
    Real.one_le_rpow hQ.le (by linarith)
  have hpow : Q^(-(epsilon/8)) = (Q^(epsilon/8))⁻¹ := Real.rpow_neg hQ0.le _
  have hp : (1 : ℝ)/6 ≤ l 0*l 1*l 2 := by simpa [Fin.prod_univ_three,l] using hprod
  obtain hh | hh := allpoint_rank_scalar3 (l 0) (l 1) (l 2) (coordinateGauge3 e z)
    (Q^(-epsilon)) (Q^(epsilon/8)) (hl 0) (hl 1) (hl 2)
    (Real.rpow_pos_of_pos hQ0 _) hq hm.1 hm.2 hfirst hshort hp hcut
  · have hg : l 1 < l 2*Q^(-(epsilon/8)) := by
      rw [hpow]
      simpa only [div_eq_mul_inv] using hh.1
    have hgap : ∀ i : Fin 3, i < 2 → l i < l 2 := by
      intro i hi
      have hfac : Q^(-(epsilon/8)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
      have h12 : l 1 < l 2 := hg.trans (by nlinarith [hl 2])
      exact (successiveRadius3_monotone B e (show i ≤ 1 by omega)).trans_lt h12
    exact ⟨2,Or.inr rfl,by simpa using hg,hh.2,
      lattice3_short_mem_minimaFlag B e v hv hvL hatt 2 hgap z hz hh.2⟩
  · have hg : l 0 < l 1*Q^(-(epsilon/8)) := by
      rw [hpow]
      simpa only [div_eq_mul_inv] using hh.2.1
    have hgap : ∀ i : Fin 3, i < 1 → l i < l 1 := by
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      have hfac : Q^(-(epsilon/8)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
      exact hg.trans (by nlinarith [hl 1])
    exact ⟨1,Or.inl rfl,by simpa using hg,hh.2.2,
      lattice3_short_mem_minimaFlag B e v hv hvL hatt 1 hgap z hz hh.2.2⟩

end JSP000334
