import SubspaceBridge.SourceSelectedVanishing4
import SubspaceBridge.SchlickeweiRealReference6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiReference4
open SourceSelectedDual4 OriginalSelectedSystem4
def finiteSupport4 (p : ℕ) [Fact p.Prime] (B : Matrix (Fin 4) (Fin 4) ℚ_[p])
    (b : Fin 4 → ℤ) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => dualValue4 B b i ≠ 0)

theorem finiteSupport_nonempty4 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 4) (Fin 4) ℚ_[p]) (hB : IsUnit B) (b : Fin 4 → ℤ) (hb : b ≠ 0) :
    (finiteSupport4 p B b).Nonempty := by
  by_contra h
  have hz : ∀ i, dualValue4 B b i = 0 := by
    intro i
    by_contra hi
    exact h ⟨i, by simp only [finiteSupport4, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi⟩
  have hvec : B⁻¹.transpose *ᵥ (fun k => (b k : ℚ_[p])) = 0 := by
    funext i
    exact hz i
  have hinv : IsUnit B⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hB
  have ht : IsUnit B⁻¹.transpose := (Matrix.isUnit_transpose B⁻¹).mpr hinv
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr ht
  have hb0 : (fun k => (b k : ℚ_[p])) = 0 := hi (hvec.trans (Matrix.mulVec_zero _).symm)
  apply hb
  funext i
  have he : (b i : ℚ_[p]) = 0 := congrFun hb0 i
  change b i = 0
  exact_mod_cast he

def publishedFloor4 (p : ℕ) (Q : ℝ) (c : Fin 4 → ℝ) (i : Fin 4) : ℤ :=
  ⌊Real.log Q / Real.log (p : ℝ) * (∑ k : Fin 3, c (i.succAbove k))⌋

def supportFloor4 (p : ℕ) (Q : ℝ) (c : Fin 4 → ℝ)
    (T : Finset (Fin 4)) (hT : T.Nonempty) : ℤ := T.inf' hT (publishedFloor4 p Q c)

theorem support_floor_spec4 (p : ℕ) (Q : ℝ) (c : Fin 4 → ℝ)
    (T : Finset (Fin 4)) (hT : T.Nonempty) :
    (∃ i ∈ T, supportFloor4 p Q c T hT = publishedFloor4 p Q c i) ∧
      ∀ i ∈ T, supportFloor4 p Q c T hT ≤ publishedFloor4 p Q c i := by
  exact ⟨T.exists_mem_eq_inf' hT _, fun i hi => Finset.inf'_le _ hi⟩

theorem three_floor_error4 (t : Fin 3 → ℝ) :
    (∑ i, ⌊t i⌋) ≤ ⌊∑ i, t i⌋ ∧ ⌊∑ i, t i⌋ ≤ (∑ i, ⌊t i⌋) + 2 := by
  have hlo : ((∑ i, ⌊t i⌋ : ℤ) : ℝ) ≤ ∑ i, t i := by
    push_cast
    exact Finset.sum_le_sum (fun i _ => Int.floor_le _)
  have hhi : (∑ i, t i) < ((∑ i, ⌊t i⌋ : ℤ) : ℝ) + 3 := by
    calc
      _ < ∑ i : Fin 3, (((⌊t i⌋ : ℤ) : ℝ) + 1) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => Int.lt_floor_add_one _)
      _ = _ := by simp [Finset.sum_add_distrib]
  have hg : (⌊∑ i, t i⌋ : ℝ) < ((∑ i, ⌊t i⌋ : ℤ) : ℝ) + 3 :=
    lt_of_le_of_lt (Int.floor_le _) hhi
  have hgZ : ⌊∑ i, t i⌋ < (∑ i, ⌊t i⌋) + 3 := by exact_mod_cast hg
  exact ⟨Int.le_floor.mpr hlo, by omega⟩

theorem three_floor_natceil_error4 (t : Fin 3 → ℝ) (ht : ∀ i, t i ≤ 0) :
    (∑ i, -(Nat.ceil (-t i) : ℤ)) ≤ ⌊∑ i, t i⌋ ∧
      ⌊∑ i, t i⌋ ≤ (∑ i, -(Nat.ceil (-t i) : ℤ)) + 2 := by
  have he (i : Fin 3) : -(Nat.ceil (-t i) : ℤ) = ⌊t i⌋ := by
    rw [Int.natCast_ceil_eq_ceil (neg_nonneg.mpr (ht i)), Int.ceil_neg, neg_neg]
  simp_rw [he]
  exact three_floor_error4 t

theorem published_floor_nonpos4 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q)
    (c : Fin 4 → ℝ) (hc : ∀ i, c i ≤ 0) (i : Fin 4) : publishedFloor4 p Q c i ≤ 0 := by
  apply Int.floor_nonpos
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact (div_pos (Real.log_pos hQ) (Real.log_pos hpR)).le
  · exact Finset.sum_nonpos (fun k _ => hc (i.succAbove k))


theorem support_floor_nonpos4 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q)
    (c : Fin 4 → ℝ) (hc : ∀ i, c i ≤ 0) (T : Finset (Fin 4)) (hT : T.Nonempty) :
    supportFloor4 p Q c T hT ≤ 0 := by
  obtain ⟨i, hi⟩ := hT
  exact (Finset.inf'_le _ hi).trans (published_floor_nonpos4 p hp Q hQ c hc i)

def rescaleMultiplier4 (g2 g3 : ℤ) : ℤ :=
  6 ^ (3 : ℕ) * 2 ^ (-g2).toNat * 3 ^ (-g3).toNat

def integerRescale4 (g2 g3 : ℤ) (b : Fin 4 → ℤ) : Fin 4 → ℤ := rescaleMultiplier4 g2 g3 • b

theorem rescale_multiplier_pos4 (g2 g3 : ℤ) : 0 < rescaleMultiplier4 g2 g3 := by
  unfold rescaleMultiplier4
  positivity

theorem integer_rescale_nonzero4 (g2 g3 : ℤ) (b : Fin 4 → ℤ) (hb : b ≠ 0) :
    integerRescale4 g2 g3 b ≠ 0 :=
  smul_ne_zero (ne_of_gt (rescale_multiplier_pos4 g2 g3)) hb

theorem integer_rescale_line4 (g2 g3 : ℤ) (b : Fin 4 → ℤ) :
    Submodule.span ℚ {fun i => (integerRescale4 g2 g3 b i : ℚ)} =
      Submodule.span ℚ {fun i => (b i : ℚ)} := by
  have he : (fun i => (integerRescale4 g2 g3 b i : ℚ)) =
      (rescaleMultiplier4 g2 g3 : ℚ) • (fun i => (b i : ℚ)) := by
    funext i
    simp only [integerRescale4, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  have hne : (rescaleMultiplier4 g2 g3 : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (rescale_multiplier_pos4 g2 g3))
  rw [he]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hne) _

theorem integer_rescale_published4 (g2 g3 : ℤ) (hg2 : g2 ≤ 0) (hg3 : g3 ≤ 0)
    (b : Fin 4 → ℤ) :
    (fun i => (integerRescale4 g2 g3 b i : ℚ)) =
      ((6 : ℚ) ^ (3 : ℕ) * 2 ^ (-g2) * 3 ^ (-g3)) • (fun i => (b i : ℚ)) := by
  have he2 : (2 : ℚ) ^ (-g2).toNat = (2 : ℚ) ^ (-g2) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (neg_nonneg.mpr hg2)]
  have he3 : (3 : ℚ) ^ (-g3).toNat = (3 : ℚ) ^ (-g3) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (neg_nonneg.mpr hg3)]
  funext i
  simp only [integerRescale4, rescaleMultiplier4, Pi.smul_apply, smul_eq_mul,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  rw [he2, he3]


theorem rescale_multiplier_factor4 (g2 g3 : ℤ) :
    rescaleMultiplier4 g2 g3 =
      (2 : ℤ) ^ (3 + (-g2).toNat) * (3 : ℤ) ^ (3 + (-g3).toNat) := by
  unfold rescaleMultiplier4
  rw [show (6 : ℤ) = 2 * 3 by norm_num, mul_pow, pow_add, pow_add]
  ring

theorem rescale_p2_norm4 (g2 g3 : ℤ) (hg2 : g2 ≤ 0) :
    ‖(rescaleMultiplier4 g2 g3 : ℚ_[2])‖ ≤ (2 : ℝ) ^ (g2 - 3) := by
  have hd : (2 : ℤ) ^ (3 + (-g2).toNat) ∣ rescaleMultiplier4 g2 g3 := by
    rw [rescale_multiplier_factor4]
    exact dvd_mul_right _ _
  have hn := (SchlickeweiIntegerPairing6.integer_norm_dvd6 2
    (rescaleMultiplier4 g2 g3) (3 + (-g2).toNat)).mpr hd
  have hc : ((-g2).toNat : ℤ) = -g2 := Int.toNat_of_nonneg (neg_nonneg.mpr hg2)
  have he : -((3 + (-g2).toNat : ℕ) : ℤ) = g2 - 3 := by
    simp only [Nat.cast_add, Nat.cast_ofNat, hc]
    ring
  simpa only [he] using hn

theorem rescale_p3_norm4 (g2 g3 : ℤ) (hg3 : g3 ≤ 0) :
    ‖(rescaleMultiplier4 g2 g3 : ℚ_[3])‖ ≤ (3 : ℝ) ^ (g3 - 3) := by
  have hd : (3 : ℤ) ^ (3 + (-g3).toNat) ∣ rescaleMultiplier4 g2 g3 := by
    rw [rescale_multiplier_factor4]
    exact dvd_mul_left _ _
  have hn := (SchlickeweiIntegerPairing6.integer_norm_dvd6 3
    (rescaleMultiplier4 g2 g3) (3 + (-g3).toNat)).mpr hd
  have hc : ((-g3).toNat : ℤ) = -g3 := Int.toNat_of_nonneg (neg_nonneg.mpr hg3)
  have he : -((3 + (-g3).toNat : ℕ) : ℤ) = g3 - 3 := by
    simp only [Nat.cast_add, Nat.cast_ofNat, hc]
    ring
  simpa only [he] using hn


open SchlickeweiIntegerPairing6

theorem floor_rounded_exponents4 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q)
    (c : Fin 4 → ℝ) (hc : ∀ i, c i ≤ 0) (f : Fin 4 → ℤ)
    (hf : ∀ i, f i = -(Nat.ceil (JSP000334.qThreshold p Q (c i)) : ℤ)) (i : Fin 4) :
    (∑ k : Fin 3, f (i.succAbove k)) ≤ publishedFloor4 p Q c i ∧
      publishedFloor4 p Q c i ≤ (∑ k : Fin 3, f (i.succAbove k)) + 2 := by
  let t : Fin 4 → ℝ := fun j => Real.log Q / Real.log (p : ℝ) * c j
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have ht (j : Fin 4) : t j ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_pos (Real.log_pos hQ) (Real.log_pos hpR)).le (hc j)
  have he (j : Fin 4) : JSP000334.qThreshold p Q (c j) = -t j := by
    unfold JSP000334.qThreshold t
    ring
  have hsum : (∑ k : Fin 3, f (i.succAbove k)) =
      ∑ k : Fin 3, -(Nat.ceil (-t (i.succAbove k)) : ℤ) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hf, he]
  have hr := three_floor_natceil_error4 (fun k => t (i.succAbove k)) (fun k => ht _)
  have hreal : (∑ k : Fin 3, t (i.succAbove k)) =
      Real.log Q / Real.log (p : ℝ) * (∑ k : Fin 3, c (i.succAbove k)) := by
    simp only [t, Finset.mul_sum]
  rw [hreal, ← hsum] at hr
  exact hr


theorem integer_rescale_dual_norm4 {K : Type*} [NormedField K] [CharZero K]
    (B : Matrix (Fin 4) (Fin 4) K) (g2 g3 : ℤ) (b : Fin 4 → ℤ) (i : Fin 4) :
    ‖dualValue4 B (integerRescale4 g2 g3 b) i‖ =
      ‖(rescaleMultiplier4 g2 g3 : K)‖*‖dualValue4 B b i‖ := by
  have he := dualValue4_scaling B (integerRescale4 g2 g3 b) b
    (rescaleMultiplier4 g2 g3) (fun _ => rfl) i
  rw [he,norm_mul]

theorem integer_rescale_finite_bound4 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 4) (Fin 4) ℚ_[p]) (g2 g3 g : ℤ) (b : Fin 4 → ℤ)
    (r : Fin 4 → ℤ)
    (hcoef : ‖(rescaleMultiplier4 g2 g3 : ℚ_[p])‖ ≤ (p : ℝ)^(g-3))
    (hb : ∀ i, ‖dualValue4 B b i‖ ≤ 1)
    (hg : ∀ i ∈ finiteSupport4 p B b, g ≤ r i+2) (i : Fin 4) :
    ‖dualValue4 B (integerRescale4 g2 g3 b) i‖ ≤ (p : ℝ)^r i := by
  rw [integer_rescale_dual_norm4]
  by_cases hz : dualValue4 B b i = 0
  · rw [hz,norm_zero,mul_zero]
    positivity
  · have hi : i ∈ finiteSupport4 p B b := by
      simp only [finiteSupport4,Finset.mem_filter,Finset.mem_univ,true_and]
      exact hz
    have hex : g-3 ≤ r i := by have h := hg i hi; omega
    have hpbase : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    calc
      _ ≤ (p : ℝ)^(g-3)*1 := mul_le_mul hcoef (hb i) (norm_nonneg _) (by positivity)
      _ = (p : ℝ)^(g-3) := mul_one _
      _ ≤ _ := zpow_le_zpow_right₀ hpbase hex

theorem floor_growth4 (Q u v : ℝ) (hQ : 1 < Q) :
    (6 : ℝ)^3*(2 : ℝ)^(-⌊Real.log Q/Real.log 2*u⌋ : ℤ)*
      (3 : ℝ)^(-⌊Real.log Q/Real.log 3*v⌋ : ℤ) ≤ (6 : ℝ)^4*Q^(-u-v) := by
  have h2 := SchlickeweiRealReference6.floor_power_bound6 2 Q u (by norm_num) hQ
  have h3 := SchlickeweiRealReference6.floor_power_bound6 3 Q v (by norm_num) hQ
  calc
    _ ≤ (6 : ℝ)^3*(2*Q^(-u))*(3*Q^(-v)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h2 (by positivity)) h3 (by positivity) (by positivity)
    _ = _ := by rw [sub_eq_add_neg,Real.rpow_add (zero_lt_one.trans hQ)]; ring


theorem omitted_balance_gap4 (c : Fin 3 → Fin 4 → ℝ) (delta : ℝ)
    (hb : (∑ tau, ∑ i, c tau i) = 0) (s : MixedIndex4)
    (hs : (∑ tau, c tau (s tau)) < -delta/2) :
    -(∑ k : Fin 3, c 1 ((s 1).succAbove k)) - (∑ k : Fin 3, c 2 ((s 2).succAbove k)) <
      (∑ i : Fin 4, c 0 i) - c 0 (s 0) - delta/2 := by
  have h1 := Fin.sum_univ_succAbove (c 1) (s 1)
  have h2 := Fin.sum_univ_succAbove (c 2) (s 2)
  simp only [Fin.sum_univ_three] at hb hs
  linarith

theorem power_covolume4 (Q delta C : ℝ) (c : Fin 3 → Fin 4 → ℝ)
    (hQ : 0 < Q) (hc : (∏ j, Q^(c 0 j)) ≤ C) (i : Fin 4) :
    Q^((∑ j : Fin 4, c 0 j)-c 0 i-delta/2) ≤
      (C/Q^(c 0 i))*Q^(-delta/2) := by
  have hw : Q^(∑ j : Fin 4, c 0 j) ≤ C := by
    rwa [Real.rpow_sum_of_pos hQ]
  calc
    _ = (Q^(∑ j : Fin 4, c 0 j)/Q^(c 0 i))*Q^(-delta/2) := by
      rw [Real.rpow_sub hQ,Real.rpow_sub hQ,
        show -delta/2 = -(delta/2) by ring,Real.rpow_neg hQ.le,div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hw (Real.rpow_pos_of_pos hQ _).le) (by positivity)

theorem reference_real_coordinate4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (Q delta C : ℝ) (hQ : 1 < Q) (A c2 c3 : Fin 4 → ℝ) (hA : ∀ i, 0 < A i)
    (hb : (∏ i, A i)*(∏ i, Q^(c2 i+c3 i)) = 1) (hc : (∏ i, A i) ≤ C)
    (b : Fin 4 → ℤ) (k : ℤ) (s : MixedIndex4)
    (h2s : dualValue4 (A2.map (algebraMap ℚ ℚ_[2])) b (s 1) ≠ 0)
    (h3s : dualValue4 (A3.map (algebraMap ℚ ℚ_[3])) b (s 2) ≠ 0)
    (hz : ∀ s ∈ publishedIndexSet4 Q delta A c2 c3, mixedProduct4 A2 A3 L b s = 0)
    (hgrowth : |(k : ℝ)| ≤ (6 : ℝ)^4 * Q^
      (-(∑ j : Fin 3, c2 ((s 1).succAbove j))-(∑ j : Fin 3, c3 ((s 2).succAbove j)))) :
    ‖dualValue4 L (k • b) (s 0)‖ ≤
      ((6 : ℝ)^4*‖dualValue4 L b (s 0)‖)*(C/A (s 0))*Q^(-delta/2) := by
  have hscale : dualValue4 L (k • b) (s 0) = (k : ℝ)*dualValue4 L b (s 0) :=
    dualValue4_scaling L _ b k (fun _ => rfl) (s 0)
  have hC : 0 ≤ C := (Finset.prod_nonneg (fun i _ => (hA i).le)).trans hc
  by_cases hs : s ∈ publishedIndexSet4 Q delta A c2 c3
  · have hzero := hz s hs
    have hr : dualValue4 L b (s 0) = 0 := by
      have hpn : ‖dualValue4 (A2.map (algebraMap ℚ ℚ_[2])) b (s 1)‖ ≠ 0 := norm_ne_zero_iff.mpr h2s
      have hqn : ‖dualValue4 (A3.map (algebraMap ℚ ℚ_[3])) b (s 2)‖ ≠ 0 := norm_ne_zero_iff.mpr h3s
      exact norm_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hqn)).resolve_right hpn)
    rw [hscale,hr,mul_zero,norm_zero]
    simp only [mul_zero,zero_mul,le_refl]
  · let c := logarithmicWeights4 Q A c2 c3
    have hgap : (∑ tau, c tau (s tau)) < -delta/2 :=
      lt_of_not_ge (fun h => hs ((published_index_logarithmic4 Q delta hQ A c2 c3 hA s).mpr h))
    have he := omitted_balance_gap4 c delta (logarithmic_balance4 Q hQ A c2 c3 hA hb) s hgap
    have hw : ∏ j, Q^(c 0 j) ≤ C := by
      have hi (j) : Q^(c 0 j) = A j := by
        exact logarithmic_width4 Q hQ A hA j
      simpa only [hi] using hc
    have hpower := (Real.rpow_le_rpow_of_exponent_le hQ.le he.le).trans
      (power_covolume4 Q delta C c (zero_lt_one.trans hQ) hw (s 0))
    have hwidth : Q^(c 0 (s 0)) = A (s 0) := logarithmic_width4 Q hQ A hA (s 0)
    rw [hwidth] at hpower
    change Q^(-(∑ j : Fin 3, c2 ((s 1).succAbove j))-(∑ j : Fin 3, c3 ((s 2).succAbove j))) ≤ _ at hpower
    rw [hscale,norm_mul,Real.norm_eq_abs]
    calc
      _ ≤ ((6 : ℝ)^4*Q^(-(∑ j : Fin 3, c2 ((s 1).succAbove j))-
          (∑ j : Fin 3, c3 ((s 2).succAbove j))))*‖dualValue4 L b (s 0)‖ :=
        mul_le_mul_of_nonneg_right hgrowth (norm_nonneg _)
      _ ≤ ((6 : ℝ)^4*((C/A (s 0))*Q^(-delta/2)))*‖dualValue4 L b (s 0)‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower (by positivity)) (norm_nonneg _)
      _ = _ := by ring

end CompoundFeasibility.SchlickeweiReference4
