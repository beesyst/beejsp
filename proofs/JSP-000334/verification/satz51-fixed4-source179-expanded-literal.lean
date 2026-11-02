import SubspaceBridge.SourceSelectedVanishing4
import SubspaceBridge.SchlickeweiRealReference6

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiReference4Literal179
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

end CompoundFeasibility.SchlickeweiReference4Literal179

end

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179
open SchlickeweiReference4Literal179 SourceSelectedDual4 OriginalSelectedSystem4 OriginalDeformedSource4

def sourceExponent4 (p : ℕ) (q : ℝ) (c : Fin 4 → ℝ) (i : Fin 4) : ℤ :=
  -(Nat.ceil (JSP000334.qThreshold p q (c i)) : ℤ)

theorem source_exponent_rescaling4 (p : ℕ) (q : ℝ) (c : Fin 4 → ℝ) (i : Fin 4) :
    sourceExponent4 p q c i = -(Nat.ceil (JSP000334.qThreshold p (q^(5 : ℕ)) (c i/5)) : ℤ) := by
  unfold sourceExponent4 JSP000334.qThreshold
  congr 3
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  ring

def sourceFloor4 (p : ℕ) (q : ℝ) (c : Fin 4 → ℝ) (T : Finset (Fin 4)) (hT : T.Nonempty) : ℤ :=
  supportFloor4 p (q^(5 : ℕ)) (fun i => c i/5) T hT

def rescaledReference4 (q : ℝ) (c2 c3 : Fin 4 → ℝ)
    (T2 T3 : Finset (Fin 4)) (hT2 : T2.Nonempty) (hT3 : T3.Nonempty) (b : Fin 4 → ℤ) : Fin 4 → ℤ :=
  integerRescale4 (sourceFloor4 2 q c2 T2 hT2) (sourceFloor4 3 q c3 T3 hT3) b

theorem source_floor_nonpos4 (p : ℕ) (hp : 1 < p) (q : ℝ) (hq : 1 < q)
    (c : Fin 4 → ℝ) (hc : ∀ i, c i ≤ 0) (T : Finset (Fin 4)) (hT : T.Nonempty) :
    sourceFloor4 p q c T hT ≤ 0 :=
  support_floor_nonpos4 p hp _ (one_lt_pow₀ hq (by decide)) _
    (fun i => div_nonpos_of_nonpos_of_nonneg (hc i) (by norm_num)) T hT

theorem source_floor_rounded4 (p : ℕ) (hp : 1 < p) (q : ℝ) (hq : 1 < q)
    (c : Fin 4 → ℝ) (hc : ∀ i, c i ≤ 0) (T : Finset (Fin 4)) (hT : T.Nonempty) :
    ∀ i ∈ T, sourceFloor4 p q c T hT ≤ (∑ k : Fin 3, sourceExponent4 p q c (i.succAbove k))+2 := by
  intro i hi
  have hm := (support_floor_spec4 p (q^(5 : ℕ)) (fun i => c i/5) T hT).2 i hi
  exact hm.trans (floor_rounded_exponents4 p hp _ (one_lt_pow₀ hq (by decide)) _
    (fun i => div_nonpos_of_nonpos_of_nonneg (hc i) (by norm_num)) _
    (source_exponent_rescaling4 p q c) i).2

theorem rescaled_reference_finite4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (b : Fin 4 → ℤ)
    (hT2 : (finiteSupport4 2 (A2.map (algebraMap ℚ ℚ_[2])) b).Nonempty)
    (hT3 : (finiteSupport4 3 (A3.map (algebraMap ℚ ℚ_[3])) b).Nonempty)
    (q : ℝ) (hq : 1 < q) (c2 c3 : Fin 4 → ℝ)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (hb2 : ∀ i, ‖dualValue4 (A2.map (algebraMap ℚ ℚ_[2])) b i‖ ≤ 1)
    (hb3 : ∀ i, ‖dualValue4 (A3.map (algebraMap ℚ ℚ_[3])) b i‖ ≤ 1) :
    let y := rescaledReference4 q c2 c3 _ _ hT2 hT3 b
    (∀ i, ‖dualValue4 (A2.map (algebraMap ℚ ℚ_[2])) y i‖ ≤
      (2 : ℝ)^(∑ k : Fin 3, sourceExponent4 2 q c2 (i.succAbove k))) ∧
    (∀ i, ‖dualValue4 (A3.map (algebraMap ℚ ℚ_[3])) y i‖ ≤
      (3 : ℝ)^(∑ k : Fin 3, sourceExponent4 3 q c3 (i.succAbove k))) := by
  dsimp only
  let g2 := sourceFloor4 2 q c2 _ hT2
  let g3 := sourceFloor4 3 q c3 _ hT3
  have hn2 : g2 ≤ 0 := source_floor_nonpos4 2 (by decide) q hq c2 hc2 _ hT2
  have hn3 : g3 ≤ 0 := source_floor_nonpos4 3 (by decide) q hq c3 hc3 _ hT3
  constructor
  · exact integer_rescale_finite_bound4 2 _ g2 g3 g2 b _ (rescale_p2_norm4 g2 g3 hn2) hb2
      (source_floor_rounded4 2 (by decide) q hq c2 hc2 _ hT2)
  · exact integer_rescale_finite_bound4 3 _ g2 g3 g3 b _ (rescale_p3_norm4 g2 g3 hn3) hb3
      (source_floor_rounded4 3 (by decide) q hq c3 hc3 _ hT3)

theorem multiplier_real_growth4 (g2 g3 : ℤ) (hg2 : g2 ≤ 0) (hg3 : g3 ≤ 0)
    (Q u v : ℝ) (hQ : 1 < Q)
    (he2 : g2 = ⌊Real.log Q/Real.log 2*u⌋) (he3 : g3 = ⌊Real.log Q/Real.log 3*v⌋) :
    |(rescaleMultiplier4 g2 g3 : ℝ)| ≤ (6 : ℝ)^4*Q^(-u-v) := by
  have hc2 : ((-g2).toNat : ℤ) = -g2 := Int.toNat_of_nonneg (neg_nonneg.mpr hg2)
  have hc3 : ((-g3).toNat : ℤ) = -g3 := Int.toNat_of_nonneg (neg_nonneg.mpr hg3)
  have he : (rescaleMultiplier4 g2 g3 : ℝ) = (6 : ℝ)^3*(2 : ℝ)^(-g2)*(3 : ℝ)^(-g3) := by
    simp only [rescaleMultiplier4,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
    have hp2 : (2 : ℝ)^(-g2).toNat = (2 : ℝ)^(-g2) := by rw [← zpow_natCast,hc2]
    have hp3 : (3 : ℝ)^(-g3).toNat = (3 : ℝ)^(-g3) := by rw [← zpow_natCast,hc3]
    rw [hp2,hp3]
  rw [he,abs_of_pos (by positivity),he2,he3]
  exact floor_growth4 Q u v hQ


def referenceRealConstant4 (L : Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 4 → ℤ) : ℝ :=
  (6 : ℝ)^4*(1+∑ i : Fin 4, ‖dualValue4 L b i‖)

theorem reference_real_constant_pos4 (L : Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 4 → ℤ) :
    0 < referenceRealConstant4 L b := by unfold referenceRealConstant4; positivity

theorem reference_real_constant_bound4 (L : Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 4 → ℤ) (i : Fin 4) :
    (6 : ℝ)^4*‖dualValue4 L b i‖ ≤ referenceRealConstant4 L b := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := Finset.single_le_sum (f := fun j : Fin 4 => ‖dualValue4 L b j‖)
    (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  exact h.trans (le_add_of_nonneg_left zero_le_one)

theorem rescaled_reference_real_decay4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 4 → ℤ)
    (hT2 : (finiteSupport4 2 (A2.map (algebraMap ℚ ℚ_[2])) b).Nonempty)
    (hT3 : (finiteSupport4 3 (A3.map (algebraMap ℚ ℚ_[3])) b).Nonempty)
    (q delta C : ℝ) (hq : 1 < q) (A c2 c3 : Fin 4 → ℝ) (hA : ∀ i, 0 < A i)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (hb : (∏ i, A i)*(∏ i, (q^(5 : ℕ))^(c2 i/5+c3 i/5)) = 1) (hc : (∏ i, A i) ≤ C)
    (hz : ∀ s ∈ publishedIndexSet4 (q^(5 : ℕ)) delta A (fun i => c2 i/5) (fun i => c3 i/5),
      mixedProduct4 A2 A3 L b s = 0) (i : Fin 4) :
    ‖dualValue4 L (rescaledReference4 q c2 c3 _ _ hT2 hT3 b) i‖ ≤
      referenceRealConstant4 L b*(C/A i)*(q^(5 : ℕ))^(-delta/2) := by
  let g2 := sourceFloor4 2 q c2 _ hT2
  let g3 := sourceFloor4 3 q c3 _ hT3
  obtain ⟨j2,hj2,he2⟩ := (support_floor_spec4 2 (q^(5 : ℕ)) (fun i => c2 i/5) _ hT2).1
  obtain ⟨j3,hj3,he3⟩ := (support_floor_spec4 3 (q^(5 : ℕ)) (fun i => c3 i/5) _ hT3).1
  let s : MixedIndex4 := ![i,j2,j3]
  have hn2 : dualValue4 (A2.map (algebraMap ℚ ℚ_[2])) b j2 ≠ 0 := (Finset.mem_filter.mp hj2).2
  have hn3 : dualValue4 (A3.map (algebraMap ℚ ℚ_[3])) b j3 ≠ 0 := (Finset.mem_filter.mp hj3).2
  have hq5 : 1 < q^(5 : ℕ) := one_lt_pow₀ hq (by decide)
  have hkg := multiplier_real_growth4 g2 g3
    (source_floor_nonpos4 2 (by decide) q hq c2 hc2 _ hT2)
    (source_floor_nonpos4 3 (by decide) q hq c3 hc3 _ hT3)
    (q^(5 : ℕ)) (∑ k : Fin 3, c2 (j2.succAbove k)/5)
    (∑ k : Fin 3, c3 (j3.succAbove k)/5) hq5 he2 he3
  have hr := reference_real_coordinate4 A2 A3 L (q^(5 : ℕ)) delta C hq5 A
    (fun i => c2 i/5) (fun i => c3 i/5) hA hb hc b (rescaleMultiplier4 g2 g3) s hn2 hn3 hz hkg
  have hC : 0 ≤ C := (Finset.prod_nonneg (fun j _ => (hA j).le)).trans hc
  exact hr.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (reference_real_constant_bound4 L b i) (div_nonneg hC (hA i).le))
    (by positivity))


theorem reference_decay_cutoff4 (C delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ q : ℝ, T < q → 1 < q → C*(q^(5 : ℕ))^(-delta/2) ≤ 1 := by
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 C delta hd
  refine ⟨T,hT,?_⟩
  intro q hq hq1
  have hq5 : 1 < q^(5 : ℕ) := one_lt_pow₀ hq1 (by decide)
  have hpow : C < (q^(5 : ℕ))^(delta/2) :=
    hcut _ (hq.trans_le (le_self_pow₀ hq1.le (by decide)))
  rw [show -delta/2 = -(delta/2) by ring,Real.rpow_neg (zero_lt_one.trans hq5).le]
  exact (by simpa only [div_eq_mul_inv] using
    ((div_lt_one (Real.rpow_pos_of_pos (zero_lt_one.trans hq5) _)).mpr hpow).le)

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
  {U : Set ℝ} {hQU : ∀ q ∈ U, 1 < q}
  {u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3}

open OriginalDeformedSource4 OriginalDeformation4 OriginalAuxiliaryGeometry4 OriginalAuxiliaryDual4

theorem rescaled_reference_auxiliary4
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hd : 0 < delta)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q))
    (S : Finset MixedIndex4)
    (hselected : ∀ q : U, publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
      (SourceWeights4.frameWidths F q) (fun i => c2 i/5) (fun i => c3 i/5) = S)
    (b : Fin 4 → ℤ)
    (hT2 : (finiteSupport4 2 (A2.map (algebraMap ℚ ℚ_[2])) b).Nonempty)
    (hT3 : (finiteSupport4 3 (A3.map (algebraMap ℚ ℚ_[3])) b).Nonempty)
    (hb2 : ∀ i, ‖dualValue4 (A2.map (algebraMap ℚ ℚ_[2])) b i‖ ≤ 1)
    (hb3 : ∀ i, ‖dualValue4 (A3.map (algebraMap ℚ ℚ_[3])) b i‖ ≤ 1)
    (hz : ∀ s ∈ S, mixedProduct4 A2 A3 L b s = 0) :
    ∃ T : ℝ, 1 < T ∧ ∀ q : U, T < q.val →
      auxiliaryInteger4 A2 A3 L
        (fun i => Nat.ceil (JSP000334.qThreshold 2 q.val (c2 i)))
        (fun i => Nat.ceil (JSP000334.qThreshold 3 q.val (c3 i)))
        (SourceWeights4.frameWidths F q) (rescaledReference4 q.val c2 c3 _ _ hT2 hT3 b) := by
  obtain ⟨T,hT,hcut⟩ := reference_decay_cutoff4 (referenceRealConstant4 L b) (delta/24) (by positivity)
  refine ⟨T,hT,?_⟩
  intro q hq
  have hq1 := hQU q.val q.property
  have hfinite := rescaled_reference_finite4 A2 A3 b hT2 hT3 q.val hq1 c2 c3 hc2 hc3 hb2 hb3
  refine ⟨?_,hfinite.1,hfinite.2⟩
  intro i
  let A := SourceWeights4.frameWidths F q
  let C := ZLattice.covolume (integerRealImage (originalSourceGroup4 A2 A3 q.val c2 c3))
  have hbalance : (∏ i, A i)*(∏ i, (q.val^(5 : ℕ))^(c2 i/5+c3 i/5)) = 1 := by
    convert (F q).balance using 2
    apply Finset.prod_congr rfl
    intro j _
    rw [← add_div,rescaled_power4 q.val _ (zero_lt_one.trans hq1)]
  have hcov : (∏ i, A i) ≤ C := balanced_width_product_covolume4 A2 A3 h2 h3 q.val hq1 A c2 c3 (F q).balance
  have hzero : ∀ s ∈ publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24) A
      (fun i => c2 i/5) (fun i => c3 i/5), mixedProduct4 A2 A3 L b s = 0 := by
    intro s hs
    exact hz s ((hselected q) ▸ hs)
  have hr := rescaled_reference_real_decay4 A2 A3 L b hT2 hT3 q.val (delta/24) C hq1
    A c2 c3 (F q).widths_pos hc2 hc3 hbalance hcov hzero i
  have hC : 0 ≤ C := (Finset.prod_nonneg (fun j _ => (F q).widths_pos j |>.le)).trans hcov
  have hdv : 0 ≤ C/A i := div_nonneg hC ((F q).widths_pos i).le
  calc
    _ ≤ referenceRealConstant4 L b*(C/A i)*(q.val^(5 : ℕ))^(-(delta/24)/2) := hr
    _ = (C/A i)*(referenceRealConstant4 L b*(q.val^(5 : ℕ))^(-(delta/24)/2)) := by ring
    _ ≤ C/A i := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hcut q.val hq hq1) hdv

end CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179

end

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiFixedLine4Literal179
open SchlickeweiReference4Literal179 SchlickeweiReferenceRescaling4Literal179 SourceSelectedDual4
open OriginalSelectedSystem4 OriginalDeformedSource4 OriginalDeformation4
open OriginalAuxiliaryGeometry4 OriginalAuxiliaryDual4 OriginalLastDual4

theorem cofactor_finite_unit4 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) (e : Fin 4 → ℕ)
    (v : Fin 4 → Fin 4 → ℤ) (hv : ∀ j, v j ∈ lattice4 p A e) (i : Fin 4) :
    ‖dualValue4 (A.map (algebraMap ℚ ℚ_[p])) (integerLastDual4 v) i‖ ≤ 1 := by
  have hbound := finite_cofactor_bound4 p A hA e v hv i
  have he : (∑ k : Fin 3, -(e (i.succAbove k) : ℤ)) ≤ 0 :=
    Finset.sum_nonpos (fun k _ => by omega)
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  exact hbound.trans (by simpa only [zpow_zero] using zpow_le_zpow_right₀ hp he)

theorem nonzero_mem_line_span4 (x y : Fin 4 → ℚ) (hx : x ≠ 0)
    (hxy : x ∈ Submodule.span ℚ {y}) : Submodule.span ℚ {x} = Submodule.span ℚ {y} := by
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hxy
  have hne : a ≠ 0 := by intro hz; rw [hz,zero_smul] at ha; exact hx ha.symm
  rw [← ha]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hne) y

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
  {U : Set ℝ} {hQU : ∀ q ∈ U, 1 < q}
  {u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3}

theorem same_deformed_auxiliary_line4
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1) (hd : 0 < delta)
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q)) :
    ∃ T : ℝ, 1 < T ∧ ∀ q : U, T < q.val → ∀ y : Fin 4 → ℤ,
      auxiliaryInteger4 A2 A3 L
        (fun i => Nat.ceil (JSP000334.qThreshold 2 q.val (c2 i)))
        (fun i => Nat.ceil (JSP000334.qThreshold 3 q.val (c3 i)))
        (SourceWeights4.frameWidths F q) y →
      (∀ j : Fin 3, integerPairing4 ((F q).w j.castSucc : Fin 4 → ℤ) y = 0) ∧
      (fun i => (y i : ℚ)) ∈ Submodule.span ℚ
        {lastDual4 (fun j i => (((F q).w j : Fin 4 → ℤ) i : ℚ)) (F q).rational_independent} := by
  have hLd : L.det ≠ 0 := by rw [hLdet]; exact one_ne_zero
  obtain ⟨T,hT,hpoint⟩ := source_auxiliary_line4 A2 A3 L h2 h3 hLd (delta/24) (by positivity)
  refine ⟨T,hT,?_⟩
  intro q hq y hy
  exact hpoint q.val hq (hQU q.val q.property) c2 c3 (SourceWeights4.frameWidths F q)
    (F q).widths_pos (F q).w (F q).rational_independent (attaining_first_three4 (F q)) y hy

theorem same_frame_fixed_last_dual4
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1) (hd : 0 < delta)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q))
    (hU : ¬ BddAbove U) (S : Finset MixedIndex4)
    (hselected : ∀ q : U, publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
      (SourceWeights4.frameWidths F q) (fun i => c2 i/5) (fun i => c3 i/5) = S)
    (Tzero : ℝ) (hzero : ∀ q : U, Tzero < q.val → ∀ s ∈ S,
      lastDualProduct4 A2 A3 L (fun j => ((F q).w j : Fin 4 → ℤ)) (F q).rational_independent s = 0) :
    ∃ (q1 : U) (b : Fin 4 → ℤ) (B : ℝ), Tzero < q1.val ∧
      b = integerLastDual4 (fun j => ((F q1).w j : Fin 4 → ℤ)) ∧ b ≠ 0 ∧
      Submodule.span ℚ {fun i => (b i : ℚ)} =
        Submodule.span ℚ {lastDual4 (fun j i => (((F q1).w j : Fin 4 → ℤ) i : ℚ)) (F q1).rational_independent} ∧
      (∀ s ∈ S, mixedProduct4 A2 A3 L b s = 0) ∧
      1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ U ∧ B < q} ∧
      ∀ q : U, B < q.val →
        Submodule.span ℚ {lastDual4 (fun j i => (((F q).w j : Fin 4 → ℤ) i : ℚ)) (F q).rational_independent} =
          Submodule.span ℚ {fun i => (b i : ℚ)} := by
  obtain ⟨Tpoint,hTp,hpoint⟩ := same_deformed_auxiliary_line4 (A2 := A2) (A3 := A3) (L := L) (hL := hL) (c0 := c0) (c2 := c2) (c3 := c3) (delta := delta) (U := U) (hQU := hQU) (u := u) h2 h3 hLdet hd F
  obtain ⟨q1,hq1,hfar⟩ := not_bddAbove_iff.mp hU (max Tzero Tpoint)
  let r1 : U := ⟨q1,hq1⟩
  let b := integerLastDual4 (fun j => ((F r1).w j : Fin 4 → ℤ))
  have hb : b ≠ 0 := integerLastDual4_nonzero _ (F r1).rational_independent
  have hunit (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) :
      IsUnit (A.map (algebraMap ℚ ℚ_[p])) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [mapped_det_one4 A hA]
    exact isUnit_one
  have hT2 := finiteSupport_nonempty4 2 _ (hunit 2 A2 h2) b hb
  have hT3 := finiteSupport_nonempty4 3 _ (hunit 3 A3 h3) b hb
  have hb2 (i : Fin 4) : ‖dualValue4 (A2.map (algebraMap ℚ ℚ_[2])) b i‖ ≤ 1 :=
    cofactor_finite_unit4 2 A2 h2 _ _ (fun j => ((F r1).w j).property.1) i
  have hb3 (i : Fin 4) : ‖dualValue4 (A3.map (algebraMap ℚ ℚ_[3])) b i‖ ≤ 1 :=
    cofactor_finite_unit4 3 A3 h3 _ _ (fun j => ((F r1).w j).property.2) i
  have hzero1 := hzero r1 ((le_max_left _ _).trans_lt hfar)
  have hz : ∀ s ∈ S, mixedProduct4 A2 A3 L b s = 0 := by
    intro s hs
    exact (primitive_lastDualProduct4_zero A2 A3 L _ (F r1).rational_independent b 1
      one_ne_zero (fun i => by simp [b]) s).mpr (hzero1 s hs)
  obtain ⟨Treal,hTr,haux⟩ := rescaled_reference_auxiliary4 (A2 := A2) (A3 := A3) (L := L) (hL := hL) (c0 := c0) (c2 := c2) (c3 := c3) (delta := delta) (U := U) (hQU := hQU) (u := u) h2 h3 hd hc2 hc3 F S hselected b hT2 hT3 hb2 hb3 hz
  let B := max Tzero (max Tpoint Treal)
  have hpt : Tpoint ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hrt : Treal ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨r1,b,B,(le_max_left _ _).trans_lt hfar,rfl,hb,
    integerLastDual4_line _ (F r1).rational_independent,hz,hTr.trans_le hrt,
    JSP000334.sourceDual_unbounded_tail3 U hU B,?_⟩
  intro q hq
  let y := rescaledReference4 q.val c2 c3 _ _ hT2 hT3 b
  have hy := haux q (hrt.trans_lt hq)
  have hmem := (hpoint q (hpt.trans_lt hq) y hy).2
  have hyn : y ≠ 0 := integer_rescale_nonzero4 _ _ b hb
  have hyQ : (fun i => (y i : ℚ)) ≠ 0 := by
    intro he
    apply hyn
    funext i
    have hi : (y i : ℚ) = 0 := congrFun he i
    exact_mod_cast hi
  have heq := (nonzero_mem_line_span4 _ _ hyQ hmem).symm
  exact heq.trans (integer_rescale_line4 _ _ b)

theorem source_deformed_fixed_last_dual4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c0 c2 c3 : Fin 4 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ V),
      sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q (hQV q hq) c0 c2 c3 2 <
        sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q (hQV q hq) c0 c2 c3 3*q^(-delta)) :
    ∃ U : Set ℝ, ∃ hUV : U ⊆ V, ¬ BddAbove U ∧
      ∃ u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3,
      ∃ F : (q : U) → DeformedAttaining4 A2 A3 L (sourceUnit42 L hLdet) q.val
        (hQV q.val (hUV q.property)) c0 c2 c3 delta (u q),
      ∃ S : Finset OriginalSelectedSystem4.MixedIndex4, S.Nonempty ∧
      ∃ W : Set ℝ, ∃ hWU : W ⊆ U, ¬ BddAbove W ∧
        ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' W) ∧
        (∀ q : U, q.val ∈ W →
          OriginalSelectedSystem4.publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
            (OriginalDeformation4.deformedWidths4 q.val c0
              (OriginalDeformation4.gapDeformation4
                (sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q.val
                  (hQV q.val (hUV q.property)) c0 c2 c3)) (F q).sigma) (fun i => c2 i/5) (fun i => c3 i/5) = S) ∧
        ∃ (q1 : U) (b : Fin 4 → ℤ) (B : ℝ), q1.val ∈ W ∧
          b = integerLastDual4 (fun j => ((F q1).w j : Fin 4 → ℤ)) ∧ b ≠ 0 ∧
          Submodule.span ℚ {fun i => (b i : ℚ)} =
            Submodule.span ℚ {lastDual4 (fun j i => (((F q1).w j : Fin 4 → ℤ) i : ℚ)) (F q1).rational_independent} ∧
          (∀ s ∈ S, mixedProduct4 A2 A3 L b s = 0) ∧
          1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ W ∧ B < q} ∧
          ∀ q : U, q.val ∈ W → B < q.val →
            Submodule.span ℚ {lastDual4 (fun j i => (((F q).w j : Fin 4 → ℤ) i : ℚ)) (F q).rational_independent} =
              Submodule.span ℚ {fun i => (b i : ℚ)} := by
  obtain ⟨U,hUV,hU,u,F,S,hS,W,hWU,hW,hWp,hselected,Tzero,hzero⟩ :=
    SourceSelectedVanishing4.source_selected_vanishing4 A2 A3 L h2 h3 hLdet hAlg delta hd
      c0 c2 c3 hc0 hc2 hc3 hb V hV hQV hgap
  let lift : W → U := fun q => ⟨q.val,hWU q.property⟩
  obtain ⟨q1,b,B,hq1,hb,hbn,hline,hbz,hB,htail,hfixed⟩ := same_frame_fixed_last_dual4
    (A2 := A2) (A3 := A3) (L := L) (hL := sourceUnit42 L hLdet)
    (c0 := c0) (c2 := c2) (c3 := c3) (delta := delta) (U := W)
    (hQU := fun q hq => hQV q (hUV (hWU hq))) (u := fun q : W => u (lift q))
    h2 h3 hLdet hd (fun i => (hc2 i).2) (fun i => (hc3 i).2)
    (fun q : W => F (lift q)) hW S
    (fun q => hselected (lift q) q.property) Tzero
    (fun q hq s hs => hzero (lift q) q.property hq s hs)
  refine ⟨U,hUV,hU,u,F,S,hS,W,hWU,hW,hWp,hselected,lift q1,b,B,q1.property,
    hb,hbn,hline,hbz,hB,htail,?_⟩
  intro q hq hBq
  exact hfixed ⟨q.val,hq⟩ hBq

end CompoundFeasibility.SchlickeweiFixedLine4Literal179
end

#check CompoundFeasibility.SchlickeweiReference4Literal179.finiteSupport4
#print CompoundFeasibility.SchlickeweiReference4Literal179.finiteSupport4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.finiteSupport4
#check CompoundFeasibility.SchlickeweiReference4Literal179.finiteSupport_nonempty4
#print CompoundFeasibility.SchlickeweiReference4Literal179.finiteSupport_nonempty4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.finiteSupport_nonempty4
#check CompoundFeasibility.SchlickeweiReference4Literal179.publishedFloor4
#print CompoundFeasibility.SchlickeweiReference4Literal179.publishedFloor4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.publishedFloor4
#check CompoundFeasibility.SchlickeweiReference4Literal179.supportFloor4
#print CompoundFeasibility.SchlickeweiReference4Literal179.supportFloor4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.supportFloor4
#check CompoundFeasibility.SchlickeweiReference4Literal179.support_floor_spec4
#print CompoundFeasibility.SchlickeweiReference4Literal179.support_floor_spec4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.support_floor_spec4
#check CompoundFeasibility.SchlickeweiReference4Literal179.three_floor_error4
#print CompoundFeasibility.SchlickeweiReference4Literal179.three_floor_error4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.three_floor_error4
#check CompoundFeasibility.SchlickeweiReference4Literal179.three_floor_natceil_error4
#print CompoundFeasibility.SchlickeweiReference4Literal179.three_floor_natceil_error4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.three_floor_natceil_error4
#check CompoundFeasibility.SchlickeweiReference4Literal179.published_floor_nonpos4
#print CompoundFeasibility.SchlickeweiReference4Literal179.published_floor_nonpos4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.published_floor_nonpos4
#check CompoundFeasibility.SchlickeweiReference4Literal179.support_floor_nonpos4
#print CompoundFeasibility.SchlickeweiReference4Literal179.support_floor_nonpos4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.support_floor_nonpos4
#check CompoundFeasibility.SchlickeweiReference4Literal179.rescaleMultiplier4
#print CompoundFeasibility.SchlickeweiReference4Literal179.rescaleMultiplier4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.rescaleMultiplier4
#check CompoundFeasibility.SchlickeweiReference4Literal179.integerRescale4
#print CompoundFeasibility.SchlickeweiReference4Literal179.integerRescale4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.integerRescale4
#check CompoundFeasibility.SchlickeweiReference4Literal179.rescale_multiplier_pos4
#print CompoundFeasibility.SchlickeweiReference4Literal179.rescale_multiplier_pos4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.rescale_multiplier_pos4
#check CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_nonzero4
#print CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_nonzero4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_nonzero4
#check CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_line4
#print CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_line4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_line4
#check CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_published4
#print CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_published4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_published4
#check CompoundFeasibility.SchlickeweiReference4Literal179.rescale_multiplier_factor4
#print CompoundFeasibility.SchlickeweiReference4Literal179.rescale_multiplier_factor4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.rescale_multiplier_factor4
#check CompoundFeasibility.SchlickeweiReference4Literal179.rescale_p2_norm4
#print CompoundFeasibility.SchlickeweiReference4Literal179.rescale_p2_norm4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.rescale_p2_norm4
#check CompoundFeasibility.SchlickeweiReference4Literal179.rescale_p3_norm4
#print CompoundFeasibility.SchlickeweiReference4Literal179.rescale_p3_norm4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.rescale_p3_norm4
#check CompoundFeasibility.SchlickeweiReference4Literal179.floor_rounded_exponents4
#print CompoundFeasibility.SchlickeweiReference4Literal179.floor_rounded_exponents4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.floor_rounded_exponents4
#check CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_dual_norm4
#print CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_dual_norm4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_dual_norm4
#check CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_finite_bound4
#print CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_finite_bound4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.integer_rescale_finite_bound4
#check CompoundFeasibility.SchlickeweiReference4Literal179.floor_growth4
#print CompoundFeasibility.SchlickeweiReference4Literal179.floor_growth4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.floor_growth4
#check CompoundFeasibility.SchlickeweiReference4Literal179.omitted_balance_gap4
#print CompoundFeasibility.SchlickeweiReference4Literal179.omitted_balance_gap4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.omitted_balance_gap4
#check CompoundFeasibility.SchlickeweiReference4Literal179.power_covolume4
#print CompoundFeasibility.SchlickeweiReference4Literal179.power_covolume4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.power_covolume4
#check CompoundFeasibility.SchlickeweiReference4Literal179.reference_real_coordinate4
#print CompoundFeasibility.SchlickeweiReference4Literal179.reference_real_coordinate4
#print axioms CompoundFeasibility.SchlickeweiReference4Literal179.reference_real_coordinate4
#check CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.sourceExponent4
#print CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.sourceExponent4
#print axioms CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.sourceExponent4
#check CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.source_exponent_rescaling4
#print CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.source_exponent_rescaling4
#print axioms CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.source_exponent_rescaling4
#check CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.sourceFloor4
#print CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.sourceFloor4
#print axioms CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.sourceFloor4
#check CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.rescaledReference4
#print CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.rescaledReference4
#print axioms CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.rescaledReference4
#check CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.source_floor_nonpos4
#print CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.source_floor_nonpos4
#print axioms CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.source_floor_nonpos4
#check CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.source_floor_rounded4
#print CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.source_floor_rounded4
#print axioms CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.source_floor_rounded4
#check CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.rescaled_reference_finite4
#print CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.rescaled_reference_finite4
#print axioms CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.rescaled_reference_finite4
#check CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.multiplier_real_growth4
#print CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.multiplier_real_growth4
#print axioms CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.multiplier_real_growth4
#check CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.referenceRealConstant4
#print CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.referenceRealConstant4
#print axioms CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.referenceRealConstant4
#check CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.reference_real_constant_pos4
#print CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.reference_real_constant_pos4
#print axioms CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.reference_real_constant_pos4
#check CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.reference_real_constant_bound4
#print CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.reference_real_constant_bound4
#print axioms CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.reference_real_constant_bound4
#check CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.rescaled_reference_real_decay4
#print CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.rescaled_reference_real_decay4
#print axioms CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.rescaled_reference_real_decay4
#check CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.reference_decay_cutoff4
#print CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.reference_decay_cutoff4
#print axioms CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.reference_decay_cutoff4
#check CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.rescaled_reference_auxiliary4
#print CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.rescaled_reference_auxiliary4
#print axioms CompoundFeasibility.SchlickeweiReferenceRescaling4Literal179.rescaled_reference_auxiliary4
#check CompoundFeasibility.SchlickeweiFixedLine4Literal179.cofactor_finite_unit4
#print CompoundFeasibility.SchlickeweiFixedLine4Literal179.cofactor_finite_unit4
#print axioms CompoundFeasibility.SchlickeweiFixedLine4Literal179.cofactor_finite_unit4
#check CompoundFeasibility.SchlickeweiFixedLine4Literal179.nonzero_mem_line_span4
#print CompoundFeasibility.SchlickeweiFixedLine4Literal179.nonzero_mem_line_span4
#print axioms CompoundFeasibility.SchlickeweiFixedLine4Literal179.nonzero_mem_line_span4
#check CompoundFeasibility.SchlickeweiFixedLine4Literal179.same_deformed_auxiliary_line4
#print CompoundFeasibility.SchlickeweiFixedLine4Literal179.same_deformed_auxiliary_line4
#print axioms CompoundFeasibility.SchlickeweiFixedLine4Literal179.same_deformed_auxiliary_line4
#check CompoundFeasibility.SchlickeweiFixedLine4Literal179.same_frame_fixed_last_dual4
#print CompoundFeasibility.SchlickeweiFixedLine4Literal179.same_frame_fixed_last_dual4
#print axioms CompoundFeasibility.SchlickeweiFixedLine4Literal179.same_frame_fixed_last_dual4
#check CompoundFeasibility.SchlickeweiFixedLine4Literal179.source_deformed_fixed_last_dual4
#print CompoundFeasibility.SchlickeweiFixedLine4Literal179.source_deformed_fixed_last_dual4
#print axioms CompoundFeasibility.SchlickeweiFixedLine4Literal179.source_deformed_fixed_last_dual4
