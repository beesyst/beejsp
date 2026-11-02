import SubspaceBridge.SchlickeweiReference4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiReferenceRescaling4
open SchlickeweiReference4 SourceSelectedDual4 OriginalSelectedSystem4 OriginalDeformedSource4

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

end CompoundFeasibility.SchlickeweiReferenceRescaling4
