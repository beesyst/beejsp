import SubspaceBridge.SourceOriginalAuxiliaryFamily10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSelectedSet10

abbrev MixedIndex10 := Fin 3 → Fin 10

def roundedRadius10 (p : ℕ) (Q c : ℝ) : ℝ :=
  ((p : ℝ)^Nat.ceil (JSP000334.qThreshold p Q c))⁻¹

def roundedSelector10 (Q delta : ℝ) (A c2 c3 : Fin 10 → ℝ) : Finset MixedIndex10 :=
  Finset.univ.filter (fun s => 1 ≤ A (s 0)*roundedRadius10 2 Q (c2 (s 1))*
    roundedRadius10 3 Q (c3 (s 2))*Q^(delta/2))

def roundedWeights10 (Q : ℝ) (A c2 c3 : Fin 10 → ℝ) : Fin 3 → Fin 10 → ℝ :=
  ![fun i => Real.log (A i)/Real.log Q,
    fun i => Real.log (roundedRadius10 2 Q (c2 i))/Real.log Q,
    fun i => Real.log (roundedRadius10 3 Q (c3 i))/Real.log Q]

theorem roundedRadius10_pos (p : ℕ) (hp : 1 < p) (Q c : ℝ) :
    0 < roundedRadius10 p Q c := by
  unfold roundedRadius10
  positivity

theorem roundedRadius10_bounds (p : ℕ) (hp : 1 < p) (Q c : ℝ)
    (hQ : 1 < Q) (hc : c ≤ 0) :
    Q^c/(p : ℝ) < roundedRadius10 p Q c ∧ roundedRadius10 p Q c ≤ Q^c := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hpR
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  have ht := JSP000334.qThreshold_nonneg p hp Q c hQ hc
  have hf := JSP000334.ceilingFactor_bounds (p : ℝ) _ hpR ht
  have he : roundedRadius10 p Q c = Q^c /
      JSP000334.ceilingFactor p (JSP000334.qThreshold p Q c) := by
    unfold roundedRadius10
    rw [JSP000334.pow_ceil_factorization _ _ hp0,JSP000334.qThreshold_rpow p hp Q c hQ]
    rw [mul_inv,Real.rpow_neg hQ0.le]
    simp only [inv_inv,div_eq_mul_inv]
  rw [he]
  exact ⟨div_lt_div_of_pos_left (Real.rpow_pos_of_pos hQ0 _) (by linarith) hf.2,
    (div_le_iff₀ (by linarith : 0 < JSP000334.ceilingFactor p (JSP000334.qThreshold p Q c))).mpr
      (by nlinarith [Real.rpow_pos_of_pos hQ0 c])⟩

theorem roundedSelector10_iff (Q delta : ℝ) (hQ : 1 < Q)
    (A c2 c3 : Fin 10 → ℝ) (hA : ∀ i, 0 < A i) (s : MixedIndex10) :
    s ∈ roundedSelector10 Q delta A c2 c3 ↔
      -delta/2 ≤ ∑ tau, roundedWeights10 Q A c2 c3 tau (s tau) := by
  have h2 := roundedRadius10_pos 2 (by decide) Q (c2 (s 1))
  have h3 := roundedRadius10_pos 3 (by decide) Q (c3 (s 2))
  have hpow := Real.rpow_pos_of_pos (zero_lt_one.trans hQ) (delta/2)
  have hlog : 1 ≤ A (s 0)*roundedRadius10 2 Q (c2 (s 1))*
      roundedRadius10 3 Q (c3 (s 2))*Q^(delta/2) ↔
      0 ≤ Real.log (A (s 0))+Real.log (roundedRadius10 2 Q (c2 (s 1)))+
        Real.log (roundedRadius10 3 Q (c3 (s 2)))+(delta/2)*Real.log Q := by
    rw [← Real.log_le_log_iff (by norm_num : (0 : ℝ) < 1)
      (mul_pos (mul_pos (mul_pos (hA _) h2) h3) hpow),Real.log_one,
      Real.log_mul (mul_pos (mul_pos (hA _) h2) h3).ne' hpow.ne',
      Real.log_mul (mul_pos (hA _) h2).ne' h3.ne',Real.log_mul (hA _).ne' h2.ne',
      Real.log_rpow (zero_lt_one.trans hQ)]
  simp only [roundedSelector10,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [hlog]
  simp only [roundedWeights10,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_zero,← add_div]
  rw [le_div_iff₀ (Real.log_pos hQ)]
  constructor <;> intro h <;> linarith

theorem balanced_mixed_nonnegative10 (c : Fin 3 → Fin 10 → ℝ)
    (hb : (∑ tau, ∑ i, c tau i) = 0) :
    ∃ s : MixedIndex10, 0 ≤ ∑ tau, c tau (s tau) := by
  have hm (tau : Fin 3) : ∃ i : Fin 10, ∀ j, c tau j ≤ c tau i := by
    obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (c tau) Finset.univ_nonempty
    exact ⟨i,fun j => hi j (Finset.mem_univ j)⟩
  choose s hs using hm
  refine ⟨s,?_⟩
  have hrow (tau : Fin 3) : (∑ i, c tau i) ≤ 10*c tau (s tau) := by
    calc
      _ ≤ ∑ _i : Fin 10, c tau (s tau) := Finset.sum_le_sum (fun j _ => hs tau j)
      _ = _ := by simp
  have h := Finset.sum_le_sum (fun tau (_ : tau ∈ Finset.univ) => hrow tau)
  rw [hb,← Finset.mul_sum] at h
  linarith

theorem roundedSelector10_nonempty (Q delta : ℝ) (hQ : 1 < Q) (hd : 0 < delta)
    (A c2 c3 : Fin 10 → ℝ) (hA : ∀ i, 0 < A i)
    (hb : (∏ i, A i)*(∏ i, roundedRadius10 2 Q (c2 i)*roundedRadius10 3 Q (c3 i)) = 1) :
    (roundedSelector10 Q delta A c2 c3).Nonempty := by
  have h2 (i) := roundedRadius10_pos 2 (by decide) Q (c2 i)
  have h3 (i) := roundedRadius10_pos 3 (by decide) Q (c3 i)
  have hlog := congrArg Real.log hb
  rw [Real.log_mul (Finset.prod_pos (fun i _ => hA i)).ne'
    (Finset.prod_pos (fun i _ => mul_pos (h2 i) (h3 i))).ne',
    Real.log_prod Finset.univ A (fun i _ => (hA i).ne'),
    Real.log_prod Finset.univ _ (fun i _ => (mul_pos (h2 i) (h3 i)).ne'),Real.log_one] at hlog
  simp_rw [Real.log_mul (h2 _).ne' (h3 _).ne'] at hlog
  have hbalance : (∑ tau, ∑ i, roundedWeights10 Q A c2 c3 tau i) = 0 := by
    simp only [roundedWeights10,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_zero,← Finset.sum_div,← add_div]
    apply (div_eq_zero_iff).mpr
    left
    simpa only [Finset.sum_add_distrib,add_assoc] using hlog
  obtain ⟨s,hs⟩ := balanced_mixed_nonnegative10 _ hbalance
  exact ⟨s,(roundedSelector10_iff Q delta hQ A c2 c3 hA s).mpr (by linarith)⟩

theorem rounded_to_power_margin10 (Q delta : ℝ) (hQ : 1 < Q)
    (A c2 c3 : Fin 10 → ℝ) (hA : ∀ i, 0 < A i)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (d : Fin 3 → Fin 10 → ℝ)
    (hd0 : ∀ i, Real.log (A i)/Real.log Q-delta/4 ≤ d 0 i)
    (hd2 : ∀ i, c2 i ≤ d 1 i) (hd3 : ∀ i, c3 i ≤ d 2 i)
    (s : MixedIndex10) (hs : s ∈ roundedSelector10 Q delta A c2 c3) :
    -(3*delta)/4 ≤ ∑ tau, d tau (s tau) := by
  have hlog2 := Real.log_le_log (roundedRadius10_pos 2 (by decide) Q (c2 (s 1)))
    (roundedRadius10_bounds 2 (by decide) Q _ hQ (hc2 _)).2
  have hlog3 := Real.log_le_log (roundedRadius10_pos 3 (by decide) Q (c3 (s 2)))
    (roundedRadius10_bounds 3 (by decide) Q _ hQ (hc3 _)).2
  rw [Real.log_rpow (zero_lt_one.trans hQ)] at hlog2 hlog3
  have h2 : Real.log (roundedRadius10 2 Q (c2 (s 1)))/Real.log Q ≤ c2 (s 1) :=
    (div_le_iff₀ (Real.log_pos hQ)).mpr (by nlinarith [Real.log_pos hQ])
  have h3 : Real.log (roundedRadius10 3 Q (c3 (s 2)))/Real.log Q ≤ c3 (s 2) :=
    (div_le_iff₀ (Real.log_pos hQ)).mpr (by nlinarith [Real.log_pos hQ])
  have hs' := (roundedSelector10_iff Q delta hQ A c2 c3 hA s).mp hs
  simp only [roundedWeights10,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_zero] at hs'
  rw [Fin.sum_univ_three]
  linarith [hd0 (s 0),hd2 (s 1),hd3 (s 2)]


theorem rounded_power_selector_nonempty10 (Q delta : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 10 → ℝ)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0) (hlarge : 6 ≤ Q^(delta/2)) :
    (roundedSelector10 Q delta (fun i => Q^(c0 i)) c2 c3).Nonempty := by
  have hbalance : (∑ tau, ∑ i, (![c0,c2,c3] : Fin 3 → Fin 10 → ℝ) tau i) = 0 := by
    simpa only [Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Finset.sum_add_distrib,add_assoc] using hb
  obtain ⟨s,hs⟩ := balanced_mixed_nonnegative10 _ hbalance
  have hs' : 0 ≤ c0 (s 0)+c2 (s 1)+c3 (s 2) := by
    simpa only [Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hs
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  have h0 := Real.rpow_pos_of_pos hQ0 (c0 (s 0))
  have h2 := Real.rpow_pos_of_pos hQ0 (c2 (s 1))
  have h3 := Real.rpow_pos_of_pos hQ0 (c3 (s 2))
  have hr2 := roundedRadius10_pos 2 (by decide) Q (c2 (s 1))
  have hr3 := roundedRadius10_pos 3 (by decide) Q (c3 (s 2))
  have hb2 := (roundedRadius10_bounds 2 (by decide) Q (c2 (s 1)) hQ (hc2 (s 1))).1
  have hb3 := (roundedRadius10_bounds 3 (by decide) Q (c3 (s 2)) hQ (hc3 (s 2))).1
  have hprod : 1 ≤ Q^(c0 (s 0))*Q^(c2 (s 1))*Q^(c3 (s 2)) := by
    rw [← Real.rpow_add hQ0,← Real.rpow_add hQ0]
    exact Real.one_le_rpow hQ.le hs'
  have hl : (1 : ℝ)/6 < Q^(c0 (s 0))*roundedRadius10 2 Q (c2 (s 1))*
      roundedRadius10 3 Q (c3 (s 2)) := by
    have hmul := mul_lt_mul hb2 hb3.le (by positivity : 0 < Q^(c3 (s 2))/3) hr2.le
    have ht := mul_lt_mul_of_pos_left hmul h0
    nlinarith
  refine ⟨s,?_⟩
  simp only [roundedSelector10,Finset.mem_filter,Finset.mem_univ,true_and]
  have hp : 0 < Q^(c0 (s 0))*roundedRadius10 2 Q (c2 (s 1))*roundedRadius10 3 Q (c3 (s 2)) :=
    mul_pos (mul_pos h0 hr2) hr3
  nlinarith

end CompoundFeasibility.SourceSelectedSet10
