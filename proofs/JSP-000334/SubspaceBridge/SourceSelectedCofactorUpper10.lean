import SubspaceBridge.SourceSelectedCanonical10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSelectedUpper10
open OriginalDual10 SourceSelectedSet10 SchmidtNormal10 SourceHeightEnvelope10

theorem original_cofactor_mixed_power10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (q epsilon : ℝ) (hq : 1 < q) (c2 c3 : Fin 10 → ℝ)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (c : Fin 3 → Fin 10 → ℝ) (hb : (∑ tau, ∑ i, c tau i) = 0)
    (hc : ∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5)
    (w : Fin 10 → Fin 10 → ℤ)
    (hw : ∀ j, w j ∈ originalSourceGroup10 A2 A3 q c2 c3)
    (hreal : ∀ (j : Fin 9) i, ‖(L *ᵥ integerReal (w j.castSucc)) i‖ ≤ (q^5)^(c 0 i-epsilon))
    (s : MixedIndex10) :
    mixedProduct10 A2 A3 L (integerLastDual10 w) s ≤
      362880*(q^5)^(-9*epsilon-(∑ tau, c tau (s tau))) := by
  have hQ : 0 < q^5 := pow_pos (zero_lt_one.trans hq) _
  have h0 := real_cofactor_fin10 L hL w (fun _ => 1)
    (fun i => (q^5)^(c 0 i-epsilon))
    (fun j i => by simpa only [Real.norm_eq_abs,one_mul] using hreal j i) (s 0)
  simp only [Finset.prod_const_one,mul_one] at h0
  rw [real_dual_cast_norm10] at h0
  have hp2 := finite_cofactor_rescaled10 2 (by decide) A2 h2 q hq c2 hc2 w
    (fun j => (hw j).1) (s 1)
  have hp3 := finite_cofactor_rescaled10 3 (by decide) A3 h3 q hq c3 hc3 w
    (fun j => (hw j).2) (s 2)
  have hcf2 : c 1 = fun i => c2 i/5 := funext (fun i => (hc i).1)
  have hcf3 : c 2 = fun i => c3 i/5 := funext (fun i => (hc i).2)
  rw [finite_dual_norm_canonical10 2 A2 h2] at hp2
  rw [finite_dual_norm_canonical10 3 A3 h3] at hp3
  have hp2' : ‖finiteValue10 2 A2.adjugate.transpose (integerLastDual10 w) (s 1)‖ ≤
      ∏ k : Fin 9, (q^5)^(c 1 ((s 1).succAbove k)) := by
    simpa only [hcf2] using hp2
  have hp3' : ‖finiteValue10 3 A3.adjugate.transpose (integerLastDual10 w) (s 2)‖ ≤
      ∏ k : Fin 9, (q^5)^(c 2 ((s 2).succAbove k)) := by
    simpa only [hcf3] using hp3
  calc
    _ ≤ (362880*∏ k : Fin 9, (q^5)^(c 0 ((s 0).succAbove k)-epsilon))*
        (∏ k : Fin 9, (q^5)^(c 1 ((s 1).succAbove k)))*
        (∏ k : Fin 9, (q^5)^(c 2 ((s 2).succAbove k))) :=
      mixedProduct10_le_canonical_bounds A2 A3 L h2 h3 (integerLastDual10 w) s _ _ _ h0 hp2' hp3'
    _ = _ := mixed_power_product10 (q^5) epsilon hQ c hb s

theorem selected_power_margin10 (Q epsilon : ℝ) (hQ : 1 < Q) (he : 0 < epsilon)
    (c : Fin 3 → Fin 10 → ℝ) (hc2 : ∀ i, c 1 i ≤ 0) (hc3 : ∀ i, c 2 i ≤ 0)
    (s : MixedIndex10)
    (hs : s ∈ roundedSelector10 Q (epsilon/2) (fun i => Q^(c 0 i)) (c 1) (c 2)) :
    -(3*(epsilon/2))/4 ≤ ∑ tau, c tau (s tau) := by
  apply rounded_to_power_margin10 Q (epsilon/2) hQ _ _ _
    (fun i => Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _) hc2 hc3 c _
    (fun _ => le_rfl) (fun _ => le_rfl) s hs
  intro i
  have hlog : Real.log (Q^(c 0 i))/Real.log Q = c 0 i := by
    rw [Real.log_rpow (zero_lt_one.trans hQ)]
    exact mul_div_cancel_right₀ _ (Real.log_pos hQ).ne'
  rw [hlog]
  linarith

theorem original_cofactor_selected_upper10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (q epsilon : ℝ) (hq : 1 < q) (he : 0 < epsilon) (c2 c3 : Fin 10 → ℝ)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (c : Fin 3 → Fin 10 → ℝ) (hb : (∑ tau, ∑ i, c tau i) = 0)
    (hc : ∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5)
    (w : Fin 10 → Fin 10 → ℤ)
    (hw : ∀ j, w j ∈ originalSourceGroup10 A2 A3 q c2 c3)
    (hreal : ∀ (j : Fin 9) i, ‖(L *ᵥ integerReal (w j.castSucc)) i‖ ≤ (q^5)^(c 0 i-epsilon))
    (s : MixedIndex10)
    (hs : s ∈ roundedSelector10 (q^5) (epsilon/2) (fun i => (q^5)^(c 0 i)) (c 1) (c 2)) :
    mixedProduct10 A2 A3 L (integerLastDual10 w) s ≤
      362880*(q^5)^(-(epsilon/2)/4) := by
  have hQ : 1 < q^5 := one_lt_pow₀ hq (by decide)
  have hsign2 (i) : c 1 i ≤ 0 := by rw [(hc i).1]; exact div_nonpos_of_nonpos_of_nonneg (hc2 i) (by norm_num)
  have hsign3 (i) : c 2 i ≤ 0 := by rw [(hc i).2]; exact div_nonpos_of_nonpos_of_nonneg (hc3 i) (by norm_num)
  have hm := selected_power_margin10 (q^5) epsilon hQ he c hsign2 hsign3 s hs
  apply (original_cofactor_mixed_power10 A2 A3 L h2 h3 hL q epsilon hq c2 c3 hc2 hc3 c hb hc w hw hreal s).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 362880)
  exact Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith)

end CompoundFeasibility.SourceSelectedUpper10
