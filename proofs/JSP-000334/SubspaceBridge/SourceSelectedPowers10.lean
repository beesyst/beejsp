import SubspaceBridge.SourceSelectedCofactor10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSelectedUpper10
open OriginalDual10 SourceSelectedSet10 SchmidtNormal10

theorem mixed_exponent_cancel10 (c : Fin 3 → Fin 10 → ℝ) (epsilon : ℝ)
    (hb : (∑ tau, ∑ i, c tau i) = 0) (s : MixedIndex10) :
    (∑ k : Fin 9, (c 0 ((s 0).succAbove k)-epsilon)) +
      (∑ k : Fin 9, c 1 ((s 1).succAbove k)) +
      (∑ k : Fin 9, c 2 ((s 2).succAbove k)) =
      -9*epsilon-(∑ tau, c tau (s tau)) := by
  have h0 := Fin.sum_univ_succAbove (c 0) (s 0)
  have h1 := Fin.sum_univ_succAbove (c 1) (s 1)
  have h2 := Fin.sum_univ_succAbove (c 2) (s 2)
  have hb' : (∑ i, c 0 i)+(∑ i, c 1 i)+(∑ i, c 2 i) = 0 := by
    simpa only [Fin.sum_univ_three] using hb
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Fin.sum_univ_three]
  norm_num only [Nat.cast_ofNat]
  linarith

theorem mixed_power_product10 (Q epsilon : ℝ) (hQ : 0 < Q)
    (c : Fin 3 → Fin 10 → ℝ) (hb : (∑ tau, ∑ i, c tau i) = 0) (s : MixedIndex10) :
    (362880*∏ k : Fin 9, Q^(c 0 ((s 0).succAbove k)-epsilon))*
      (∏ k : Fin 9, Q^(c 1 ((s 1).succAbove k)))*
      (∏ k : Fin 9, Q^(c 2 ((s 2).succAbove k))) =
      362880*Q^(-9*epsilon-(∑ tau, c tau (s tau))) := by
  simp only [← Real.rpow_sum_of_pos hQ]
  rw [← mixed_exponent_cancel10 c epsilon hb s,Real.rpow_add hQ,Real.rpow_add hQ]
  ring

theorem real_dual_cast_norm10 {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (M : Fin n → ℤ) (i : Fin n) :
    ‖(B *ᵥ (fun k => (M k : ℝ))) i‖ = |(B *ᵥ integerReal M) i| := by
  rw [Real.norm_eq_abs]
  rfl

end CompoundFeasibility.SourceSelectedUpper10
