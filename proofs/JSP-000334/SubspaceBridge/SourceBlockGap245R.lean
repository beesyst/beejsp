import SubspaceBridge.SourceBlockUpper245R
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.BlockReduction245R
open BlockReduction245P BlockReduction245Q Exterior53_242

theorem source_block_gap245R (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 5 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ 0 < delta/3 ∧ ∀ (Q : ℝ) (hQ : 1 < Q), T < Q →
      sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3 <
        sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 4*Q^(-delta) →
      sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
        (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0) (weightp245P c2) (weightp245P c3) 8 <
      sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
        (Q^3) (powered_gt_one3242 Q hQ) (weight0245P c0) (weightp245P c2) (weightp245P c3) 9*
          (Q^3)^(-delta/3) := by
  obtain ⟨T,hT,hcomp⟩ := source_comparisons245R L hL
  refine ⟨T,hT,by positivity,?_⟩
  intro Q hQ hTQ hgap
  obtain ⟨hupper,hlower⟩ := hcomp A2 A3 Q hQ c0 c2 c3 hc0 hTQ
  have hq := zero_lt_one.trans hQ
  have hp : (Q^3)^(-delta/3) = Q^(-delta) := by
    simpa only [add_zero] using powered_rpow3242 Q (-delta) 0 0 hQ
  rw [hp]
  calc
    _ ≤ Q^2*sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3 := hupper
    _ < Q^2*(sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 4*Q^(-delta)) :=
      mul_lt_mul_of_pos_left hgap (sq_pos_of_pos hq)
    _ = (Q^2*sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 4)*Q^(-delta) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hlower (Real.rpow_pos_of_pos hq _).le

end CompoundFeasibility.BlockReduction245R
