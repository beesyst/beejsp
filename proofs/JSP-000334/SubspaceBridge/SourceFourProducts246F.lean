import SubspaceBridge.SourceExterior54Packet246F
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior54_246

def fourProducts246 (a : Fin 5 → ℝ) (j : Fin 5) : ℝ :=
  ∏ k : Fin 4, a (j.rev.succAbove k)

theorem fourProducts_pos246 (a : Fin 5 → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ j, 0 < fourProducts246 a j := fun _ => Finset.prod_pos (fun _ _ => ha _)

theorem fourProducts_mono246 (a : Fin 5 → ℝ) (ha : ∀ i, 0 < a i) (hm : Monotone a) :
    Monotone (fourProducts246 a) := by
  have hi : ∀ j k : Fin 5, j ≤ k → ∀ t : Fin 4, j.rev.succAbove t ≤ k.rev.succAbove t := by decide
  intro j k hjk
  exact Finset.prod_le_prod (fun t _ => (ha _).le) (fun t _ => hm (hi j k hjk t))

theorem fourProducts_values246 (a : Fin 5 → ℝ) :
    fourProducts246 a 0 = a 0*a 1*a 2*a 3 ∧
    fourProducts246 a 1 = a 0*a 1*a 2*a 4 ∧
    fourProducts246 a 2 = a 0*a 1*a 3*a 4 ∧
    fourProducts246 a 3 = a 0*a 2*a 3*a 4 ∧
    fourProducts246 a 4 = a 1*a 2*a 3*a 4 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals simp only [fourProducts246, Fin.prod_univ_succ, Fin.prod_univ_zero]
  · change a 0 * (a 1 * (a 2 * (a 3 * 1))) = _
    ring
  · change a 0 * (a 1 * (a 2 * (a 4 * 1))) = _
    ring
  · change a 0 * (a 1 * (a 3 * (a 4 * 1))) = _
    ring
  · change a 0 * (a 2 * (a 3 * (a 4 * 1))) = _
    ring
  · change a 1 * (a 2 * (a 3 * (a 4 * 1))) = _
    ring

theorem fourProducts_product246 (a : Fin 5 → ℝ) :
    (∏ j, fourProducts246 a j) = (∏ i, a i)^4 := by
  simp [fourProducts246, Fin.prod_univ_succ, Fin.rev, Fin.succAbove]
  ring

theorem fourProducts_gap246 (a : Fin 5 → ℝ) (ha : ∀ i, 0 < a i)
    (Q delta : ℝ) (hg : a 0 < a 1 * Q^(-delta)) :
    fourProducts246 a 3 < fourProducts246 a 4 * Q^(-delta) := by
  obtain ⟨_,_,_,h3,h4⟩ := fourProducts_values246 a
  rw [h3,h4]
  convert mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_right hg (ha 2)) (ha 3)) (ha 4) using 1 <;> ring

end CompoundFeasibility.Exterior54_246
