import SubspaceBridge.SourceExterior54Packet246F
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior54_246

theorem real_wedge_bound4246 (y : Fin 4 → Fin 5 → ℝ) (r : Fin 4 → ℝ)
    (t : Fin 5 → ℝ) (hy : ∀ j k, |y j k| ≤ r j * t k) (i : Fin 5) :
    |wedge4246 y i| ≤ 24 * (∏ j, r j) * (∏ k : Fin 4, t (i.succAbove k)) := by
  let M : Matrix (Fin 5) (Fin 5) ℝ := Matrix.of (Fin.snoc y (0 : Fin 5 → ℝ))
  change |M.adjugate i (Fin.last 4)| ≤ _
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, abs_mul, abs_pow, abs_neg, abs_one]
  simp only [one_pow, one_mul]
  have h := OriginalDual10.det_row_column_bounds10
    (M.submatrix (Fin.last 4).succAbove i.succAbove) r (fun k => t (i.succAbove k))
    (by
      intro j k
      simpa only [Matrix.submatrix_apply, Fin.succAbove_last, M, Matrix.of_apply,
        Fin.snoc_castSucc] using hy j (i.succAbove k))
  simpa only [show (Nat.factorial 4 : ℝ) = 24 by norm_num [Nat.factorial]] using h

theorem real_source_wedge4246 (L : Matrix (Fin 5) (Fin 5) ℝ)
    (x : Fin 4 → Fin 5 → ℤ) (r : Fin 4 → ℝ) (Q : ℝ) (hQ : 1 < Q)
    (c0 : Fin 5 → ℝ)
    (hx : ∀ j k, |(L *ᵥ integerReal (x j)) k| ≤ r j * Q^(c0 k)) (i : Fin 5) :
    |(compound4246 L *ᵥ integerReal (wedge4246 x)) i| ≤
      24 * (∏ j, r j) * Q^(fourWeights246 c0 i) := by
  have he : integerReal (wedge4246 x) = wedge4246 (fun j => integerReal (x j)) :=
    wedge_map4246 (Int.castRingHom ℝ) x
  rw [he, wedge_transform4246]
  have h := real_wedge_bound4246 (fun j => L *ᵥ integerReal (x j)) r
    (fun k => Q^(c0 k)) hx i
  have hp : (∏ k : Fin 4, Q^(c0 (i.succAbove k))) = Q^(fourWeights246 c0 i) := by
    rw [← Real.rpow_sum_of_pos (zero_lt_one.trans hQ)]
    rfl
  rw [hp] at h
  exact h

end CompoundFeasibility.Exterior54_246
