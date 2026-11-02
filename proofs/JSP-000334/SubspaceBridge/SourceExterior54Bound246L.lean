import SubspaceBridge.SourceExterior54Map246L
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior54_246

theorem padic_wedge_bound4246 (p : ℕ) [Fact p.Prime]
    (y : Fin 4 → Fin 5 → ℚ_[p]) (b : Fin 5 → ℝ)
    (hb : ∀ k, 0 ≤ b k) (hy : ∀ j k, ‖y j k‖ ≤ b k) (i : Fin 5) :
    ‖wedge4246 y i‖ ≤ ∏ k : Fin 4, b (i.succAbove k) := by
  let M : Matrix (Fin 5) (Fin 5) ℚ_[p] := Matrix.of (Fin.snoc y (0 : Fin 5 → ℚ_[p]))
  change ‖M.adjugate i (Fin.last 4)‖ ≤ _
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, norm_mul, norm_pow, norm_neg, norm_one]
  simp only [one_pow, one_mul]
  apply OriginalDual10.padic_det3_bound10 (n := 4) p _ _ (fun k => hb (i.succAbove k))
  intro j k
  simpa only [Matrix.submatrix_apply, Fin.succAbove_last, M, Matrix.of_apply,
    Fin.snoc_castSucc] using hy j (i.succAbove k)

end CompoundFeasibility.Exterior54_246
