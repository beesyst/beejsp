import SubspaceBridge.SchlickeweiDualVanishing6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiEquation4126
open SchlickeweiDualVanishing6 SourceMixed6 SourceReadiness6 SourceNormalHeight SourceNormalIndex
open Auxiliary6.SourceExpansion Auxiliary6.SourceBalance
theorem scalar_product_zero_transport (x0 x2 x3 y0 y2 y3 : ℝ)
    (h0 : x0 = 0 ↔ y0 = 0) (h2 : x2 = 0 ↔ y2 = 0) (h3 : x3 = 0 ↔ y3 = 0)
    (hx : x0 * x2 * x3 = 0) : y0 * y2 * y3 = 0 := by
  rcases mul_eq_zero.mp hx with hx02 | hx3
  · rcases mul_eq_zero.mp hx02 with hx0 | hx2
    · rw [h0.mp hx0, zero_mul, zero_mul]
    · rw [h2.mp hx2, mul_zero, zero_mul]
  · rw [h3.mp hx3, mul_zero]

def publishedDualProduct6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (D : Fin 6 → ℚ) (s : MixedIndex6) : ℝ :=
  ‖dualFormValue6 (compound L) D (s 0)‖ *
  ‖dualFormValue6 (finiteMatrix 2 A2) D (s 1)‖ *
  ‖dualFormValue6 (finiteMatrix 3 A3) D (s 2)‖

theorem publishedDualProduct6_of_cofactor_zero
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (D : Fin 6 → ℚ) (s : MixedIndex6)
    (hx : dualNormProduct6 A2 A3 L D s = 0) :
    publishedDualProduct6 A2 A3 L D s = 0 := by
  have h0 : (compound L).det ≠ 0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (compound_unit L hL))
  have h2' : (finiteMatrix 2 A2).det ≠ 0 := by
    apply finiteMatrix_nonsingular
    exact h2
  have h3' : (finiteMatrix 3 A3).det ≠ 0 := by
    apply finiteMatrix_nonsingular
    exact h3
  dsimp only [dualNormProduct6] at hx
  dsimp only [publishedDualProduct6]
  generalize compound L = B0 at h0 hx ⊢
  generalize finiteMatrix 2 A2 = B2 at h2' hx ⊢
  generalize finiteMatrix 3 A3 = B3 at h3' hx ⊢
  refine scalar_product_zero_transport _ _ _ _ _ _ ?_ ?_ ?_ hx
  · with_reducible exact dualFormValue6_norm_zero B0 h0 D (s 0)
  · with_reducible exact dualFormValue6_norm_zero B2 h2' D (s 1)
  · with_reducible exact dualFormValue6_norm_zero B3 h3' D (s 2)

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}

theorem source_equation4126
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) :
    ∃ B : ℝ, (∀ q : V, B < q.val → ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
      actualNormProduct6 A2 A3 L (R.M q) s = 0) ∧
      ∀ q : V, B < q.val →
        ∃ a : ℚ, a ≠ 0 ∧
          normalForm6 (R.M q) = a • rationalFrameDual42
            (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) (sourceFrameIndependent6 R q) 5 ∧
          (∀ k, (R.M q k : ℚ) = a*dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q) k) ∧
          (∀ k, dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q) k = a⁻¹*(R.M q k : ℚ)) ∧
          ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
            dualNormProduct6 A2 A3 L
              (dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q)) s = 0 ∧
            publishedDualProduct6 A2 A3 L
              (dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q)) s = 0 := by
  obtain ⟨B,hB,hdual⟩ := source_dual_eventual_zero6 R
  refine ⟨B,hB,?_⟩
  intro q hq
  obtain ⟨a,ha,hform,hscale,hinverse,hzero⟩ := hdual q hq
  refine ⟨a,ha,hform,hscale,hinverse,?_⟩
  intro s hs
  have hz := hzero s hs
  refine ⟨hz,?_⟩
  apply publishedDualProduct6_of_cofactor_zero A2 A3 L hL h2 h3
  exact hz

end CompoundFeasibility.SchlickeweiEquation4126
