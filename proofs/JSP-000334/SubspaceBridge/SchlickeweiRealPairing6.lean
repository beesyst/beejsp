import SubspaceBridge.SchlickeweiIntegerPairing6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiRealPairing6
open SchlickeweiIntegerPairing6

theorem integer_cast_real_pairing6 (x y : Fin 6 → ℤ) :
    (integerPairing6 x y : ℝ) = ∑ i, (x i : ℝ) * (y i : ℝ) := by
  simp only [integerPairing6, Int.cast_sum, Int.cast_mul]

theorem native_real_matrix_pairing6
    (B : Matrix (Fin 6) (Fin 6) ℝ) (hB : B.det ≠ 0)
    (xr yr : Fin 6 → ℝ) :
    (∑ k, xr k * yr k) = ∑ i, (B *ᵥ xr) i * (B⁻¹.transpose *ᵥ yr) i := by
  change xr ⬝ᵥ yr = (B *ᵥ xr) ⬝ᵥ (B⁻¹.transpose *ᵥ yr)
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB), Matrix.one_mulVec]

theorem native_real_integer_pairing6
    (B : Matrix (Fin 6) (Fin 6) ℝ) (hB : B.det ≠ 0) (x y : Fin 6 → ℤ) :
    (integerPairing6 x y : ℝ) =
      ∑ i, (B *ᵥ (fun k => (x k : ℝ))) i *
        (B⁻¹.transpose *ᵥ (fun k => (y k : ℝ))) i := by
  let xr : Fin 6 → ℝ := fun k => (x k : ℝ)
  let yr : Fin 6 → ℝ := fun k => (y k : ℝ)
  exact (integer_cast_real_pairing6 x y).trans (native_real_matrix_pairing6 B hB xr yr)


theorem real_dual_coordinates6
    (B : Matrix (Fin 6) (Fin 6) ℝ) (y : Fin 6 → ℤ) (i : Fin 6) :
    SchlickeweiDualVanishing6.dualFormValue6 B (fun k => (y k : ℚ)) i =
      (B⁻¹.transpose *ᵥ (fun k => (y k : ℝ))) i := by
  simp only [SchlickeweiDualVanishing6.dualFormValue6, map_intCast, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  ring


theorem real_pairing_sum_bound6
    (B : Matrix (Fin 6) (Fin 6) ℝ) (hB : B.det ≠ 0)
    (x y : Fin 6 → ℤ) (a b : Fin 6 → ℝ)
    (ha : ∀ i, 0 ≤ a i) (_hb : ∀ i, 0 ≤ b i)
    (hx : ∀ i, ‖(B *ᵥ (fun k => (x k : ℝ))) i‖ ≤ a i)
    (hy : ∀ i, ‖(B⁻¹.transpose *ᵥ (fun k => (y k : ℝ))) i‖ ≤ b i) :
    ‖(integerPairing6 x y : ℝ)‖ ≤ ∑ i, a i * b i := by
  rw [native_real_integer_pairing6 B hB x y]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  exact mul_le_mul (hx i) (hy i) (norm_nonneg _) (ha i)


theorem real_power_cancel6 (Q d c delta : ℝ) (hQ : 0 < Q) (_hd : 0 ≤ d) :
    Q ^ (c - delta) * (d / Q ^ c) = d * Q ^ (-delta) := by
  have hc : 0 < Q ^ c := Real.rpow_pos_of_pos hQ c
  rw [show c - delta = -delta + c by ring, Real.rpow_add hQ]
  field_simp [hc.ne']
  ring


open SourceReadiness6 SchlickeweiDualVanishing6 SchlickeweiSatz51Selected6

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem source_first_five_real_bounds6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V)
    (j : Fin 5) (i : Fin 6) :
    ‖(compound L *ᵥ (fun k => ((R.w q j.castSucc : Fin 6 → ℤ) k : ℝ))) i‖ ≤
      (q.val ^ (11 : ℕ)) ^ (R.c 0 i - R.delta) := by
  exact (R.frames q).2.2.2.2.1 j i

theorem source_auxiliary_real_bounds6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V)
    (y : Fin 6 → ℤ) (hy : sourceAuxiliaryInteger6 R q y) (i : Fin 6) :
    ‖((compound L)⁻¹.transpose *ᵥ (fun k => (y k : ℝ))) i‖ ≤
      ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) /
        (q.val ^ (11 : ℕ)) ^ (R.c 0 i) := by
  have hi := hy.1 i
  rw [real_dual_coordinates6] at hi
  exact hi

theorem source_real_pairing_bound6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V)
    (y : Fin 6 → ℤ) (hy : sourceAuxiliaryInteger6 R q y) (j : Fin 5) :
    ‖(integerPairing6 (R.w q j.castSucc : Fin 6 → ℤ) y : ℝ)‖ ≤
      6 * ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) *
        (q.val ^ (11 : ℕ)) ^ (-R.delta) := by
  let Q := q.val ^ (11 : ℕ)
  let d := ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3))
  have hq : 1 < q.val := hQV q.val q.property
  have hqp : 0 < q.val := lt_trans zero_lt_one hq
  have hQ1 : 1 < Q := one_lt_pow₀ hq (by decide)
  have hQ : 0 < Q := pow_pos hqp _
  have hd : 0 < d := (SourceRelativeIndex6.source_frame_normalization6 R q).2.2.2.2.2
  have hB : (compound L).det ≠ 0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (compound_unit L hL))
  calc
    _ ≤ ∑ i : Fin 6, Q ^ (R.c 0 i - R.delta) * (d / Q ^ (R.c 0 i)) :=
      real_pairing_sum_bound6 (compound L) hB (R.w q j.castSucc : Fin 6 → ℤ) y
        (fun i => Q ^ (R.c 0 i - R.delta)) (fun i => d / Q ^ (R.c 0 i))
        (fun i => (Real.rpow_pos_of_pos hQ _).le)
        (fun i => (div_pos hd (Real.rpow_pos_of_pos hQ _)).le)
        (source_first_five_real_bounds6 R q j) (source_auxiliary_real_bounds6 R q y hy)
    _ = ∑ _i : Fin 6, d * Q ^ (-R.delta) := by
      apply Finset.sum_congr rfl
      intro i _
      exact real_power_cancel6 Q d (R.c 0 i) R.delta hQ hd.le
    _ = 6 * d * Q ^ (-R.delta) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end CompoundFeasibility.SchlickeweiRealPairing6
