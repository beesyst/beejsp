import SubspaceBridge.SourcePrimitiveHeight10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceHeightEnvelope10
open SchmidtNormal10 OriginalDual10 SourcePrimitiveHeight10

theorem transpose_inverse_reconstruction10 (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : L.det = 1) (Z : Fin 10 → ℝ) :
    L.transpose *ᵥ (L⁻¹.transpose *ᵥ Z) = Z := by
  have hu : IsUnit L.det := by rw [hL]; exact isUnit_one
  rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul,Matrix.nonsing_inv_mul L hu,
    Matrix.transpose_one,Matrix.one_mulVec]

def transposeRowConstant10 (L : Matrix (Fin 10) (Fin 10) ℝ) : ℝ :=
  1+∑ i, ∑ k, |L k i|

theorem transposeRowConstant10_pos (L : Matrix (Fin 10) (Fin 10) ℝ) :
    0 < transposeRowConstant10 L := by
  have hh : 0 ≤ ∑ i : Fin 10, ∑ k : Fin 10, |L k i| :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => abs_nonneg _))
  unfold transposeRowConstant10
  linarith

theorem actual_transformed_cofactor_bound10 (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : L.det = 1) (v : Matrix (Fin 10) (Fin 10) ℤ) (Q : ℝ)
    (hrow : ∀ (j : Fin 9) i, |(L *ᵥ integerReal (v j.castSucc)) i| ≤ Q) (i : Fin 10) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 v k : ℝ))) i‖ ≤ 362880*Q^9 := by
  have hh := real_cofactor_fin10 L hL v (fun _ => Q) (fun _ => 1)
    (fun j k => by simpa only [mul_one] using hrow j k) i
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,one_pow,mul_one] using hh

theorem transpose_back_bound10 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : L.det = 1)
    (Z : Fin 10 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ i, ‖(L⁻¹.transpose *ᵥ Z) i‖ ≤ B) (i : Fin 10) :
    |Z i| ≤ transposeRowConstant10 L*B := by
  have hrow : (∑ k, |L k i|) ≤ transposeRowConstant10 L := by
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin 10 => ∑ k : Fin 10, |L k i|)
      (fun i _ => Finset.sum_nonneg (fun k _ => abs_nonneg _)) (Finset.mem_univ i)
    unfold transposeRowConstant10
    linarith
  calc
    |Z i| = ‖∑ k, L k i*(L⁻¹.transpose *ᵥ Z) k‖ := by
      change |Z i| = ‖(L.transpose *ᵥ (L⁻¹.transpose *ᵥ Z)) i‖
      rw [transpose_inverse_reconstruction10 L hL Z,Real.norm_eq_abs]
    _ ≤ ∑ k, ‖L k i*(L⁻¹.transpose *ᵥ Z) k‖ := norm_sum_le _ _
    _ ≤ ∑ k, |L k i| *B := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbound k) (abs_nonneg _)
    _ = (∑ k, |L k i|)*B := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow hB

theorem actual_integer_cofactor_bound10 (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : L.det = 1) (v : Matrix (Fin 10) (Fin 10) ℤ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hrow : ∀ (j : Fin 9) i, |(L *ᵥ integerReal (v j.castSucc)) i| ≤ Q) (i : Fin 10) :
    |(integerLastDual10 v i : ℝ)| ≤ (transposeRowConstant10 L*362880)*Q^9 := by
  have hh := transpose_back_bound10 L hL (fun k => (integerLastDual10 v k : ℝ))
    (362880*Q^9) (by positivity) (actual_transformed_cofactor_bound10 L hL v Q hrow) i
  exact hh.trans_eq (by ring)

theorem normalHeight10_real_le (M : Fin 10 → ℤ) (B : ℝ)
    (h : ∀ i, |(M i : ℝ)| ≤ B) : (normalHeight10 M : ℝ) ≤ B := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 10))
    Finset.univ_nonempty (fun i => (M i).natAbs)
  change ((Finset.univ.sup (fun i => (M i).natAbs) : ℕ) : ℝ) ≤ B
  rw [hi]
  have he : ((M i).natAbs : ℝ) = |(M i : ℝ)| := by
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  rw [he]
  exact h i

theorem actual_primitive_height_upper10 (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : L.det = 1) (v : Matrix (Fin 10) (Fin 10) ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ)))
    (M a : Fin 10 → ℤ) (hM : M ≠ 0) (ha : (∑ i, a i*M i) = 1)
    (hann : ∀ j : Fin 9, (∑ i, M i*v j.castSucc i) = 0)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hrow : ∀ (j : Fin 9) i, |(L *ᵥ integerReal (v j.castSucc)) i| ≤ Q) :
    (normalHeight10 M : ℝ) ≤ (transposeRowConstant10 L*362880)*Q^9 := by
  obtain ⟨hg,hscale,hgcd⟩ := primitive_original_cofactor_factor10 v hv M a hM ha hann
  let g : ℤ := ∑ i, a i*integerLastDual10 v i
  have hg1 : 1 ≤ |(g : ℝ)| := by
    have hn : 1 ≤ g.natAbs := Int.natAbs_pos.mpr hg
    have hr : (1 : ℝ) ≤ (g.natAbs : ℝ) := by exact_mod_cast hn
    simpa only [Int.cast_natAbs,Int.cast_abs] using hr
  apply normalHeight10_real_le
  intro i
  have hs : (integerLastDual10 v i : ℝ) = (g : ℝ)*(M i : ℝ) := by exact_mod_cast hscale i
  have hh := actual_integer_cofactor_bound10 L hL v Q hQ hrow i
  have hl : |(M i : ℝ)| ≤ |(integerLastDual10 v i : ℝ)| := by
    rw [hs,abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hg1 (abs_nonneg (M i : ℝ))
  exact hl.trans hh

end CompoundFeasibility.SourceHeightEnvelope10
