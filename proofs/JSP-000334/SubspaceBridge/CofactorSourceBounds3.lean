import SubspaceBridge.CofactorSourceGeometry3
open scoped BigOperators Matrix
namespace JSP000334
noncomputable section

theorem cofactorOriginalMatrix3_table (k : Fin 3) :
    retainedIntegerMatrix3 k =
      ![![![0,1,0],![0,0,1],![1,1,1]],
        ![![1,0,0],![0,0,1],![1,1,1]],
        ![![1,0,0],![0,1,0],![1,1,1]]] k := by
  fin_cases k <;> decide

theorem cofactorIntegerMatrix3_table (k : Fin 3) :
    cofactorIntegerMatrix3 k =
      ![![![-1,1,0],![-1,0,1],![1,0,0]],
        ![![-1,1,0],![0,1,-1],![0,-1,0]],
        ![![1,0,-1],![0,1,-1],![0,0,1]]] k := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [cofactorIntegerMatrix3,cofactorOriginalMatrix3_table,
      Matrix.adjugate_fin_three,Matrix.transpose_apply,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

noncomputable def cofactorRationalMatrix3 (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℚ :=
  (cofactorIntegerMatrix3 k).map (Int.castRingHom ℚ)

noncomputable def cofactorDualValue3 (k : Fin 3) (x : Fin 3 → ℚ) (i : Fin 3) : ℚ :=
  ∑ l : Fin 3, (cofactorRationalMatrix3 k)⁻¹ l i * x l

theorem cofactorRationalMatrix3_det (k : Fin 3) :
    (cofactorRationalMatrix3 k).det = 1 := by
  have hd : (cofactorRationalMatrix3 k).det = ((cofactorIntegerMatrix3 k).det : ℚ) :=
    ((Int.castRingHom ℚ).map_det _).symm
  rw [hd, cofactorIntegerMatrix3_det]
  norm_num

theorem cofactorDualValue3_inverse (k : Fin 3) (w : Fin 3 → IntegerTriple) (i j : Fin 3) :
    cofactorDualValue3 k (dualFrameVector3 w j) i =
      (dualFrameRationalMatrix3 w * (cofactorRationalMatrix3 k).transpose)⁻¹ i j := by
  rw [Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]
  rfl

theorem cofactor_scaled_dual_padic_bound3 (p : ℕ) [Fact p.Prime]
    (G : AddSubgroup IntegerTriple) (c : Basis (Fin 3) ℤ G) (u : Fin 3 → G)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (k : Fin 3) (s : Fin 3 → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hpoint : ∀ j i, (padicNorm p (∑ l : Fin 3,
      (cofactorRationalMatrix3 k) i l * ((u j : IntegerTriple) l : ℚ)) : ℝ) ≤ s i)
    (i : Fin 3) :
    (padicNorm p (cofactorDualValue3 k (fun l =>
      ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) *
        dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 l) i) : ℝ) ≤
      s (i.succAbove 0) * s (i.succAbove 1) := by
  let w := fun j => (u j : IntegerTriple)
  let U := dualFrameRationalMatrix3 w * (cofactorRationalMatrix3 k).transpose
  have huQ := dualFrameMatrix3_rational_independent w hu
  have hUnz : U.det ≠ 0 := by
    dsimp [U]
    rw [Matrix.det_mul, Matrix.det_transpose]
    apply mul_ne_zero (dualFrameMatrix3_det_ne_zero w huQ)
    rw [cofactorRationalMatrix3_det]
    norm_num
  have hcof : U.det * U⁻¹ i 2 = U.adjugate i 2 := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
    change _ * (_⁻¹ * _) = _
    rw [← mul_assoc, mul_inv_cancel₀ hUnz, one_mul]
  have hJD : padicNorm p U.det =
      padicNorm p (((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ)) := by
    dsimp [U]
    rw [Matrix.det_mul, Matrix.det_transpose, padicNorm.mul, cofactorRationalMatrix3_det]
    simp only [padicNorm.one, mul_one]
    all_goals
      rw [dualFrameRelativeIndex3_mul_index G c u hu]
      have hd : (dualFrameRationalMatrix3 w).det = ((dualFrameIntegerMatrix3 w).det : ℚ) :=
        ((Int.castRingHom ℚ).map_det _).symm
      rw [hd, ← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      by_cases h : (0 : ℚ) ≤ ((dualFrameIntegerMatrix3 w).det : ℚ)
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg (lt_of_not_ge h), padicNorm.neg]
  have he : cofactorDualValue3 k (fun l =>
      ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) * dualFrameVector3 w 2 l) i =
      ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) * U⁻¹ i 2 := by
    rw [← cofactorDualValue3_inverse k w i 2]
    simp only [cofactorDualValue3, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hnorm : padicNorm p (cofactorDualValue3 k (fun l =>
      ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) * dualFrameVector3 w 2 l) i) =
      padicNorm p (U.adjugate i 2) := by
    rw [he, ← hcof, padicNorm.mul, padicNorm.mul, hJD]
  rw [hnorm]
  apply conditional_last_cofactor_bound3 p U s hs
  intro j l
  have h := hpoint j l
  simpa [U, dualFrameRationalMatrix3, dualFrameIntegerMatrix3,
    Matrix.mul_apply, Matrix.transpose_apply, w, mul_comm] using h

theorem cofactor_source_value3 (k i : Fin 3) (x : IntegerTriple) :
    (∑ l : Fin 3, cofactorRationalMatrix3 k i l * (x l : ℚ)) =
      cofactorForms3 k i (fun l => (x l : ℚ)) := by
  rw [← cofactorIntegerMatrix3_apply k i x]
  simp [cofactorRationalMatrix3, Matrix.mulVec, dotProduct]

theorem cofactor_actual_finite_bounds3
    (k₂ k₃ : Fin 3) (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (c : Basis (Fin 3) ℤ (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃))
    (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple))) :
    let z := fun l => ((dualFrameRelativeIndex3 (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃) u *
      (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
        dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 l
    (∀ i, (padicNorm 2 (cofactorDualValue3 k₂ z i) : ℝ) ≤
      Q ^ (c₂ (i.succAbove 0) + c₂ (i.succAbove 1))) ∧
    (∀ i, (padicNorm 3 (cofactorDualValue3 k₃ z i) : ℝ) ≤
      Q ^ (c₃ (i.succAbove 0) + c₃ (i.succAbove 1))) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hb j := (cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).1 (u j)
  have hp := lt_trans zero_lt_one hQ
  constructor
  · intro i
    rw [Real.rpow_add hp]
    apply cofactor_scaled_dual_padic_bound3 2 _ c u hu k₂ (fun i => Q ^ c₂ i)
      (fun i => (Real.rpow_pos_of_pos hp _).le)
    intro j l
    rw [cofactor_source_value3]
    exact ((hb j).mp (u j).property).1 l
  · intro i
    rw [Real.rpow_add hp]
    apply cofactor_scaled_dual_padic_bound3 3 _ c u hu k₃ (fun i => Q ^ c₃ i)
      (fun i => (Real.rpow_pos_of_pos hp _).le)
    intro j l
    rw [cofactor_source_value3]
    exact ((hb j).mp (u j).property).2 l

def cofactorDualInt3 (k : Fin 3) (m : IntegerTriple) : IntegerTriple :=
  if k = 1 then -(retainedIntegerMatrix3 k *ᵥ m) else retainedIntegerMatrix3 k *ᵥ m

theorem cofactorDualInt3_value (k : Fin 3) (m : IntegerTriple) (i : Fin 3) :
    cofactorDualValue3 k (fun l => (m l : ℚ)) i = (cofactorDualInt3 k m i : ℚ) := by
  let A := cofactorRationalMatrix3 k
  let v : Fin 3 → ℚ := fun l => (cofactorDualInt3 k m l : ℚ)
  have hAv : A.transpose *ᵥ v = fun l => (m l : ℚ) := by
    ext l
    fin_cases k <;> fin_cases l <;>
      norm_num [A,v,cofactorRationalMatrix3,cofactorRealMatrix3,cofactorIntegerMatrix3_table,
        cofactorDualInt3,cofactorOriginalMatrix3_table,
        integerTripleReal3,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
        Fin.sum_univ_succ,Pi.single_apply,Fin.succAbove,Fin.ext_iff,Fin.lt_def,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] <;> ring <;> try rfl
  have hunit : IsUnit A.det := by
    dsimp [A]
    rw [cofactorRationalMatrix3_det]
    norm_num
  change (A⁻¹.transpose *ᵥ (fun l => (m l : ℚ))) i = v i
  rw [← hAv, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv A hunit, Matrix.transpose_one, Matrix.one_mulVec]

theorem cofactorDualInt3_height_bound (k : Fin 3) (m : IntegerTriple) (i : Fin 3) :
    |(cofactorDualInt3 k m i : ℝ)| ≤ 3 * (rothKernelRowHeight m : ℝ) := by
  have hi := conditional_height_coord3 m
  have hn : (0 : ℝ) ≤ rothKernelRowHeight m := Nat.cast_nonneg _
  have hneg : |-(m 2 : ℝ) + -(m 1 : ℝ) + -(m 0 : ℝ)| ≤
      3 * (rothKernelRowHeight m : ℝ) := by
    rw [show -(m 2 : ℝ) + -(m 1 : ℝ) + -(m 0 : ℝ) =
      -((m 0 : ℝ) + ((m 1 : ℝ) + (m 2 : ℝ))) by ring,abs_neg]
    calc
      _ ≤ |(m 0 : ℝ)| + (|(m 1 : ℝ)| + |(m 2 : ℝ)|) :=
        (abs_add _ _).trans (add_le_add_left (abs_add _ _) _)
      _ ≤ _ := by linarith [hi 0,hi 1,hi 2]
  fin_cases k <;> fin_cases i <;>
    simp [cofactorDualInt3,cofactorOriginalMatrix3_table,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Pi.single_apply,Fin.succAbove,Fin.ext_iff,Fin.lt_def] <;>
    nlinarith [hi 0,hi 1,hi 2,hneg,abs_add (m 0 : ℝ) (m 1 : ℝ),
      abs_add ((m 0 : ℝ)+(m 1 : ℝ)) (m 2 : ℝ),
      abs_add (m 1 : ℝ) (m 2 : ℝ),abs_add (m 0 : ℝ) ((m 1 : ℝ)+(m 2 : ℝ))]

noncomputable def cofactorSelectedProduct3 (k₀ k₂ k₃ : Fin 3)
    (s : Fin 3 → Fin 3) (x : Fin 3 → ℚ) : ℝ :=
  |(cofactorDualValue3 k₀ x (s 0) : ℝ)| *
    (padicNorm 2 (cofactorDualValue3 k₂ x (s 1)) : ℝ) *
    (padicNorm 3 (cofactorDualValue3 k₃ x (s 2)) : ℝ)

theorem cofactor_selected_product_lower3 (k₀ k₂ k₃ : Fin 3)
    (s : Fin 3 → Fin 3) (m : IntegerTriple) (hm : m ≠ 0)
    (hn : cofactorSelectedProduct3 k₀ k₂ k₃ s (fun l => (m l : ℚ)) ≠ 0) :
    1 / (9 * (rothKernelRowHeight m : ℝ) ^ 2) ≤
      cofactorSelectedProduct3 k₀ k₂ k₃ s (fun l => (m l : ℚ)) := by
  let z₀ := cofactorDualInt3 k₀ m (s 0)
  let z₂ := cofactorDualInt3 k₂ m (s 1)
  let z₃ := cofactorDualInt3 k₃ m (s 2)
  have hp : cofactorSelectedProduct3 k₀ k₂ k₃ s (fun l => (m l : ℚ)) =
      |(z₀ : ℝ)| * (padicNorm 2 (z₂ : ℚ) : ℝ) * (padicNorm 3 (z₃ : ℚ) : ℝ) := by
    simp only [cofactorSelectedProduct3, cofactorDualInt3_value, Rat.cast_intCast]
    rfl
  rw [hp] at hn ⊢
  have hz₀ : z₀ ≠ 0 := by intro h; simp [h] at hn
  have hz₂ : z₂ ≠ 0 := by intro h; simp [h] at hn
  have hz₃ : z₃ ≠ 0 := by intro h; simp [h] at hn
  have hH := conditional_height_pos3 m hm
  have h0 : 1 ≤ |(z₀ : ℝ)| := by
    have hh : 1 ≤ z₀.natAbs := Int.natAbs_pos.mpr hz₀
    have hab : (z₀.natAbs : ℝ) = |(z₀ : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [← hab]
    exact_mod_cast hh
  have h2 := (conditional_integer_local_lower3 z₂ hz₂).1
  have h3 := (conditional_integer_local_lower3 z₃ hz₃).2
  have h2n : (0 : ℝ) ≤ padicNorm 2 (z₂ : ℚ) := by exact_mod_cast padicNorm.nonneg _
  have h3n : (0 : ℝ) ≤ padicNorm 3 (z₃ : ℚ) := by exact_mod_cast padicNorm.nonneg _
  have hu2 := cofactorDualInt3_height_bound k₂ m (s 1)
  have hu3 := cofactorDualInt3_height_bound k₃ m (s 2)
  have hl2 : 1 / (3 * (rothKernelRowHeight m : ℝ)) ≤ (padicNorm 2 (z₂ : ℚ) : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hu2 h2n]
  have hl3 : 1 / (3 * (rothKernelRowHeight m : ℝ)) ≤ (padicNorm 3 (z₃ : ℚ) : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hu3 h3n]
  have hmul := mul_le_mul hl2 hl3 (by positivity) h2n
  have hfull := mul_le_mul h0 hmul (by positivity) (abs_nonneg (z₀ : ℝ))
  calc
    _ = (1 : ℝ) * (1 / (3 * (rothKernelRowHeight m : ℝ)) *
        (1 / (3 * (rothKernelRowHeight m : ℝ)))) := by ring
    _ ≤ _ := by simpa [mul_assoc] using hfull


theorem cofactor_actual_real_bound3
    (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (B : Basis (Fin 3) ℝ RealTriple)
    (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hreal : ∀ i, |((dualFrameRelativeIndex3 (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃) u *
      (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℝ) *
        dualFrameRealLocalValue3 (cofactorRealMatrix3 k₀)
          (fun j => (u j : IntegerTriple)) 2 i| ≤
      6 * ((cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℝ) * (Q ^ c₀ i)⁻¹ *
        (successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) 2)⁻¹)
    (hsmall : successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) 1 < Q ^ (-delta))
    (i : Fin 3) :
    |((dualFrameRelativeIndex3 (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃) u *
      (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℝ) *
        dualFrameRealLocalValue3 (cofactorRealMatrix3 k₀)
          (fun j => (u j : IntegerTriple)) 2 i| ≤
      36 * (∏ l : Fin 3, Q ^ c₀ l) * (Q ^ c₀ i)⁻¹ * Q ^ (-2 * delta) := by
  let G := cofactorSourceLattice3 k₂ k₃ Q c₂ c₃
  let P := ∏ l : Fin 3, Q ^ c₀ l
  have ha (i : Fin 3) : 0 < Q ^ c₀ i := Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _
  have hP : 0 < P := Finset.prod_pos (fun l _ => ha l)
  have hD : (0 : ℝ) < G.index := by
    rw [(cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1]
    unfold qCongruenceIndex3
    positivity
  have hcov : ZLattice.covolume (lattice3 B) = (G.index : ℝ) := by
    rw [hB, (cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1]
    exact (cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.2
  have hvol : MeasureTheory.volume.real (parallelepipedBody3 (cofactorSourceCoordinates3 k₀ Q c₀ hQ)) =
      8 * P := by
    rw [← cofactorSourceBody3_eq_parallelepiped k₀ Q c₀ hQ]
    exact cofactorSourceBody3_volume k₀ Q c₀ hQ
  have hl := source_minima_product_lower3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) G.index P hP hvol hcov
  obtain ⟨_, _, _, hs, horder, _⟩ := exists_successive_minima3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
  have hrec := conditional_reciprocal_last3 _ hs horder.1 G.index P (Q ^ (-delta)) hD hP
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) hl hsmall.le
  have he : (Q ^ (-delta)) ^ 2 = Q ^ (-2 * delta) := by
    rw [pow_two, ← Real.rpow_add (lt_trans zero_lt_one hQ)]
    congr 1
    ring
  rw [he] at hrec
  have hh := mul_le_mul_of_nonneg_left hrec
    (by positivity : 0 ≤ 6 * (G.index : ℝ) * (Q ^ c₀ i)⁻¹)
  apply (hreal i).trans
  calc
    _ ≤ _ := hh
    _ = _ := by field_simp; ring


noncomputable def cofactorDualRealCoordinates3 (k : Fin 3) : RealTriple ≃ₗ[ℝ] RealTriple :=
  LinearEquiv.ofBijective (Matrix.toLin' (cofactorRealMatrix3 k)⁻¹.transpose) (by
    have h : IsUnit (cofactorRealMatrix3 k) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      rw [cofactorRealMatrix3_det]
      norm_num
    have ht : IsUnit (cofactorRealMatrix3 k)⁻¹.transpose := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      exact IsUnit.inv ((Matrix.isUnit_iff_isUnit_det _).mp h)
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr ht,
      Matrix.mulVec_surjective_iff_isUnit.mpr ht⟩)

theorem cofactorDualRealCoordinates3_apply (k : Fin 3) (x : RealTriple) (i : Fin 3) :
    cofactorDualRealCoordinates3 k x i =
      ∑ j : Fin 3, (cofactorRealMatrix3 k)⁻¹ j i * x j := rfl

theorem cofactorDualInt3_real_value (k : Fin 3) (z : IntegerTriple) (i : Fin 3) :
    cofactorDualRealCoordinates3 k (integerTripleReal3 z) i = (cofactorDualInt3 k z i : ℝ) := by
  let A := cofactorRealMatrix3 k
  let v : RealTriple := fun l => (cofactorDualInt3 k z l : ℝ)
  have hAv : A.transpose *ᵥ v = integerTripleReal3 z := by
    ext l
    fin_cases k <;> fin_cases l <;>
      norm_num [A,v,cofactorRationalMatrix3,cofactorRealMatrix3,cofactorIntegerMatrix3_table,
        cofactorDualInt3,cofactorOriginalMatrix3_table,
        integerTripleReal3,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
        Fin.sum_univ_succ,Pi.single_apply,Fin.succAbove,Fin.ext_iff,Fin.lt_def,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] <;> ring <;> try rfl
  have hunit : IsUnit A.det := by
    dsimp [A]
    rw [cofactorRealMatrix3_det]
    norm_num
  change (A⁻¹.transpose *ᵥ integerTripleReal3 z) i = v i
  rw [← hAv, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv A hunit, Matrix.transpose_one, Matrix.one_mulVec]

theorem cofactor_scaled_real_value3 (k : Fin 3) (w : Fin 3 → IntegerTriple)
    (t : ℕ) (z : IntegerTriple)
    (hz : ∀ i, (t : ℚ) * dualFrameVector3 w 2 i = (z i : ℚ)) (i : Fin 3) :
    |(cofactorDualValue3 k (fun l => (z l : ℚ)) i : ℝ)| =
      |(t : ℝ) * dualFrameRealLocalValue3 (cofactorRealMatrix3 k) w 2 i| := by
  rw [cofactorDualInt3_value, Rat.cast_intCast, ← cofactorDualInt3_real_value,
    cofactorDualRealCoordinates3_apply]
  congr 1
  have hr (l : Fin 3) : (z l : ℝ) = (t : ℝ) * (dualFrameVector3 w 2 l : ℝ) := by
    exact_mod_cast (hz l).symm
  simp only [integerTripleReal3, LinearMap.coe_mk, AddHom.coe_mk, hr,
    dualFrameRealLocalValue3, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem cofactorDualValue3_scale (k : Fin 3) (q : ℚ) (x : Fin 3 → ℚ) (i : Fin 3) :
    cofactorDualValue3 k (fun l => q * x l) i = q * cofactorDualValue3 k x i := by
  simp only [cofactorDualValue3, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem cofactorSelectedProduct3_nonneg (k₀ k₂ k₃ : Fin 3)
    (s : Fin 3 → Fin 3) (x : Fin 3 → ℚ) : 0 ≤ cofactorSelectedProduct3 k₀ k₂ k₃ s x := by
  unfold cofactorSelectedProduct3
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (by exact_mod_cast padicNorm.nonneg _))
    (by exact_mod_cast padicNorm.nonneg _)

theorem cofactorSelectedProduct3_scale (k₀ k₂ k₃ : Fin 3)
    (s : Fin 3 → Fin 3) (q : ℚ) (x : Fin 3 → ℚ) :
    cofactorSelectedProduct3 k₀ k₂ k₃ s (fun l => q * x l) =
      (|((q : ℚ) : ℝ)| * (padicNorm 2 q : ℝ) * (padicNorm 3 q : ℝ)) *
        cofactorSelectedProduct3 k₀ k₂ k₃ s x := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  simp only [cofactorSelectedProduct3, cofactorDualValue3_scale, Rat.cast_mul,
    abs_mul, padicNorm.mul]
  ring

theorem cofactor_primitive_product_le3 (k₀ k₂ k₃ : Fin 3)
    (s : Fin 3 → Fin 3) (g : ℤ) (hg : g ≠ 0) (z m : IntegerTriple)
    (hz : ∀ i, z i = g * m i) :
    cofactorSelectedProduct3 k₀ k₂ k₃ s (fun l => (m l : ℚ)) ≤
      cofactorSelectedProduct3 k₀ k₂ k₃ s (fun l => (z l : ℚ)) := by
  have he : (fun l => (z l : ℚ)) = fun l => (g : ℚ) * (m l : ℚ) := by
    ext l
    rw [hz l, Int.cast_mul]
  rw [he, cofactorSelectedProduct3_scale]
  have hl := rothInteger_three_place_lower g hg
  change (1 : ℝ) ≤ |(g : ℝ)| * (padicNorm 2 (g : ℚ) : ℝ) * (padicNorm 3 (g : ℚ) : ℝ) at hl
  have hh := mul_le_mul_of_nonneg_right hl
    (cofactorSelectedProduct3_nonneg k₀ k₂ k₃ s (fun l => (m l : ℚ)))
  simpa using hh

theorem cofactor_selected_product_upper3
    (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hd : 0 < delta)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (s : Fin 3 → Fin 3) (hweight : -(3 * delta) / 4 ≤ c₀ (s 0) + c₂ (s 1) + c₃ (s 2))
    (z : IntegerTriple)
    (hreal : ∀ i, |(cofactorDualValue3 k₀ (fun l => (z l : ℚ)) i : ℝ)| ≤
      36 * (∏ l : Fin 3, Q ^ c₀ l) * (Q ^ c₀ i)⁻¹ * Q ^ (-2 * delta))
    (h2 : ∀ i, (padicNorm 2 (cofactorDualValue3 k₂ (fun l => (z l : ℚ)) i) : ℝ) ≤
      Q ^ (c₂ (i.succAbove 0) + c₂ (i.succAbove 1)))
    (h3 : ∀ i, (padicNorm 3 (cofactorDualValue3 k₃ (fun l => (z l : ℚ)) i) : ℝ) ≤
      Q ^ (c₃ (i.succAbove 0) + c₃ (i.succAbove 1))) :
    cofactorSelectedProduct3 k₀ k₂ k₃ s (fun l => (z l : ℚ)) ≤ 36 * Q ^ (-delta / 4) := by
  have hp := lt_trans zero_lt_one hQ
  have he : (∏ l : Fin 3, Q ^ c₀ l) * (Q ^ c₀ (s 0))⁻¹ * Q ^ (-2 * delta) *
      Q ^ (c₂ ((s 1).succAbove 0) + c₂ ((s 1).succAbove 1)) *
      Q ^ (c₃ ((s 2).succAbove 0) + c₃ ((s 2).succAbove 1)) =
        Q ^ (-2 * delta - (c₀ (s 0) + c₂ (s 1) + c₃ (s 2))) := by
    rw [← Real.rpow_sum_of_pos hp, ← Real.rpow_neg hp.le,
      conditional_sum_others3, conditional_sum_others3]
    rw [← Real.rpow_add hp, ← Real.rpow_add hp, ← Real.rpow_add hp, ← Real.rpow_add hp]
    congr 1
    simp only [Finset.sum_add_distrib] at hb
    linarith
  have hn2 : (0 : ℝ) ≤ padicNorm 2 (cofactorDualValue3 k₂ (fun l => (z l : ℚ)) (s 1)) := by
    exact_mod_cast padicNorm.nonneg _
  have hn3 : (0 : ℝ) ≤ padicNorm 3 (cofactorDualValue3 k₃ (fun l => (z l : ℚ)) (s 2)) := by
    exact_mod_cast padicNorm.nonneg _
  have hr0 : 0 ≤ 36 * (∏ l : Fin 3, Q ^ c₀ l) * (Q ^ c₀ (s 0))⁻¹ * Q ^ (-2 * delta) := by
    positivity
  have hr2 : 0 ≤ Q ^ (c₂ ((s 1).succAbove 0) + c₂ ((s 1).succAbove 1)) :=
    (Real.rpow_pos_of_pos hp _).le
  have hmul := mul_le_mul (mul_le_mul (hreal (s 0)) (h2 (s 1)) hn2 hr0)
    (h3 (s 2)) hn3 (mul_nonneg hr0 hr2)
  have hbound := Real.rpow_le_rpow_of_exponent_le hQ.le
    (show -2 * delta - (c₀ (s 0) + c₂ (s 1) + c₃ (s 2)) ≤ -delta / 4 by linarith)
  calc
    _ ≤ _ := hmul
    _ = 36 * Q ^ (-2 * delta - (c₀ (s 0) + c₂ (s 1) + c₃ (s 2))) := by
      rw [← he]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by norm_num)

theorem cofactorDualInt3_reconstruct (k : Fin 3) (z : IntegerTriple) (l : Fin 3) :
    (z l : ℝ) = ∑ i : Fin 3, cofactorRealMatrix3 k i l * (cofactorDualInt3 k z i : ℝ) := by
  fin_cases k <;> fin_cases l <;>
    norm_num [cofactorRealMatrix3,cofactorIntegerMatrix3_table,cofactorDualInt3,
      cofactorOriginalMatrix3_table,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Pi.single_apply,Fin.succAbove,Fin.ext_iff,Fin.lt_def,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] <;> ring <;> try rfl

theorem cofactor_primitive_height_bound3 (k : Fin 3) (g : ℤ) (hg : g ≠ 0)
    (z m : IntegerTriple) (hz : ∀ i, z i = g * m i) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ i, |(cofactorDualValue3 k (fun l => (z l : ℚ)) i : ℝ)| ≤ M) :
    (rothKernelRowHeight m : ℝ) ≤ 3 * M := by
  have hgabs : (1 : ℝ) ≤ |(g : ℝ)| := by
    have h : 1 ≤ g.natAbs := Int.natAbs_pos.mpr hg
    have he : (g.natAbs : ℝ) = |(g : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [← he]
    exact_mod_cast h
  have hcoeff (i l : Fin 3) : |cofactorRealMatrix3 k i l| ≤ 1 := by
    fin_cases k <;> fin_cases i <;> fin_cases l <;>
      norm_num [cofactorRealMatrix3,cofactorIntegerMatrix3_table,cofactorOriginalMatrix3_table,Pi.single_apply,Fin.succAbove,Fin.ext_iff,Fin.lt_def,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  have hm (l : Fin 3) : |(m l : ℝ)| ≤ 3 * M := by
    have hzbound : |(z l : ℝ)| ≤ 3 * M := by
      rw [cofactorDualInt3_reconstruct k z l]
      calc
        _ ≤ ∑ i : Fin 3, |cofactorRealMatrix3 k i l * (cofactorDualInt3 k z i : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin 3, M := by
          apply Finset.sum_le_sum
          intro i _
          have hb' := hb i
          rw [cofactorDualInt3_value, Rat.cast_intCast] at hb'
          rw [abs_mul]
          exact (mul_le_mul (hcoeff i l) hb' (abs_nonneg _) (by norm_num)).trans_eq (one_mul M)
        _ = 3 * M := by simp
    rw [hz l, Int.cast_mul, abs_mul] at hzbound
    nlinarith [abs_nonneg (m l : ℝ)]
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => (m i).natAbs)
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty)
  have he : rothKernelRowHeight m = (m i).natAbs := by
    apply le_antisymm
    · exact Finset.sup_le (fun j hj => hmax j hj)
    · exact Finset.le_sup (f := fun j : Fin 3 => (m j).natAbs) hi
  rw [he]
  have hab : ((m i).natAbs : ℝ) = |(m i : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [hab]
  exact hm i

theorem cofactor_upper_height_power3 (k : Fin 3) (Q delta : ℝ) (c₀ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hd : 0 < delta) (hc₀ : ∀ i, |c₀ i| ≤ 1) (hcut : 108 ≤ Q)
    (g : ℤ) (hg : g ≠ 0) (z m : IntegerTriple) (hz : ∀ i, z i = g * m i)
    (hb : ∀ i, |(cofactorDualValue3 k (fun l => (z l : ℚ)) i : ℝ)| ≤
      36 * (∏ l : Fin 3, Q ^ c₀ l) * (Q ^ c₀ i)⁻¹ * Q ^ (-2 * delta)) :
    (rothKernelRowHeight m : ℝ) ≤ Q ^ (9 : ℝ) := by
  have hp := lt_trans zero_lt_one hQ
  have hP : (∏ i : Fin 3, Q ^ c₀ i) ≤ Q ^ (3 : ℕ) := by
    calc
      _ ≤ ∏ _i : Fin 3, Q := Finset.prod_le_prod
        (fun i _ => (Real.rpow_pos_of_pos hp _).le)
        (fun i _ => (Real.rpow_le_rpow_of_exponent_le hQ.le (abs_le.mp (hc₀ i)).2).trans_eq
          (Real.rpow_one Q))
      _ = _ := by simp
  have hi (i : Fin 3) : (Q ^ c₀ i)⁻¹ ≤ Q := by
    rw [← Real.rpow_neg hp.le]
    exact (Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith [(abs_le.mp (hc₀ i)).1])).trans_eq
      (Real.rpow_one Q)
  have hdQ : Q ^ (-2 * delta) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hQ.le (by linarith)
  have hheight : (rothKernelRowHeight m : ℝ) ≤ 3 * (36 * Q ^ (4 : ℕ)) := by
    apply cofactor_primitive_height_bound3 k g hg z m hz (36 * Q ^ (4 : ℕ)) (by positivity)
    intro i
    apply (hb i).trans
    have hbase := mul_le_mul (mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 36))
      (hi i) (inv_nonneg.mpr (Real.rpow_pos_of_pos hp _).le) (by positivity : 0 ≤ 36 * Q ^ (3 : ℕ))
    have hfull := mul_le_mul hbase hdQ (Real.rpow_pos_of_pos hp _).le
      (by positivity : 0 ≤ 36 * Q ^ (3 : ℕ) * Q)
    nlinarith
  change (rothKernelRowHeight m : ℝ) ≤ Q ^ ((9 : ℕ) : ℝ)
  rw [Real.rpow_natCast]
  calc
    _ ≤ 108 * Q ^ (4 : ℕ) := by nlinarith
    _ ≤ Q * Q ^ (4 : ℕ) := mul_le_mul_of_nonneg_right hcut (pow_nonneg hp.le _)
    _ = Q ^ (5 : ℕ) := by ring
    _ ≤ Q ^ (9 : ℕ) := pow_le_pow_right₀ hQ.le (by decide)


theorem cofactorDualValue3_real_cast (k : Fin 3) (x : Fin 3 → ℚ) (i : Fin 3) :
    (cofactorDualValue3 k x i : ℝ) =
      ∑ l : Fin 3, (cofactorRealMatrix3 k)⁻¹ l i * (x l : ℝ) := by
  have hmap : (cofactorRationalMatrix3 k).map (Rat.castHom ℝ) = cofactorRealMatrix3 k := by
    ext l j
    simp [cofactorRationalMatrix3, cofactorRealMatrix3]
  have hdet : ((cofactorRationalMatrix3 k).det : ℝ) = (cofactorRealMatrix3 k).det := by
    rw [← hmap]
    exact (Rat.castHom ℝ).map_det _
  have hentry (l j : Fin 3) : (((cofactorRationalMatrix3 k)⁻¹ l j : ℚ) : ℝ) =
      (cofactorRealMatrix3 k)⁻¹ l j := by
    rw [Matrix.inv_def, Matrix.inv_def]
    change ((Ring.inverse (cofactorRationalMatrix3 k).det *
      (cofactorRationalMatrix3 k).adjugate l j : ℚ) : ℝ) =
        Ring.inverse (cofactorRealMatrix3 k).det * (cofactorRealMatrix3 k).adjugate l j
    rw [Ring.inverse_eq_inv, Ring.inverse_eq_inv, Rat.cast_mul, Rat.cast_inv, hdet]
    congr 1
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M l j)
      ((Rat.castHom ℝ).map_adjugate (cofactorRationalMatrix3 k))
    simpa only [hmap, Matrix.map_apply] using h
  simp only [cofactorDualValue3, Rat.cast_sum, Rat.cast_mul, hentry]
end
end JSP000334
