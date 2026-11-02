import SubspaceBridge.RestrictedSource4
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedSelectedIndex4
noncomputable section

theorem selected_integer_two_index_bound
    (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det ≠ 0)
    (G : AddSubgroup (Fin 2 → ℤ)) (b : Basis (Fin 2) ℤ G)
    (e : Fin 2 → ℕ)
    (hlocal : ∀ (x : G) i, padicNorm 2 (((B.map (Int.castRingHom ℚ)) *ᵥ
      (fun k => ((x : Fin 2 → ℤ) k : ℚ))) i) ≤ (2 : ℚ)^(-(e i : ℤ))) :
    2^(∑ i, e i) ≤ B.det.natAbs * G.index := by
  let C : Matrix (Fin 2) (Fin 2) ℤ := fun i j => (b j : Fin 2 → ℤ) i
  have hC : C.det.natAbs = G.index := by
    rw [AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin 2)) G b, Basis.det_apply]
    rfl
  have hli : LinearIndependent ℤ (fun j => (b j : Fin 2 → ℤ)) :=
    b.linearIndependent.map' G.toIntSubmodule.subtype (Submodule.ker_subtype _)
  have hCne : C.det ≠ 0 :=
    (SourceRelativeIndex6.integer_span_index_det (Pi.basisFun ℤ (Fin 2)) _ hli).2.2
  have hdiv : ∀ i j, (2 : ℤ)^(e i) ∣ (B*C) i j := by
    intro i j
    have hh : ((2^e i : ℕ) : ℤ) ∣ (B*C) i j := by
      apply padicNorm.dvd_iff_norm_le.mpr
      convert hlocal (b j) i using 1 <;> simp [Matrix.mul_apply,Matrix.mulVec,dotProduct,C]
    simpa using hh
  choose D hD using hdiv
  let E : Matrix (Fin 2) (Fin 2) ℤ := D
  have hmatrix : B*C = Matrix.diagonal (fun i => (2 : ℤ)^e i) * E := by
    ext i j
    simpa [Matrix.diagonal_mul] using hD i j
  have hdetdiv : (2 : ℤ)^(∑ i, e i) ∣ (B*C).det := by
    rw [hmatrix,Matrix.det_mul,Matrix.det_diagonal,Finset.prod_pow_eq_pow_sum]
    exact dvd_mul_right _ _
  have hnonzero : (B*C).det ≠ 0 := by rw [Matrix.det_mul];exact mul_ne_zero hB hCne
  have hle := Int.natAbs_le_of_dvd_ne_zero hdetdiv hnonzero
  simpa only [Matrix.det_mul,Int.natAbs_mul,Int.natAbs_pow,
    show (2 : ℤ).natAbs = 2 from rfl,hC] using hle

theorem selected_rational_index_lower4 (d : Fin 4)
    (B₂ B₃ : Matrix (Fin d.val) (Fin d.val) ℚ)
    (G : AddSubgroup (Fin d.val → ℤ)) (b : Basis (Fin d.val) ℤ G)
    (e₂ e₃ : Fin d.val → ℕ)
    (h₂ : ∀ (x : G) i, padicNorm 2 ((B₂ *ᵥ (fun k => ((x : Fin d.val → ℤ) k : ℚ))) i) ≤
      (2 : ℚ)^(-(e₂ i : ℤ)))
    (h₃ : ∀ (x : G) i, padicNorm 3 ((B₃ *ᵥ (fun k => ((x : Fin d.val → ℤ) k : ℚ))) i) ≤
      (3 : ℚ)^(-(e₃ i : ℤ))) :
    (padicNorm 2 B₂.det : ℝ) * (padicNorm 3 B₃.det : ℝ) *
      (2 : ℝ)^(∑ i, e₂ i) * (3 : ℝ)^(∑ i, e₃ i) ≤ (G.index : ℝ) := by
  let U : Matrix (Fin d.val) (Fin d.val) ℤ := fun k i => (b k : Fin d.val → ℤ) i
  have hli : LinearIndependent ℤ (fun k => (b k : Fin d.val → ℤ)) :=
    b.linearIndependent.map' G.toIntSubmodule.subtype (Submodule.ker_subtype _)
  have hUne : U.det ≠ 0 := by
    have h := (SourceRelativeIndex6.integer_span_index_det (Pi.basisFun ℤ (Fin d.val)) _ hli).2.2
    change U.transpose.det ≠ 0 at h
    simpa using h
  have hUR : (U.map (Int.castRingHom ℝ)).det ≠ 0 := by
    rw [← integer_matrix_det_cast]
    exact_mod_cast hUne
  have hreal := Matrix.linearIndependent_rows_of_det_ne_zero hUR
  have hindex : |(U.map (Int.castRingHom ℝ)).det| = (G.index : ℝ) := by
    have h := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin d.val)) G b
    rw [Basis.det_apply] at h
    have he : (Pi.basisFun ℤ (Fin d.val)).toMatrix (fun k => (b k : Fin d.val → ℤ)) = U.transpose := by rfl
    rw [he,Matrix.det_transpose] at h
    rw [← integer_matrix_det_cast,← Int.cast_abs,← Int.cast_natAbs,← h]
  have hbase := integer_matrix_three_place_lower U hreal
  rw [hindex] at hbase
  have htwo := padic_det_frame_bound 2 B₂ e₂ U (fun k i => h₂ (b k) i)
  have hthree := padic_det_frame_bound 3 B₃ e₃ U (fun k i => h₃ (b k) i)
  have htwoR : (padicNorm 2 B₂.det : ℝ) * (padicNorm 2 (U.map (Int.castRingHom ℚ)).det : ℝ) ≤
      ((2 : ℝ)^(∑ i, e₂ i))⁻¹ := by
    have hh := (Rat.cast_le (K := ℝ)).mpr htwo
    simpa only [Rat.cast_mul,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat] using hh
  have hthreeR : (padicNorm 3 B₃.det : ℝ) * (padicNorm 3 (U.map (Int.castRingHom ℚ)).det : ℝ) ≤
      ((3 : ℝ)^(∑ i, e₃ i))⁻¹ := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hthree
    simpa only [Rat.cast_mul,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat] using hh
  have hp₂ : 0 ≤ (padicNorm 2 B₂.det : ℝ) := by exact_mod_cast padicNorm.nonneg B₂.det
  have hp₃ : 0 ≤ (padicNorm 3 B₃.det : ℝ) := by exact_mod_cast padicNorm.nonneg B₃.det
  have hu₂ : 0 ≤ (padicNorm 2 (U.map (Int.castRingHom ℚ)).det : ℝ) := by exact_mod_cast padicNorm.nonneg _
  have hu₃ : 0 ≤ (padicNorm 3 (U.map (Int.castRingHom ℚ)).det : ℝ) := by exact_mod_cast padicNorm.nonneg _
  have hm := mul_le_mul htwoR hthreeR (mul_nonneg hp₃ hu₃) (by positivity)
  have hstart := mul_le_mul_of_nonneg_right hbase (mul_nonneg hp₂ hp₃)
  have hstep : (padicNorm 2 B₂.det : ℝ) * (padicNorm 3 B₃.det : ℝ) ≤
      (G.index : ℝ) * (((2 : ℝ)^(∑ i, e₂ i))⁻¹ * ((3 : ℝ)^(∑ i, e₃ i))⁻¹) := by
    calc
      _ ≤ (G.index : ℝ) *
          (((padicNorm 2 B₂.det : ℝ) * (padicNorm 2 (U.map (Int.castRingHom ℚ)).det : ℝ)) *
           ((padicNorm 3 B₃.det : ℝ) * (padicNorm 3 (U.map (Int.castRingHom ℚ)).det : ℝ))) := by nlinarith [hstart]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
  have hlast := mul_le_mul_of_nonneg_right hstep
    (show 0 ≤ (2 : ℝ)^(∑ i, e₂ i) * (3 : ℝ)^(∑ i, e₃ i) by positivity)
  have hcancel : (G.index : ℝ) *
      (((2 : ℝ)^(∑ i, e₂ i))⁻¹ * ((3 : ℝ)^(∑ i, e₃ i))⁻¹) *
      ((2 : ℝ)^(∑ i, e₂ i) * (3 : ℝ)^(∑ i, e₃ i)) = (G.index : ℝ) := by
    calc
      _ = (G.index : ℝ) *
          ((((2 : ℝ)^(∑ i, e₂ i))⁻¹ * (2 : ℝ)^(∑ i, e₂ i)) *
           (((3 : ℝ)^(∑ i, e₃ i))⁻¹ * (3 : ℝ)^(∑ i, e₃ i))) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (by positivity),inv_mul_cancel₀ (by positivity),mul_one,mul_one]
  rw [hcancel] at hlast
  simpa only [mul_assoc] using hlast

end
end CompoundFeasibility.RestrictedSelectedIndex4
