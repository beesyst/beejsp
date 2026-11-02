import SubspaceBridge.RestrictedLower5
open scoped BigOperators Matrix
noncomputable section
namespace CompoundFeasibility.RestrictedSelectedIndex5

theorem selected_rational_index_lower5 (n : ℕ)
    (B₂ B₃ : Matrix (Fin n) (Fin n) ℚ)
    (G : AddSubgroup (Fin n → ℤ)) (b : Basis (Fin n) ℤ G)
    (e₂ e₃ : Fin n → ℕ)
    (h₂ : ∀ (x : G) i, padicNorm 2 ((B₂ *ᵥ (fun k => ((x : Fin n → ℤ) k : ℚ))) i) ≤
      (2 : ℚ)^(-(e₂ i : ℤ)))
    (h₃ : ∀ (x : G) i, padicNorm 3 ((B₃ *ᵥ (fun k => ((x : Fin n → ℤ) k : ℚ))) i) ≤
      (3 : ℚ)^(-(e₃ i : ℤ))) :
    (padicNorm 2 B₂.det : ℝ) * (padicNorm 3 B₃.det : ℝ) *
      (2 : ℝ)^(∑ i, e₂ i) * (3 : ℝ)^(∑ i, e₃ i) ≤ (G.index : ℝ) := by
  let U : Matrix (Fin n) (Fin n) ℤ := fun k i => (b k : Fin n → ℤ) i
  have hli : LinearIndependent ℤ (fun k => (b k : Fin n → ℤ)) :=
    b.linearIndependent.map' G.toIntSubmodule.subtype (Submodule.ker_subtype _)
  have hUne : U.det ≠ 0 := by
    have h := (SourceRelativeIndex6.integer_span_index_det (Pi.basisFun ℤ (Fin n)) _ hli).2.2
    change U.transpose.det ≠ 0 at h
    simpa using h
  have hUR : (U.map (Int.castRingHom ℝ)).det ≠ 0 := by
    rw [← integer_matrix_det_cast]
    exact_mod_cast hUne
  have hreal := Matrix.linearIndependent_rows_of_det_ne_zero hUR
  have hindex : |(U.map (Int.castRingHom ℝ)).det| = (G.index : ℝ) := by
    have h := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin n)) G b
    rw [Basis.det_apply] at h
    have he : (Pi.basisFun ℤ (Fin n)).toMatrix (fun k => (b k : Fin n → ℤ)) = U.transpose := by rfl
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


theorem selected_prime_powers_lower5 {d : ℕ} (p : ℕ) (hp : 1 < p)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin d → ℝ) :
    Q^(-(∑ k, c k)) ≤ (p : ℝ)^(∑ k, Nat.ceil (JSP000334.qThreshold p Q (c k))) := by
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  calc
    _ = ∏ k, Q^(-c k) := by
      rw [← Real.rpow_sum_of_pos hQpos]
      simp
    _ ≤ ∏ k, (p : ℝ)^Nat.ceil (JSP000334.qThreshold p Q (c k)) := by
      apply Finset.prod_le_prod (fun _ _ => (Real.rpow_pos_of_pos hQpos _).le)
      intro k hk
      rw [← JSP000334.qThreshold_rpow p hp Q (c k) hQ,← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.le) (Nat.le_ceil _)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _


end CompoundFeasibility.RestrictedSelectedIndex5
