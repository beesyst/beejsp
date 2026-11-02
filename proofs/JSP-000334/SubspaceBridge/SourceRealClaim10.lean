import SubspaceBridge.SourceBalance10
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary10.SourceBalance10
open SourceMultiblock10 SourceNormalHighIndex10 SourceExpansion10 SourceSupport10

theorem source_real_reconstruction10 {m : ℕ} (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : L.det = 1) (J : Vars10 m →₀ ℕ) (P : MvPolynomial (Vars10 m) ℤ) :
    substitution L (expansion L J P) = derivative10 J (P.map (Int.castRingHom ℝ)) := by
  rw [expansion, substitution_comp, OriginalDual10.inverse_adjugate_fin10 L hL,
    Matrix.adjugate_mul, hL, one_smul, substitution_one]

theorem coefficient_zero_of_unit10 {F : Type*} [Field F] [CharZero F]
    {m : ℕ} (L : Matrix (Fin 10) (Fin 10) F) (hL : IsUnit L)
    (r : Fin m → ℕ) (eta : ℝ) (P : MvPolynomial (Vars10 m) ℤ)
    (hi : matrixIndex10 L r eta P) (i : Fin 10) (J b : Vars10 m →₀ ℕ)
    (hb : rothSourceDerivativeWeight r J + coordinateWeight r i b < (1/10-eta)*m) :
    (expansion L J P).coeff b = 0 := by
  have hd : L.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det L).mp hL).ne_zero
  have hn : ∃ p, L i p ≠ 0 := by
    by_contra! hh
    exact hd (Matrix.det_eq_zero_of_row_eq_zero i hh)
  obtain ⟨p,hp⟩ := hn
  apply coeff_zero_below_index r L hd i p hp ((1/10-eta)*m) P
  · intro D hD
    exact hi i D hD (fun _ => p) (fun _ => hp)
  · exact hb

theorem source_real_coefficient_zero10 {m : ℕ} (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : L.det = 1) (r : Fin m → ℕ) (eta : ℝ)
    (P : MvPolynomial (Vars10 m) ℤ) (hi : matrixIndex10 L r eta P)
    (i : Fin 10) (J b : Vars10 m →₀ ℕ)
    (hb : rothSourceDerivativeWeight r J + coordinateWeight r i b < (1/10-eta)*m) :
    (expansion L J P).coeff b = 0 := by
  let u : (Matrix (Fin 10) (Fin 10) ℝ)ˣ :=
    ⟨L,L.adjugate,by rw [Matrix.mul_adjugate,hL,one_smul],
      by rw [Matrix.adjugate_mul,hL,one_smul]⟩
  have hu : IsUnit L := ⟨u,rfl⟩
  exact coefficient_zero_of_unit10 L hu r eta P hi i J b hb

theorem source_real_block_degree10 {m : ℕ} (L : Matrix (Fin 10) (Fin 10) ℝ)
    (r : Fin m → ℕ) (P : MvPolynomial (Vars10 m) ℤ) (hhom : homogeneous10 r P)
    (J b : Vars10 m →₀ ℕ) (hb : (expansion L J P).coeff b ≠ 0) (h : Fin m) :
    (∑ j : Fin 10, b (h,j)) = r h - ∑ j : Fin 10, J (h,j) := by
  exact expansion_block_degree r L J P hhom b hb h

theorem source_real_total_weight10 {m : ℕ} (L : Matrix (Fin 10) (Fin 10) ℝ)
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars10 m) ℤ) (hhom : homogeneous10 r P)
    (J b : Vars10 m →₀ ℕ) (hb : (expansion L J P).coeff b ≠ 0) :
    (∑ i : Fin 10, coordinateWeight r i b) ≤ (m : ℝ) := by
  exact total_coordinate_weight_le r hr L J P hhom b hb

theorem source_real_balanced_support10 {m : ℕ} (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : L.det = 1) (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (P : MvPolynomial (Vars10 m) ℤ)
    (hhom : homogeneous10 r P) (hi : matrixIndex10 L r eta P)
    (J b : Vars10 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m)
    (hb : (expansion L J P).coeff b ≠ 0) :
    ∀ i, |coordinateWeight r i b - (m : ℝ)/10| ≤ 54*eta*m := by
  exact balanced_of_vanishing r hr eta heta L P hhom
    (source_real_coefficient_zero10 L hL r eta P hi) J b hJ hb

theorem source_real_claim10 {m : ℕ} (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : L.det = 1) (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (P : MvPolynomial (Vars10 m) ℤ)
    (hhom : homogeneous10 r P) (hi : matrixIndex10 L r eta P) :
    Claims r eta L P := by
  exact ⟨fun J => source_real_reconstruction10 L hL J P,
    source_real_coefficient_zero10 L hL r eta P hi,
    fun J b hb h => source_real_block_degree10 L r P hhom J b hb h,
    fun J b hb => source_real_total_weight10 L r hr P hhom J b hb,
    fun J b hJ hb => source_real_balanced_support10 L hL r hr eta heta P hhom hi J b hJ hb⟩

theorem claims_of_unit10 {F : Type*} [Field F] [CharZero F]
    {m : ℕ} (B : Matrix (Fin 10) (Fin 10) F) (hB : IsUnit B)
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta)
    (P : MvPolynomial (Vars10 m) ℤ) (hhom : homogeneous10 r P)
    (hi : matrixIndex10 B r eta P) : Claims r eta B P := by
  have hd : B.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det B).mp hB).ne_zero
  apply claims_of_charts r hr eta heta B hd P hhom
  intro i J hJ k hk
  exact hi i J hJ (fun _ => k) (fun _ => hk)

end CompoundFeasibility.Auxiliary10.SourceBalance10
