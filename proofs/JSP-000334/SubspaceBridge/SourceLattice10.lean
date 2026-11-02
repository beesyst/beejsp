import SubspaceBridge.SourceLattice5
open scoped BigOperators Matrix Pointwise
open MeasureTheory Filter
namespace CompoundFeasibility
noncomputable section

def row10 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) : (Fin n → ℤ) →+ ℚ where
  toFun x := (A *ᵥ (fun j => (x j : ℚ))) i
  map_zero' := by
    change (A *ᵥ (0 : Fin n → ℚ)) i = 0
    rw [Matrix.mulVec_zero]
    rfl
  map_add' x y := by
    simp only [Pi.add_apply,Int.cast_add]
    change (A *ᵥ ((fun j => (x j : ℚ)) + (fun j => (y j : ℚ)))) i = _
    rw [Matrix.mulVec_add]
    rfl

def lattice10 {n : ℕ} (p : ℕ) [Fact p.Prime] (A : Matrix (Fin n) (Fin n) ℚ)
    (e : Fin n → ℕ) : AddSubgroup (Fin n → ℤ) :=
  ⨅ i, (normBall p (e i)).comap (row10 A i)

theorem lattice10_spec {n : ℕ} (p : ℕ) [Fact p.Prime] (A : Matrix (Fin n) (Fin n) ℚ)
    (e : Fin n → ℕ) (x : Fin n → ℤ) : x ∈ lattice10 p A e ↔
    ∀ i, padicNorm p ((A *ᵥ (fun j => (x j : ℚ))) i) ≤ (p : ℚ) ^ (-(e i : ℤ)) := by
  simp only [lattice10,AddSubgroup.mem_iInf,AddSubgroup.mem_comap]
  change (∀ i, padicNorm p ((A *ᵥ (fun j => (x j : ℚ))) i) ≤ ((p : ℚ) ^ e i)⁻¹) ↔ _
  simp only [zpow_neg,zpow_natCast]

def sourceLattice10 (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (e₂ e₃ : Fin 10 → ℕ) : AddSubgroup (Fin 10 → ℤ) := lattice10 2 A₂ e₂ ⊓ lattice10 3 A₃ e₃

theorem sourceLattice10_multiple (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (e₂ e₃ : Fin 10 → ℕ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ j : Fin 10, Pi.single j D ∈ sourceLattice10 A₂ A₃ e₂ e₃ := by
  obtain ⟨D₂,h₂,hD₂⟩ := clear_matrix_denominators A₂
  obtain ⟨D₃,h₃,hD₃⟩ := clear_matrix_denominators A₃
  let D : ℤ := D₂ * D₃ * 2 ^ (∑ s, e₂ s) * 3 ^ (∑ s, e₃ s)
  refine ⟨D, by dsimp [D]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero h₂ h₃) (by positivity)) (by positivity), ?_⟩
  intro j
  constructor
  · apply (lattice10_spec 2 A₂ e₂ _).mpr
    have he : D = D₂ * 2 ^ (∑ s, e₂ s) * (D₃ * 3 ^ (∑ s, e₃ s)) := by dsimp [D]; ring
    rw [he]
    exact local_multiple_bounds 2 A₂ e₂ D₂ hD₂ _ j
  · apply (lattice10_spec 3 A₃ e₃ _).mpr
    have he : D = D₃ * 3 ^ (∑ s, e₃ s) * (D₂ * 2 ^ (∑ s, e₂ s)) := by dsimp [D]; ring
    rw [he]
    exact local_multiple_bounds 3 A₃ e₃ D₃ hD₃ _ j

theorem sourceLattice10_has_basis (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (e₂ e₃ : Fin 10 → ℕ) : Nonempty (Basis (Fin 10) ℤ (sourceLattice10 A₂ A₃ e₂ e₃)) := by
  obtain ⟨D,hD,hm⟩ := sourceLattice10_multiple A₂ A₃ e₂ e₃
  exact integer_subgroup_has_basis _ D hD hm

instance sourceLattice10_isZLattice (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (e₂ e₃ : Fin 10 → ℕ) : IsZLattice ℝ (integerRealImage (sourceLattice10 A₂ A₃ e₂ e₃)) where
  span_top := by
    obtain ⟨D,hD,hm⟩ := sourceLattice10_multiple A₂ A₃ e₂ e₃
    exact integerRealImage_span_top _ D hD hm

theorem sourceLattice10_covolume_det (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (e₂ e₃ : Fin 10 → ℕ) (c : Basis (Fin 10) ℤ (sourceLattice10 A₂ A₃ e₂ e₃)) :
    ZLattice.covolume (integerRealImage (sourceLattice10 A₂ A₃ e₂ e₃)) =
      |(Matrix.of (fun j i => ((c j : Fin 10 → ℤ) i : ℝ))).det| :=
  integerRealImage_covolume_det _ c

theorem sourceLattice10_covolume_index (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (e₂ e₃ : Fin 10 → ℕ) :
    ZLattice.covolume (integerRealImage (sourceLattice10 A₂ A₃ e₂ e₃)) =
      ((sourceLattice10 A₂ A₃ e₂ e₃).index : ℝ) := by
  obtain ⟨c⟩ := sourceLattice10_has_basis A₂ A₃ e₂ e₃
  exact integerRealImage_covolume_index _ c

theorem inverse_integral_frame10 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsUnit A) :
    ∃ (D : ℤ) (B : Matrix (Fin n) (Fin n) ℤ), D ≠ 0 ∧ B.det ≠ 0 ∧
      B.map (Int.castRingHom ℚ) = (D : ℚ) • A⁻¹ := by
  classical
  obtain ⟨D,hD,hm⟩ := clear_matrix_denominators A⁻¹
  choose b hB using hm
  let B : Matrix (Fin n) (Fin n) ℤ := b
  have he : (B : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℚ) = (D : ℚ) • A⁻¹ := by
    ext i j
    exact hB i j
  refine ⟨D,B,hD,?_,he⟩
  have hd : ((B : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [he, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hD))
      (inv_ne_zero (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hA)))
  intro h
  apply hd
  rw [← integer_matrix_det_cast, h, Int.cast_zero]

theorem lattice10_index_upper {n : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin n) (Fin n) ℚ) (D : ℤ) (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0)
    (he : B.map (Int.castRingHom ℚ) = (D : ℚ) • A⁻¹) (hA : IsUnit A)
    (e : Fin n → ℕ) :
    (lattice10 p A e).index ≤ B.det.natAbs * p ^ (∑ i, e i) := by
  classical
  let U := B * Matrix.diagonal (fun i => (p : ℤ) ^ e i)
  have hd : U.det = B.det * (p : ℤ) ^ (∑ i, e i) := by
    rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hU : U.det ≠ 0 := by rw [hd]; exact mul_ne_zero hB (pow_ne_zero _ (by exact_mod_cast hp))
  have hm (j : Fin n) : U.col j ∈ lattice10 p A e := by
    apply (lattice10_spec p A e _).mpr
    have hcol : (fun k => (U.col j k : ℚ)) =
        (p : ℚ) ^ e j • (B.map (Int.castRingHom ℚ)).col j := by
      ext k
      simp [U,Matrix.mul_diagonal,Matrix.col_apply,smul_eq_mul,mul_comm]
    have hmul : A * B.map (Int.castRingHom ℚ) = (D : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
      rw [he,Matrix.mul_smul,Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)]
    have hact : A *ᵥ (B.map (Int.castRingHom ℚ)).col j =
        ((D : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ)).col j := by
      change (A * B.map (Int.castRingHom ℚ)).col j = _
      rw [hmul]
    intro i
    rw [hcol,Matrix.mulVec_smul,hact]
    by_cases hij : i = j
    · subst i
      simp only [Pi.smul_apply,smul_eq_mul,Matrix.col_apply,Matrix.smul_apply,Matrix.one_apply_eq,mul_one]
      rw [show (p : ℚ) ^ e j * (D : ℚ) = (((p : ℤ) ^ e j * D : ℤ) : ℚ) by push_cast; ring]
      apply padicNorm.dvd_iff_norm_le.mp
      exact_mod_cast (dvd_mul_right ((p : ℤ) ^ e j) D)
    · simp [Matrix.col_apply,Matrix.one_apply,hij,Ne.symm hij]
  have h := integer_matrix_index_upper5 (lattice10 p A e) U hU hm
  rw [hd,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at h
  exact h

theorem sourceLattice10_uniform_index_upper (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) :
    ∃ K : ℕ, 0 < K ∧ ∀ e₂ e₃ : Fin 10 → ℕ,
      (sourceLattice10 A₂ A₃ e₂ e₃).index ≤
        K * 2 ^ (∑ i, e₂ i) * 3 ^ (∑ i, e₃ i) := by
  obtain ⟨D₂,B₂,hD₂,hB₂,he₂⟩ := inverse_integral_frame10 A₂ h₂
  obtain ⟨D₃,B₃,hD₃,hB₃,he₃⟩ := inverse_integral_frame10 A₃ h₃
  refine ⟨B₂.det.natAbs * B₃.det.natAbs,
    Nat.mul_pos (Int.natAbs_pos.mpr hB₂) (Int.natAbs_pos.mpr hB₃),?_⟩
  intro e₂ e₃
  have h2 := lattice10_index_upper 2 A₂ D₂ B₂ hB₂ he₂ h₂ e₂
  have h3 := lattice10_index_upper 3 A₃ D₃ B₃ hB₃ he₃ h₃ e₃
  have h := (AddSubgroup.index_inf_le (H := lattice10 2 A₂ e₂) (K := lattice10 3 A₃ e₃)).trans
    (Nat.mul_le_mul h2 h3)
  simpa only [sourceLattice10, Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h

theorem q_prime_powers_product_upper10 (p : ℕ) (hp : 1 < p)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin 10 → ℝ) (hc : ∀ i, c i ≤ 0) :
    (p : ℝ) ^ (∑ i, Nat.ceil (JSP000334.qThreshold p Q (c i))) ≤
      (p : ℝ) ^ 10 * ∏ i, Q ^ (-c i) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_trans Nat.zero_lt_one hp)
  have hstep (i : Fin 10) :
      (p : ℝ) ^ Nat.ceil (JSP000334.qThreshold p Q (c i)) ≤ (p : ℝ) * Q ^ (-c i) := by
    rw [← JSP000334.qThreshold_rpow p hp Q (c i) hQ, ← Real.rpow_natCast]
    calc
      _ ≤ (p : ℝ) ^ (JSP000334.qThreshold p Q (c i) + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.le)
          (Nat.ceil_lt_add_one (JSP000334.qThreshold_nonneg p hp Q (c i) hQ (hc i))).le
      _ = _ := by rw [Real.rpow_add hp0,Real.rpow_one]; ring
  rw [← Finset.prod_pow_eq_pow_sum]
  have h := Finset.prod_le_prod (s := Finset.univ) (fun i _ => pow_nonneg hp0.le _) (fun i _ => hstep i)
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h

theorem q_prime_powers_normalized_upper10 (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 10 → ℝ) (h₂ : ∀ i, c₂ i ≤ 0) (h₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    (2 : ℝ) ^ (∑ i, Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))) *
      3 ^ (∑ i, Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))) ≤
      60466176 * ∏ i, Q ^ c₀ i := by
  have hQ0 := lt_trans zero_lt_one hQ
  have hprod : (∏ i, Q ^ (-c₂ i)) * (∏ i, Q ^ (-c₃ i)) = ∏ i, Q ^ c₀ i := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [← Real.rpow_add hQ0]
    rw [← Real.rpow_sum_of_pos hQ0 _ Finset.univ, ← Real.rpow_sum_of_pos hQ0 _ Finset.univ]
    congr 1
    simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib] at hb ⊢
    linarith
  have h := mul_le_mul (q_prime_powers_product_upper10 2 (by decide) Q hQ c₂ h₂)
    (q_prime_powers_product_upper10 3 (by decide) Q hQ c₃ h₃)
    (by positivity) (by positivity)
  calc
    _ ≤ ((2 : ℝ) ^ 10 * ∏ i, Q ^ (-c₂ i)) * (3 ^ 10 * ∏ i, Q ^ (-c₃ i)) := h
    _ = ((2 : ℝ) ^ 10 * 3 ^ 10) * ((∏ i, Q ^ (-c₂ i)) * ∏ i, Q ^ (-c₃ i)) := by ring
    _ = _ := by rw [hprod]; norm_num

theorem sourceLattice10_uniform_normalized_covolume_upper
    (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) :
    ∃ K : ℕ, 0 < K ∧ ∀ (Q : ℝ), 1 < Q → ∀ c₀ c₂ c₃ : Fin 10 → ℝ,
      (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) →
      (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
      ZLattice.covolume (integerRealImage (sourceLattice10 A₂ A₃
        (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
        (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))))) /
        (∏ i, Q ^ c₀ i) ≤ (K : ℝ) * 60466176 := by
  obtain ⟨K,hK,hindex⟩ := sourceLattice10_uniform_index_upper A₂ A₃ h₂ h₃
  refine ⟨K,hK,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
  have hW : 0 < ∏ i, Q ^ c₀ i := Finset.prod_pos
    (fun i _ => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
  apply (div_le_iff₀ hW).mpr
  rw [sourceLattice10_covolume_index]
  have hi := hindex (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
  have hiR : (((sourceLattice10 A₂ A₃
      (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
      (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))))).index : ℝ) ≤
      (K : ℝ) * 2 ^ (∑ i, Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))) *
        3 ^ (∑ i, Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))) := by exact_mod_cast hi
  have hn := mul_le_mul_of_nonneg_left (q_prime_powers_normalized_upper10 Q hQ c₀ c₂ c₃ hc₂ hc₃ hb)
    (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
  exact hiR.trans (by simpa only [mul_assoc] using hn)


end
end CompoundFeasibility
