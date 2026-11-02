import SubspaceBridge.SchlickeweiSatz51Selected6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiAuxiliaryDual6
open SourceReadiness6 SourceMixed6 SourceWeights SchlickeweiDualVanishing6
open SchlickeweiEquation4116 SchlickeweiSatz51Selected6
theorem integer_matrix_index_upper6 (G : AddSubgroup (Fin 6 → ℤ))
    (U : Matrix (Fin 6) (Fin 6) ℤ) (hU : U.det ≠ 0) (hm : ∀ j, U.col j ∈ G) :
    G.index ≤ U.det.natAbs := by
  classical
  let N := Submodule.span ℤ (Set.range U.col)
  obtain ⟨hf,hi,hd⟩ := SourceRelativeIndex6.integer_span6_index_det (Pi.basisFun ℤ (Fin 6)) U.col
    (Matrix.linearIndependent_cols_of_det_ne_zero hU)
  have he : (Pi.basisFun ℤ (Fin 6)).toMatrix U.col = U := by ext i j; rfl
  have hi2 : N.toAddSubgroup.index = U.det.natAbs :=
    hi.trans (congrArg (fun M : Matrix (Fin 6) (Fin 6) ℤ => M.det.natAbs) he)
  letI : N.toAddSubgroup.FiniteIndex :=
    ⟨fun hz => (Int.natAbs_ne_zero.mpr hU) (hi2.symm.trans hz)⟩
  have hle : N.toAddSubgroup ≤ G := by
    change N ≤ G.toIntSubmodule
    exact Submodule.span_le.mpr (by rintro _ ⟨j,rfl⟩; exact hm j)
  exact (AddSubgroup.index_antitone hle).trans_eq hi2

theorem inverse_integral_frame6 (A : Matrix (Fin 6) (Fin 6) ℚ) (hA : IsUnit A) :
    ∃ (D : ℤ) (B : Matrix (Fin 6) (Fin 6) ℤ), D ≠ 0 ∧ B.det ≠ 0 ∧
      B.map (Int.castRingHom ℚ) = (D : ℚ) • A⁻¹ := by
  classical
  obtain ⟨D,hD,hm⟩ := clear_matrix_denominators A⁻¹
  choose b hB using hm
  let B : Matrix (Fin 6) (Fin 6) ℤ := b
  have he : (B : Matrix (Fin 6) (Fin 6) ℤ).map (Int.castRingHom ℚ) = (D : ℚ) • A⁻¹ := by
    ext i j
    exact hB i j
  refine ⟨D,B,hD,?_,he⟩
  have hd : ((B : Matrix (Fin 6) (Fin 6) ℤ).map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [he, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hD))
      (inv_ne_zero (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hA)))
  intro h
  apply hd
  rw [← integer_matrix_det_cast, h, Int.cast_zero]

theorem directLocal_index_upper6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (D : ℤ) (B : Matrix (Fin 6) (Fin 6) ℤ)
    (hB : B.det ≠ 0)
    (he : B.map (Int.castRingHom ℚ) = (D : ℚ) • (compound A)⁻¹) (hA : IsUnit (compound A))
    (a : Fin 4 → ℝ) :
    (directLocal42 p A a).index ≤ B.det.natAbs * p ^ (∑ i : Fin 6, Nat.ceil (a (lo i) + a (hi i))) := by
  classical
  let e : Fin 6 → ℕ := fun i => Nat.ceil (a (lo i) + a (hi i))
  let U := B * Matrix.diagonal (fun i => (p : ℤ) ^ e i)
  have hd : U.det = B.det * (p : ℤ) ^ (∑ i, e i) := by
    rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hU : U.det ≠ 0 := by rw [hd]; exact mul_ne_zero hB (pow_ne_zero _ (by exact_mod_cast hp))
  have hm (j : Fin 6) : U.col j ∈ directLocal42 p A a := by
    apply (directLocal42_spec p A a _).mpr
    have hcol : (fun k => (U.col j k : ℚ)) =
        (p : ℚ) ^ e j • (B.map (Int.castRingHom ℚ)).col j := by
      ext k
      simp [U,Matrix.mul_diagonal,Matrix.col_apply,smul_eq_mul,mul_comm]
    have hmul : compound A * B.map (Int.castRingHom ℚ) = (D : ℚ) • (1 : Matrix (Fin 6) (Fin 6) ℚ) := by
      rw [he,Matrix.mul_smul,Matrix.mul_nonsing_inv (compound A) ((Matrix.isUnit_iff_isUnit_det (compound A)).mp hA)]
    have hact : compound A *ᵥ (B.map (Int.castRingHom ℚ)).col j =
        ((D : ℚ) • (1 : Matrix (Fin 6) (Fin 6) ℚ)).col j := by
      change (compound A * B.map (Int.castRingHom ℚ)).col j = _
      rw [hmul]
    intro i
    rw [hcol,Matrix.mulVec_smul,hact]
    by_cases hij : i = j
    · subst i
      simp only [Pi.smul_apply,smul_eq_mul,Matrix.col_apply,Matrix.smul_apply,Matrix.one_apply_eq,mul_one]
      rw [show (p : ℚ) ^ e j * (D : ℚ) = (((p : ℤ) ^ e j * D : ℤ) : ℚ) by push_cast; ring]
      have hh := (padicNorm.dvd_iff_norm_le (p := p) (n := e j)
        (z := (p : ℤ) ^ e j * D)).mp (by
          exact_mod_cast (dvd_mul_right ((p : ℤ) ^ e j) D))
      simpa only [zpow_neg, zpow_natCast, e] using hh
    · simp [Matrix.col_apply,Matrix.one_apply,hij,Ne.symm hij]
  have h := integer_matrix_index_upper6 (directLocal42 p A a) U hU hm
  rw [hd,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at h
  exact h



theorem direct_uniform_index_upper6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) :
    ∃ K : ℕ, 0 < K ∧ ∀ (q : ℝ) (c2 c3 : Fin 4 → ℝ),
      (directCompoundGroup42 A2 A3 q c2 c3).index ≤
        K * 2 ^ (∑ i : Fin 6, Nat.ceil (JSP000334.qThreshold 2 q (pairWeights42 c2 i))) *
          3 ^ (∑ i : Fin 6, Nat.ceil (JSP000334.qThreshold 3 q (pairWeights42 c3 i))) := by
  have hu2 : IsUnit (compound A2) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (by rw [compound42_det_one A2 h2]; exact isUnit_one)
  have hu3 : IsUnit (compound A3) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (by rw [compound42_det_one A3 h3]; exact isUnit_one)
  obtain ⟨D2,B2,_,hb2,he2⟩ := inverse_integral_frame6 (compound A2) hu2
  obtain ⟨D3,B3,_,hb3,he3⟩ := inverse_integral_frame6 (compound A3) hu3
  refine ⟨B2.det.natAbs * B3.det.natAbs,
    Nat.mul_pos (Int.natAbs_pos.mpr hb2) (Int.natAbs_pos.mpr hb3), ?_⟩
  intro q c2 c3
  have hi2 := directLocal_index_upper6 2 A2 D2 B2 hb2 he2 hu2
    (fun i => JSP000334.qThreshold 2 q (c2 i))
  have hi3 := directLocal_index_upper6 3 A3 D3 B3 hb3 he3 hu3
    (fun i => JSP000334.qThreshold 3 q (c3 i))
  have h := (AddSubgroup.index_inf_le
    (H := directLocal42 2 A2 (fun i => JSP000334.qThreshold 2 q (c2 i)))
    (K := directLocal42 3 A3 (fun i => JSP000334.qThreshold 3 q (c3 i)))).trans
      (Nat.mul_le_mul hi2 hi3)
  simpa only [directCompoundGroup42, pairWeights42, qThreshold_add42,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

def primeProduct6 (q : ℝ) (c2 c3 : Fin 4 → ℝ) : ℕ :=
  2 ^ (∑ i : Fin 6, Nat.ceil (JSP000334.qThreshold 2 q (pairWeights42 c2 i))) *
    3 ^ (∑ i : Fin 6, Nat.ceil (JSP000334.qThreshold 3 q (pairWeights42 c3 i)))

theorem primeProduct_pos6 (q : ℝ) (c2 c3 : Fin 4 → ℝ) :
    0 < primeProduct6 q c2 c3 := by
  unfold primeProduct6
  positivity

theorem direct_uniform_covolume_upper6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ) (c2 c3 : Fin 4 → ℝ),
      ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q c2 c3)) ≤
        C * (primeProduct6 q c2 c3 : ℝ) := by
  obtain ⟨K,hK,h⟩ := direct_uniform_index_upper6 A2 A3 h2 h3
  refine ⟨K, by exact_mod_cast hK, ?_⟩
  intro q c2 c3
  obtain ⟨b⟩ := directCompoundGroup42_has_basis A2 A3 q c2 c3
  rw [integerRealImage_covolume_index _ b]
  have hi := h q c2 c3
  change _ ≤ (K : ℝ) * ((2 ^ _ * 3 ^ _ : ℕ) : ℝ)
  exact_mod_cast (show (directCompoundGroup42 A2 A3 q c2 c3).index ≤
    K * (2 ^ _ * 3 ^ _ : ℕ) by simpa only [Nat.mul_assoc] using hi)

end CompoundFeasibility.SchlickeweiAuxiliaryDual6
