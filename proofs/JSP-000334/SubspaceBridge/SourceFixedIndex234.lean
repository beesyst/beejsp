import SubspaceBridge.SourceLattice10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFixedArithmetic234
theorem integer_matrix_index_dvd234 {n : ℕ} (G : AddSubgroup (Fin n → ℤ))
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : U.det ≠ 0) (hm : ∀ j, U.col j ∈ G) :
    G.index ∣ U.det.natAbs := by
  classical
  let N := Submodule.span ℤ (Set.range U.col)
  obtain ⟨hf,hi,hd⟩ := integer_span5_index_det (Pi.basisFun ℤ (Fin n)) U.col
    (Matrix.linearIndependent_cols_of_det_ne_zero hU)
  have he : (Pi.basisFun ℤ (Fin n)).toMatrix U.col = U := by ext i j; rfl
  have hiMatrix := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M.det.natAbs) he
  have hi := hi.trans hiMatrix
  letI : N.toAddSubgroup.FiniteIndex := ⟨by rw [hi]; exact Int.natAbs_ne_zero.mpr hU⟩
  have hle : N.toAddSubgroup ≤ G := by
    change N ≤ G.toIntSubmodule
    exact Submodule.span_le.mpr (by rintro _ ⟨j,rfl⟩; exact hm j)
  have hiN : N.toAddSubgroup.index = U.det.natAbs := hi
  rw [← hiN]
  exact AddSubgroup.index_dvd_of_le hle

theorem lattice10_index_dvd234 {n : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin n) (Fin n) ℚ) (D : ℤ) (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0)
    (he : B.map (Int.castRingHom ℚ) = (D : ℚ) • A⁻¹) (hA : IsUnit A)
    (e : Fin n → ℕ) :
    (lattice10 p A e).index ∣ B.det.natAbs * p ^ (∑ i, e i) := by
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
  have h := integer_matrix_index_dvd234 (lattice10 p A e) U hU hm
  rw [hd,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at h
  exact h


theorem intersection_index_dvd234 (H K : AddSubgroup (Fin 10 → ℤ)) :
    (H ⊓ K).index ∣ H.index * K.index := by
  rw [← AddSubgroup.relindex_mul_index (show H ⊓ K ≤ K from inf_le_right),
    AddSubgroup.inf_relindex_right]
  exact mul_dvd_mul_right (AddSubgroup.relindex_dvd_index_of_normal H K) _

theorem source_index_dvd234 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) :
    ∃ C : ℕ, 0 < C ∧ ∀ e2 e3 : Fin 10 → ℕ,
      (sourceLattice10 A2 A3 e2 e3).index ∣ C * 2^(∑ i, e2 i) * 3^(∑ i, e3 i) := by
  obtain ⟨D2,B2,_,hB2,he2⟩ := inverse_integral_frame10 A2 h2
  obtain ⟨D3,B3,_,hB3,he3⟩ := inverse_integral_frame10 A3 h3
  refine ⟨B2.det.natAbs*B3.det.natAbs,
    Nat.mul_pos (Int.natAbs_pos.mpr hB2) (Int.natAbs_pos.mpr hB3),?_⟩
  intro e2 e3
  have hd := (intersection_index_dvd234 (lattice10 2 A2 e2) (lattice10 3 A3 e3)).trans
    (Nat.mul_dvd_mul (lattice10_index_dvd234 2 A2 D2 B2 hB2 he2 h2 e2)
      (lattice10_index_dvd234 3 A3 D3 B3 hB3 he3 h3 e3))
  simpa only [sourceLattice10,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hd

end CompoundFeasibility.SourceFixedArithmetic234
