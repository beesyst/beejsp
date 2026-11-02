import SubspaceBridge.BinaryKernelNonvanishing2
import SubspaceBridge.AuxiliaryLocalExpansion
open scoped BigOperators Classical
namespace JSP000334
noncomputable def binaryLocalRationalMatrix (L : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix (Fin 2) (Fin 2) ℚ := fun i j => (L i j : ℚ)

noncomputable def binaryLocalLinearChart {m : ℕ} (B : Matrix (Fin 2) (Fin 2) ℚ)
    (u : RothBlockVars2 m) : MvPolynomial (RothBlockVars2 m) ℚ :=
  ∑ i : Fin 2, MvPolynomial.C (B u.2 i) * MvPolynomial.X (u.1,i)

noncomputable def binaryLocalSubstitution {m : ℕ} (B : Matrix (Fin 2) (Fin 2) ℚ) :
    MvPolynomial (RothBlockVars2 m) ℚ →+* MvPolynomial (RothBlockVars2 m) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (binaryLocalLinearChart B)

noncomputable def binaryLocalExpansion {m : ℕ} (L : Matrix (Fin 2) (Fin 2) ℤ)
    (J : RothBlockVars2 m →₀ ℕ) (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    MvPolynomial (RothBlockVars2 m) ℚ :=
  MvPolynomial.eval₂Hom (Int.castRingHom _)
    (binaryLocalLinearChart (binaryLocalRationalMatrix L)⁻¹)
    (binaryDividedDerivative J P)

theorem binaryLocal_chart_one {m : ℕ} (u : RothBlockVars2 m) :
    binaryLocalLinearChart (1 : Matrix (Fin 2) (Fin 2) ℚ) u = MvPolynomial.X u := by
  simp [binaryLocalLinearChart, Matrix.one_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem binaryLocal_chart_comp {m : ℕ} (A B : Matrix (Fin 2) (Fin 2) ℚ)
    (u : RothBlockVars2 m) :
    binaryLocalSubstitution A (binaryLocalLinearChart B u) = binaryLocalLinearChart (B * A) u := by
  classical
  simp only [binaryLocalLinearChart, binaryLocalSubstitution, map_sum, map_mul,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.mul_apply]
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul]
  ring

theorem binaryLocal_expansion_reconstruct {m : ℕ} (L : Matrix (Fin 2) (Fin 2) ℤ)
    (hL : (binaryLocalRationalMatrix L).det ≠ 0) (J : RothBlockVars2 m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    binaryLocalSubstitution (binaryLocalRationalMatrix L) (binaryLocalExpansion L J P) =
      MvPolynomial.map (Int.castRingHom ℚ) (binaryDividedDerivative J P) := by
  classical
  have hinv := Matrix.nonsing_inv_mul (binaryLocalRationalMatrix L) (isUnit_iff_ne_zero.mpr hL)
  have he : (binaryLocalSubstitution (m := m) (binaryLocalRationalMatrix L)).comp
      (MvPolynomial.eval₂Hom (Int.castRingHom _)
        (binaryLocalLinearChart (binaryLocalRationalMatrix L)⁻¹)) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [binaryLocalSubstitution]
    · intro u
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [binaryLocal_chart_comp, hinv, binaryLocal_chart_one]
      simp
  exact congrArg (fun f => f (binaryDividedDerivative J P)) he

theorem binaryLocal_chart_pderiv {m : ℕ} (B : Matrix (Fin 2) (Fin 2) ℚ)
    (h : Fin m) (i : Fin 2) (u : RothBlockVars2 m) :
    MvPolynomial.pderiv (h,i) (binaryLocalLinearChart B u) =
      if u.1 = h then MvPolynomial.C (B u.2 i) else 0 := by
  classical
  rcases u with ⟨g,j⟩
  by_cases hg : g = h
  · subst g
    fin_cases i <;> simp [binaryLocalLinearChart, map_sum, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
      Pi.single_apply, Prod.mk.injEq, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  · simp [binaryLocalLinearChart, map_sum, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
      Pi.single_apply, Prod.mk.injEq, hg, Ne.symm hg]

theorem binaryLocal_substitution_one {m : ℕ} (P : MvPolynomial (RothBlockVars2 m) ℚ) :
    binaryLocalSubstitution (1 : Matrix (Fin 2) (Fin 2) ℚ) P = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [binaryLocalSubstitution]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P u hP =>
    rw [map_mul, hP]
    simp [binaryLocalSubstitution, binaryLocal_chart_one]

theorem binaryLocal_substitution_comp {m : ℕ} (A B : Matrix (Fin 2) (Fin 2) ℚ)
    (P : MvPolynomial (RothBlockVars2 m) ℚ) :
    binaryLocalSubstitution A (binaryLocalSubstitution B P) = binaryLocalSubstitution (B * A) P := by
  have he : (binaryLocalSubstitution (m := m) A).comp (binaryLocalSubstitution B) =
      binaryLocalSubstitution (B * A) := by
    apply MvPolynomial.ringHom_ext
    · intro q
      simp [binaryLocalSubstitution]
    · intro u
      simp only [RingHom.comp_apply, binaryLocalSubstitution, MvPolynomial.eval₂Hom_X']
      exact binaryLocal_chart_comp A B u
  exact congrArg (fun f => f P) he

theorem binaryLocal_substitution_injective {m : ℕ} (M : Matrix (Fin 2) (Fin 2) ℚ)
    (hM : M.det ≠ 0) : Function.Injective (binaryLocalSubstitution (m := m) M) := by
  intro P Q h
  have he := congrArg (binaryLocalSubstitution M⁻¹) h
  rw [binaryLocal_substitution_comp, binaryLocal_substitution_comp,
    Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),
    binaryLocal_substitution_one, binaryLocal_substitution_one] at he
  exact he

theorem binaryLocal_expansion_unique {m : ℕ} (L : Matrix (Fin 2) (Fin 2) ℤ)
    (hL : (binaryLocalRationalMatrix L).det ≠ 0) (J : RothBlockVars2 m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (Q : MvPolynomial (RothBlockVars2 m) ℚ)
    (hQ : binaryLocalSubstitution (binaryLocalRationalMatrix L) Q =
      MvPolynomial.map (Int.castRingHom ℚ) (binaryDividedDerivative J P)) :
    Q = binaryLocalExpansion L J P := by
  apply binaryLocal_substitution_injective (binaryLocalRationalMatrix L) hL
  exact hQ.trans (binaryLocal_expansion_reconstruct L hL J P).symm

theorem binaryLocal_substitution_chain {m : ℕ} (B : Matrix (Fin 2) (Fin 2) ℚ)
    (h : Fin m) (i : Fin 2) (P : MvPolynomial (RothBlockVars2 m) ℚ) :
    MvPolynomial.pderiv (h,i) (binaryLocalSubstitution B P) =
      ∑ j : Fin 2, MvPolynomial.C (B j i) *
        binaryLocalSubstitution B (MvPolynomial.pderiv (h,j) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [binaryLocalSubstitution]
  | add P Q hP hQ => simp only [map_add, hP, hQ, mul_add, Finset.sum_add_distrib]
  | mul_X P u hP =>
    have hdelta : (∑ j : Fin 2, (MvPolynomial.C (B j i) * binaryLocalSubstitution B P) *
        (if (h,j) = u then 1 else 0)) =
        binaryLocalSubstitution B P * (if u.1 = h then MvPolynomial.C (B u.2 i) else 0) := by
      rcases u with ⟨g,l⟩
      by_cases hg : g = h
      · subst g
        simp [Prod.mk.injEq, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]
      · simp [Prod.mk.injEq, hg, Ne.symm hg]
    have hX : binaryLocalSubstitution B (MvPolynomial.X u) = binaryLocalLinearChart B u := by
      simp [binaryLocalSubstitution]
    have hD (j : Fin 2) :
        binaryLocalSubstitution B (MvPolynomial.pderiv (h,j) (P * MvPolynomial.X u)) =
          binaryLocalSubstitution B (MvPolynomial.pderiv (h,j) P) * binaryLocalLinearChart B u +
          binaryLocalSubstitution B P * (if (h,j) = u then 1 else 0) := by
      by_cases he : (h,j) = u <;>
        simp [MvPolynomial.pderiv_mul, hX, MvPolynomial.pderiv_X, Pi.single_apply, he, eq_comm] <;> ring
    rw [map_mul, MvPolynomial.pderiv_mul, hP, hX, binaryLocal_chart_pderiv]
    simp_rw [hD, mul_add, ← mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hdelta]

end JSP000334
