import SubspaceBridge.BinaryAuxCount2
import SubspaceBridge.AuxiliaryMatrix
open scoped BigOperators Classical
namespace JSP000334

abbrev RothBlockVars2 (m : ℕ) := Fin m × Fin 2

noncomputable def binaryAuxExponent {m : ℕ} {r : Fin m → ℕ}
    (b : BinaryAuxCoefficients r) : RothBlockVars2 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.2 = 0 then (b u.1).val else r u.1-(b u.1).val)

noncomputable def binaryAuxPolynomial {m : ℕ} {r : Fin m → ℕ}
    (c : BinaryAuxCoefficients r → ℤ) : MvPolynomial (RothBlockVars2 m) ℤ :=
  ∑ b, MvPolynomial.monomial (binaryAuxExponent b) (c b)

def binaryBlockHomogeneous {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) : Prop :=
  ∀ e ∈ P.support, ∀ h, ∑ j : Fin 2, e (h,j) = r h

noncomputable def binaryDividedDerivative {m : ℕ} (J : RothBlockVars2 m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) : MvPolynomial (RothBlockVars2 m) ℤ :=
  P.sum (fun e c => MvPolynomial.monomial (e-J)
    (c*∏ u : RothBlockVars2 m, (Nat.choose (e u) (J u) : ℤ)))

noncomputable def binaryScaledChart {m : ℕ} (a : Fin 2 → ℤ) (k : Fin 2)
    (u : RothBlockVars2 m) : MvPolynomial (RothBlockVars2 m) ℤ :=
  if u.2 = k then MvPolynomial.C (-a k.rev)*MvPolynomial.X (u.1,k.rev)
  else MvPolynomial.C (a k)*MvPolynomial.X u

noncomputable def binaryScaledSubstitution {m : ℕ} (a : Fin 2 → ℤ) (k : Fin 2) :
    MvPolynomial (RothBlockVars2 m) ℤ →+* MvPolynomial (RothBlockVars2 m) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (binaryScaledChart a k)

noncomputable def binaryPivotDerivative {m : ℕ} (k : Fin 2) (i : Fin m → ℕ) : RothBlockVars2 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.2 = k then i u.1 else 0)

noncomputable def binaryFreeExponent {m : ℕ} (k : Fin 2) (s : Fin m → ℕ) : RothBlockVars2 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.2 = k then 0 else s u.1)

theorem binary_exponent_block {m : ℕ} {r : Fin m → ℕ} (b : BinaryAuxCoefficients r) (h : Fin m) :
    (∑ j : Fin 2, binaryAuxExponent b (h,j)) = r h := by
  simp [binaryAuxExponent, Fin.sum_univ_two]
  have hi := (b h).isLt
  omega

theorem binary_exponent_injective {m : ℕ} (r : Fin m → ℕ) :
    Function.Injective (@binaryAuxExponent m r) := by
  intro b c he
  funext h
  apply Fin.ext
  have hh := congrArg (fun e : RothBlockVars2 m →₀ ℕ => e (h,0)) he
  simpa [binaryAuxExponent] using hh

theorem binary_polynomial_coeff {m : ℕ} {r : Fin m → ℕ}
    (c : BinaryAuxCoefficients r → ℤ) (b : BinaryAuxCoefficients r) :
    (binaryAuxPolynomial c).coeff (binaryAuxExponent b) = c b := by
  simp only [binaryAuxPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    (binary_exponent_injective r).eq_iff]
  simp

theorem binary_polynomial_support {m : ℕ} {r : Fin m → ℕ}
    (c : BinaryAuxCoefficients r → ℤ) (e : RothBlockVars2 m →₀ ℕ)
    (he : e ∈ (binaryAuxPolynomial c).support) : ∃ b : BinaryAuxCoefficients r, binaryAuxExponent b = e := by
  obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  exact ⟨b,(Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)).symm⟩

theorem binary_polynomial_homogeneous {m : ℕ} {r : Fin m → ℕ}
    (c : BinaryAuxCoefficients r → ℤ) : binaryBlockHomogeneous r (binaryAuxPolynomial c) := by
  intro e he h
  obtain ⟨b,rfl⟩ := binary_polynomial_support c e he
  exact binary_exponent_block b h

theorem binary_polynomial_ne_zero {m : ℕ} {r : Fin m → ℕ}
    (c : BinaryAuxCoefficients r → ℤ) (hc : c ≠ 0) : binaryAuxPolynomial c ≠ 0 := by
  intro hz
  apply hc
  funext b
  have hh := binary_polynomial_coeff c b
  rw [hz,MvPolynomial.coeff_zero] at hh
  exact hh.symm

theorem binary_derivative_monomial {m : ℕ} (J e : RothBlockVars2 m →₀ ℕ) (c : ℤ) :
    binaryDividedDerivative J (MvPolynomial.monomial e c) =
      MvPolynomial.monomial (e-J) (c*∏ u : RothBlockVars2 m, (Nat.choose (e u) (J u) : ℤ)) := by
  unfold binaryDividedDerivative
  exact MvPolynomial.sum_monomial_eq (by simp)

theorem binary_scaled_derivative_monomial {m : ℕ} (a : Fin 2 → ℤ) (k : Fin 2)
    (J e : RothBlockVars2 m →₀ ℕ) :
    binaryScaledSubstitution a k (binaryDividedDerivative J (MvPolynomial.monomial e 1)) =
      MvPolynomial.C (∏ u : RothBlockVars2 m, (Nat.choose (e u) (J u) : ℤ)) *
        ∏ u : RothBlockVars2 m, binaryScaledChart a k u ^ (e-J) u := by
  rw [binary_derivative_monomial]
  change MvPolynomial.eval₂ MvPolynomial.C (binaryScaledChart a k)
    (MvPolynomial.monomial (e-J) (1*∏ u, (Nat.choose (e u) (J u) : ℤ))) = _
  rw [MvPolynomial.eval₂_monomial,one_mul]
  congr 1
  exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)

theorem binary_scaled_chart_form {m : ℕ} (a : Fin 2 → ℤ) (k : Fin 2) (h : Fin m) :
    (∑ j : Fin 2, MvPolynomial.C (a j)*binaryScaledChart a k (h,j)) = 0 := by
  fin_cases k <;> simp [Fin.sum_univ_two,binaryScaledChart] <;> ring

noncomputable def binaryAuxSourceHeight (L : Fin 3 → Fin 2 → Fin 2 → ℤ) : ℕ :=
  max 1 (Finset.univ.sup fun u : Fin 3 × Fin 2 × Fin 2 => (L u.1 u.2.1 u.2.2).natAbs)

theorem binary_source_height_one_le (L : Fin 3 → Fin 2 → Fin 2 → ℤ) :
    1 ≤ binaryAuxSourceHeight L := Nat.le_max_left _ _

theorem binary_source_height_coeff (L : Fin 3 → Fin 2 → Fin 2 → ℤ) (tau : Fin 3) (i j : Fin 2) :
    |L tau i j| ≤ (binaryAuxSourceHeight L : ℤ) := by
  have hh : (L tau i j).natAbs ≤ binaryAuxSourceHeight L :=
    (Finset.le_sup (f := fun u : Fin 3 × Fin 2 × Fin 2 => (L u.1 u.2.1 u.2.2).natAbs)
      (Finset.mem_univ (tau,i,j))).trans (Nat.le_max_right _ _)
  rw [← Int.natCast_natAbs]
  exact_mod_cast hh

theorem binary_exponent_sum {m : ℕ} {r : Fin m → ℕ} (b : BinaryAuxCoefficients r) :
    (∑ u : RothBlockVars2 m, binaryAuxExponent b u) = ∑ h, r h := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun h _ => binary_exponent_block b h)

theorem binary_binomial_bound {m : ℕ} {r : Fin m → ℕ}
    (b : BinaryAuxCoefficients r) (J : RothBlockVars2 m →₀ ℕ) :
    |∏ u : RothBlockVars2 m, (Nat.choose (binaryAuxExponent b u) (J u) : ℤ)| ≤
      (2 : ℤ)^(∑ h, r h) := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ u : RothBlockVars2 m, (2 : ℤ)^binaryAuxExponent b u := by
      apply Finset.prod_le_prod
      · intro u _; exact abs_nonneg _
      · intro u _
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        have hh : (binaryAuxExponent b u).choose (J u) ≤ 2^binaryAuxExponent b u := by
          rcases Nat.eq_zero_or_pos (binaryAuxExponent b u) with hz | hp
          · rw [hz]; cases J u <;> simp
          · exact (Nat.choose_le_two_pow _ _ hp).le
        exact_mod_cast hh
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum,binary_exponent_sum]

theorem binary_scaled_chart_mass {m : ℕ} (a : Fin 2 → ℤ) (k : Fin 2)
    (A : ℤ) (ha : ∀ j, |a j| ≤ A) (u : RothBlockVars2 m) :
    rothAuxMass (binaryScaledChart a k u) ≤ A := by
  unfold binaryScaledChart
  split_ifs
  · rw [rothAuxMass_C_mul_X,abs_neg]; exact ha k.rev
  · rw [rothAuxMass_C_mul_X]; exact ha k

theorem binary_transformed_entry_bound {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 2 → ℤ) (k : Fin 2) (A : ℤ) (hA : 1 ≤ A) (ha : ∀ j, |a j| ≤ A)
    (b : BinaryAuxCoefficients r) (J e : RothBlockVars2 m →₀ ℕ) :
    |(binaryScaledSubstitution a k
      (binaryDividedDerivative J (MvPolynomial.monomial (binaryAuxExponent b) 1))).coeff e| ≤
      (2*A)^(∑ h, r h) := by
  have hsum : (∑ u : RothBlockVars2 m, (binaryAuxExponent b-J) u) ≤ ∑ h, r h := by
    rw [← binary_exponent_sum b]
    exact Finset.sum_le_sum (fun u _ => Nat.sub_le _ _)
  rw [binary_scaled_derivative_monomial]
  calc
    _ ≤ rothAuxMass (MvPolynomial.C (∏ u : RothBlockVars2 m,
        (Nat.choose (binaryAuxExponent b u) (J u) : ℤ)) *
        ∏ u : RothBlockVars2 m, binaryScaledChart a k u ^ (binaryAuxExponent b-J) u) :=
      rothAux_coeff_le_mass _ _
    _ ≤ rothAuxMass (MvPolynomial.C (∏ u : RothBlockVars2 m,
        (Nat.choose (binaryAuxExponent b u) (J u) : ℤ))) *
        rothAuxMass (∏ u : RothBlockVars2 m, binaryScaledChart a k u ^ (binaryAuxExponent b-J) u) :=
      rothAuxMass_mul _ _
    _ ≤ (2 : ℤ)^(∑ h, r h)*A^(∑ h, r h) := by
      apply mul_le_mul
      · simpa only [MvPolynomial.C_apply,rothAuxMass_monomial] using binary_binomial_bound b J
      · calc
          _ ≤ ∏ u : RothBlockVars2 m, rothAuxMass (binaryScaledChart a k u ^ (binaryAuxExponent b-J) u) :=
            rothAuxMass_prod _ _
          _ ≤ ∏ u : RothBlockVars2 m, A ^ (binaryAuxExponent b-J) u := by
            apply Finset.prod_le_prod
            · intro u _; exact rothAuxMass_nonneg _
            · intro u _
              exact (rothAuxMass_pow _ _).trans
                (pow_le_pow_left₀ (rothAuxMass_nonneg _) (binary_scaled_chart_mass a k A ha u) _)
          _ = A^(∑ u : RothBlockVars2 m, (binaryAuxExponent b-J) u) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ _ := pow_le_pow_right₀ hA hsum
      · exact rothAuxMass_nonneg _
      · positivity
    _ = _ := (mul_pow _ _ _).symm

noncomputable def binaryAuxPivot (L : Fin 3 → Fin 2 → Fin 2 → ℤ)
    (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) (f : Fin 3 × Fin 2) : Fin 2 :=
  (hL f.1 f.2).choose

noncomputable def binaryAuxMatrix {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 2 → Fin 2 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) :
    Matrix (BinaryAuxEquations r eta) (BinaryAuxCoefficients r) ℤ := fun q b =>
  (binaryScaledSubstitution (L q.1.1 q.1.2) (binaryAuxPivot L hL q.1)
    (binaryDividedDerivative (binaryPivotDerivative (binaryAuxPivot L hL q.1) (fun h => (q.2.val h).val))
      (MvPolynomial.monomial (binaryAuxExponent b) 1))).coeff
        (binaryFreeExponent (binaryAuxPivot L hL q.1) (fun h => r h-(q.2.val h).val))

theorem binary_matrix_entry_bound {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 2 → Fin 2 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0)
    (q : BinaryAuxEquations r eta) (b : BinaryAuxCoefficients r) :
    |binaryAuxMatrix r eta L hL q b| ≤ (2*(binaryAuxSourceHeight L : ℤ))^(∑ h, r h) := by
  exact binary_transformed_entry_bound _ _ _
    (by exact_mod_cast binary_source_height_one_le L)
    (fun j => binary_source_height_coeff L _ _ j) b _ _

end JSP000334
