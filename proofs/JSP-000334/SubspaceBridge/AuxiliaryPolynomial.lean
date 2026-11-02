import SubspaceBridge.AuxiliarySiegel

open scoped BigOperators Classical
namespace JSP000334

theorem rothAuxPolynomial_support {m : ℕ} {r : Fin m → ℕ}
    (c : RothAuxCoefficients r → ℤ) (d : RothBlockVars m →₀ ℕ)
    (hd : d ∈ (rothAuxPolynomial c).support) :
    ∃ b : RothAuxCoefficients r, rothAuxExponent b = d := by
  obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  exact ⟨b, (Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)).symm⟩

theorem rothAuxPolynomial_coeff_zero_of_not_indexed {m : ℕ} {r : Fin m → ℕ}
    (c : RothAuxCoefficients r → ℤ) (d : RothBlockVars m →₀ ℕ)
    (hd : ¬ ∃ b : RothAuxCoefficients r, rothAuxExponent b = d) :
    (rothAuxPolynomial c).coeff d = 0 := by
  by_contra hn
  exact hd (rothAuxPolynomial_support c d (MvPolynomial.mem_support_iff.mpr hn))

theorem rothAuxPolynomial_height_le {m : ℕ} {r : Fin m → ℕ}
    (c : RothAuxCoefficients r → ℤ) (H : ℕ) (hc : ∀ b, (c b).natAbs ≤ H) :
    rothKernelBlockHeight (rothAuxPolynomial c) ≤ H := by
  apply Finset.sup_le
  intro d hd
  obtain ⟨b, hb⟩ := rothAuxPolynomial_support c d hd
  rw [← hb, rothAuxPolynomial_coeff]
  exact hc b

noncomputable def rothAuxHeightConstant (L : Fin 3 → Fin 3 → Fin 3 → ℤ) : ℝ :=
  18 * (rothAuxSourceHeight L : ℝ)

theorem rothAuxHeightConstant_one_le (L : Fin 3 → Fin 3 → Fin 3 → ℤ) :
    1 ≤ rothAuxHeightConstant L := by
  have h := rothAuxSourceHeight_one_le L
  dsimp [rothAuxHeightConstant]
  have h' : (1 : ℝ) ≤ rothAuxSourceHeight L := by exact_mod_cast h
  linarith

theorem roth_auxiliary_integer_polynomial
    (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ (eta : ℝ), 0 < eta →
      ∀ (m : ℕ), 4 * (eta ^ 2)⁻¹ * Real.log 18 ≤ (m : ℝ) →
      ∀ (r : Fin m → ℕ), (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (RothBlockVars m) ℤ,
        P ≠ 0 ∧ rothBlockHomogeneous r P ∧
        (rothKernelBlockHeight P : ℝ) ≤ D ^ (∑ h, r h) ∧
        ∀ (f : Fin 9) (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i}),
          rothAuxScaledSubstitution (L (rothAuxFormEquiv f).1 (rothAuxFormEquiv f).2)
            (rothAuxPivot L hL f) (rothBlockIntegerDividedDerivative
              (rothAuxPivotDerivative (rothAuxPivot L hL f) (fun h => (i.val h).val)) P) = 0 := by
  refine ⟨rothAuxHeightConstant L, rothAuxHeightConstant_one_le L, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨c, hc, hker, hbound⟩ := rothAuxMatrix_exists_bounded_int_kernel r hr eta heta hm L hL
  refine ⟨rothAuxPolynomial c, ?_, rothAuxPolynomial_homogeneous c, ?_, ?_⟩
  · intro hz
    apply hc
    funext b
    exact (rothAuxPolynomial_eq_zero_iff c).mp hz b
  · have hnat : ∀ b, (c b).natAbs ≤ (18 * rothAuxSourceHeight L) ^ (∑ h, r h) := by
      intro b
      have hb := hbound b
      rw [← Int.natCast_natAbs] at hb
      exact_mod_cast hb
    have hheight := rothAuxPolynomial_height_le c _ hnat
    dsimp [rothAuxHeightConstant]
    exact_mod_cast hheight
  · exact (rothAuxMatrix_mulVec_zero_iff_polynomials_zero r eta L hL c).mp hker

end JSP000334
