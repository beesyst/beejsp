import SubspaceBridge.SchmidtHilfssatz12
open scoped BigOperators Classical
noncomputable section
namespace CompoundFeasibility.SourceSchmidtContradiction10

theorem budget_nonvanishing10 (m : ℕ) (hm : 0 < m) (theta C : ℝ)
    (ht : 0 < theta) (htu : theta < 1/12) (hC : 0 < C) (hCu : C ≤ 1)
    (r : Fin m → ℕ) (p b : Fin m → ℤ) (G : MvPolynomial (Fin m) ℤ)
    (hr : ∀ h, 0 < r h)
    (hsep : ∀ (h : Fin m) (hh : h.val+1 < m),
      (r ⟨h.val+1,hh⟩ : ℝ) ≤ JSP000334.omega65 m theta*(r h : ℝ))
    (hb : ∀ h, b h ≠ 0 ∧ Int.gcd (p h) (b h) = 1)
    (hgrowth : ∀ h, |(b ⟨0,hm⟩ : ℝ)|^((r ⟨0,hm⟩ : ℝ)*C) ≤ |(b h : ℝ)|^(r h : ℝ))
    (hden : ∀ h, (2 : ℝ)^(3*m) ≤ |(b h : ℝ)|^(JSP000334.omega65 m theta*C))
    (hG : G ≠ 0) (hdegree : ∀ h, G.degreeOf h ≤ r h)
    (hheight : (JSP000334.rothIntegerHeight G : ℝ) ≤
      |(b ⟨0,hm⟩ : ℝ)|^(JSP000334.omega65 m theta*(r ⟨0,hm⟩ : ℝ)*C)) :
    ∃ J : Fin m →₀ ℕ, (∑ h : Fin m, (J h : ℝ)/(r h : ℝ)) ≤ theta ∧
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun h => (p h : ℚ)/(b h : ℚ))
        (JSP000334.rothIntegerDividedDerivative J G) ≠ 0 := by
  apply JSP000334.SchmidtHilfssatz12.hilfssatz12_nonvanishing
    m hm theta C ht htu hC hCu r p b G hr hsep hb
  · intro h
    simpa only [Real.rpow_natCast] using hgrowth h
  · exact hden
  · exact hG
  · intro d hd h
    exact (MvPolynomial.monomial_le_degreeOf h hd).trans (hdegree h)
  · exact hheight

end CompoundFeasibility.SourceSchmidtContradiction10
