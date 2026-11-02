import SubspaceBridge.SourceSchmidtRootPoint10
import SubspaceBridge.SourceSchmidtNonvanishing10
open scoped BigOperators Classical
noncomputable section
namespace CompoundFeasibility.SourceSchmidtContradiction10
open SchmidtScalar10 SchmidtRationalNormalization6 SchmidtTaylorCorrespondence6

theorem binary_closed_ideal_vanishing10 {m : ℕ} (N : Fin m → Fin 10 → ℤ)
    (r : Fin m → ℕ) (cutoff : ℝ) (G : MvPolynomial (Fin m) ℤ)
    (hG : G.map (Int.castRingHom ℝ) ∈ monicIdeal6 (binaryLift6 N) r cutoff) :
    ∀ J, JSP000334.rothTaylorWeight r J < cutoff →
      MvPolynomial.eval₂ (Int.castRingHom ℚ)
        (fun h => (rootNumerator6 (N h 0) (N h 1) : ℚ)/
          (rootDenominator6 (N h 0) (N h 1) : ℚ))
        (JSP000334.rothIntegerDividedDerivative J G) = 0 := by
  exact (monicIdeal6_iff_divided (binaryLift6 N) r _ (binary_root_point10 N) cutoff G).mp hG

theorem same_derivative_contradiction10 (m : ℕ) (hm : 0 < m)
    (N : Fin m → Fin 10 → ℤ) (theta C cutoff : ℝ)
    (ht : 0 < theta) (htu : theta < 1/12) (hC : 0 < C) (hCu : C ≤ 1)
    (hmargin : theta < cutoff) (r : Fin m → ℕ) (G : MvPolynomial (Fin m) ℤ)
    (hr : ∀ h, 0 < r h)
    (hsep : ∀ (h : Fin m) (hh : h.val+1 < m),
      (r ⟨h.val+1,hh⟩ : ℝ) ≤ JSP000334.omega65 m theta*(r h : ℝ))
    (hb : ∀ h, rootDenominator6 (N h 0) (N h 1) ≠ 0 ∧
      Int.gcd (rootNumerator6 (N h 0) (N h 1)) (rootDenominator6 (N h 0) (N h 1)) = 1)
    (hgrowth : ∀ h,
      |(rootDenominator6 (N ⟨0,hm⟩ 0) (N ⟨0,hm⟩ 1) : ℝ)|^((r ⟨0,hm⟩ : ℝ)*C) ≤
        |(rootDenominator6 (N h 0) (N h 1) : ℝ)|^(r h : ℝ))
    (hden : ∀ h, (2 : ℝ)^(3*m) ≤
      |(rootDenominator6 (N h 0) (N h 1) : ℝ)|^(JSP000334.omega65 m theta*C))
    (hGn : G ≠ 0) (hdegree : ∀ h, G.degreeOf h ≤ r h)
    (hheight : (JSP000334.rothIntegerHeight G : ℝ) ≤
      |(rootDenominator6 (N ⟨0,hm⟩ 0) (N ⟨0,hm⟩ 1) : ℝ)|^
        (JSP000334.omega65 m theta*(r ⟨0,hm⟩ : ℝ)*C))
    (hideal : G.map (Int.castRingHom ℝ) ∈ monicIdeal6 (binaryLift6 N) r cutoff) : False := by
  obtain ⟨J,hindex,hnonzero⟩ := budget_nonvanishing10 m hm theta C ht htu hC hCu r
    (fun h => rootNumerator6 (N h 0) (N h 1))
    (fun h => rootDenominator6 (N h 0) (N h 1)) G hr hsep hb hgrowth hden hGn hdegree hheight
  have hweight : JSP000334.rothTaylorWeight r J < cutoff := hindex.trans_lt hmargin
  exact hnonzero (binary_closed_ideal_vanishing10 N r cutoff G hideal J hweight)

end CompoundFeasibility.SourceSchmidtContradiction10
