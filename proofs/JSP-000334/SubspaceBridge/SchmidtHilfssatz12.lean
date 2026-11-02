import SubspaceBridge.SchmidtOmega6
open scoped BigOperators Classical
noncomputable section
namespace JSP000334.SchmidtHilfssatz12

theorem published_omega_comparison (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : 0 < theta) (ht' : theta < 1/12) :
    omega65 m theta ≤ rothInductionOmega m theta :=
  omega65_le_induction m (by omega) theta ht ht'

theorem integer_denominator_base (q : ℤ) (hq : q ≠ 0) : 1 ≤ |(q : ℝ)| := by
  have h : 1 ≤ q.natAbs := Int.natAbs_pos.mpr hq
  have hR : (1 : ℝ) ≤ (q.natAbs : ℝ) := by exact_mod_cast h
  simpa only [Int.cast_natAbs,Int.cast_abs] using hR

theorem exponent_signs (m : ℕ) (hm : 0 < m) (theta C : ℝ)
    (ht : 0 < theta) (ht' : theta < 1/12) (hC : 0 < C) (r0 : ℕ) :
    0 ≤ omega65 m theta*C ∧ 0 ≤ rothInductionOmega m theta*C ∧
      0 ≤ omega65 m theta*(r0 : ℝ)*C ∧ 0 ≤ rothInductionOmega m theta*(r0 : ℝ)*C := by
  have ho := omega65_pos m theta ht
  have hrho := ho.trans_le (published_omega_comparison m hm theta ht ht')
  refine ⟨?_,?_,?_,?_⟩ <;> positivity

theorem degree_separation_transfer (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : 0 < theta) (ht' : theta < 1/12) (r : Fin m → ℕ)
    (hsep : ∀ (h : Fin m) (hh : h.val+1 < m),
      (r ⟨h.val+1,hh⟩ : ℝ) ≤ omega65 m theta*(r h : ℝ)) :
    ∀ (h : Fin m) (hh : h.val+1 < m),
      (r ⟨h.val+1,hh⟩ : ℝ) ≤ rothInductionOmega m theta*(r h : ℝ) := by
  intro h hh
  exact (hsep h hh).trans (mul_le_mul_of_nonneg_right
    (published_omega_comparison m hm theta ht ht') (Nat.cast_nonneg _))

theorem denominator_growth_transfer (m : ℕ) (hm : 0 < m) (theta C : ℝ)
    (ht : 0 < theta) (ht' : theta < 1/12) (hC : 0 < C)
    (q : ℤ) (hq : q ≠ 0)
    (hden : (2 : ℝ)^(3*m) ≤ |(q : ℝ)|^(omega65 m theta*C)) :
    (2 : ℝ)^(3*m) ≤ |(q : ℝ)|^(rothInductionOmega m theta*C) := by
  apply hden.trans
  apply Real.rpow_le_rpow_of_exponent_le (integer_denominator_base q hq)
  exact mul_le_mul_of_nonneg_right (published_omega_comparison m hm theta ht ht') hC.le

theorem polynomial_height_transfer (m : ℕ) (hm : 0 < m) (theta C : ℝ)
    (ht : 0 < theta) (ht' : theta < 1/12) (hC : 0 < C)
    (r0 : ℕ) (q0 : ℤ) (hq0 : q0 ≠ 0) (P : MvPolynomial (Fin m) ℤ)
    (hH : (rothIntegerHeight P : ℝ) ≤ |(q0 : ℝ)|^(omega65 m theta*(r0 : ℝ)*C)) :
    (rothIntegerHeight P : ℝ) ≤ |(q0 : ℝ)|^(rothInductionOmega m theta*(r0 : ℝ)*C) := by
  apply hH.trans
  apply Real.rpow_le_rpow_of_exponent_le (integer_denominator_base q0 hq0)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (published_omega_comparison m hm theta ht ht')
      (Nat.cast_nonneg _)) hC.le

theorem hilfssatz12_nonvanishing (m : ℕ) (hm : 0 < m) (theta C : ℝ)
    (ht : 0 < theta) (ht' : theta < 1/12) (hC : 0 < C) (hC' : C ≤ 1)
    (r : Fin m → ℕ) (p q : Fin m → ℤ) (P : MvPolynomial (Fin m) ℤ)
    (hr : ∀ h, 0 < r h)
    (hsep : ∀ (h : Fin m) (hh : h.val+1 < m),
      (r ⟨h.val+1,hh⟩ : ℝ) ≤ omega65 m theta*(r h : ℝ))
    (hq : ∀ h, q h ≠ 0 ∧ Int.gcd (p h) (q h) = 1)
    (hgrowth : ∀ h : Fin m,
      |(q ⟨0,hm⟩ : ℝ)|^((r ⟨0,hm⟩ : ℝ)*C) ≤ |(q h : ℝ)|^(r h))
    (hden : ∀ h, (2 : ℝ)^(3*m) ≤ |(q h : ℝ)|^(omega65 m theta*C))
    (hP : P ≠ 0) (hb : ∀ b ∈ P.support, ∀ h, b h ≤ r h)
    (hH : (rothIntegerHeight P : ℝ) ≤
      |(q ⟨0,hm⟩ : ℝ)|^(omega65 m theta*(r ⟨0,hm⟩ : ℝ)*C)) :
    ∃ J : Fin m →₀ ℕ, (∑ h : Fin m, (J h : ℝ)/(r h : ℝ)) ≤ theta ∧
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun h => (p h : ℚ)/(q h : ℚ))
        (rothIntegerDividedDerivative J P) ≠ 0 := by
  apply roth_scalar_omega65_nonvanishing m hm theta C ht ht' hC hC' r p q P hr
    (degree_separation_transfer m hm theta ht ht' r hsep) hq
    (fun h _ => hgrowth h)
    (fun h => denominator_growth_transfer m hm theta C ht ht' hC (q h) (hq h).1 (hden h))
    hP hb
  exact polynomial_height_transfer m hm theta C ht ht' hC
    (r ⟨0,hm⟩) (q ⟨0,hm⟩) (hq _).1 P hH

theorem gamma_fifth_range (gamma : ℝ) (hg : 0 < gamma) (hg5 : gamma ≤ 5) :
    0 < gamma/5 ∧ gamma/5 ≤ 1 := by
  constructor <;> linarith

theorem hilfssatz12_gamma_fifth (m : ℕ) (hm : 0 < m) (theta gamma : ℝ)
    (ht : 0 < theta) (ht' : theta < 1/12) (hg : 0 < gamma) (hg5 : gamma ≤ 5)
    (r : Fin m → ℕ) (p q : Fin m → ℤ) (P : MvPolynomial (Fin m) ℤ)
    (hr : ∀ h, 0 < r h)
    (hsep : ∀ (h : Fin m) (hh : h.val+1 < m),
      (r ⟨h.val+1,hh⟩ : ℝ) ≤ omega65 m theta*(r h : ℝ))
    (hq : ∀ h, q h ≠ 0 ∧ Int.gcd (p h) (q h) = 1)
    (hgrowth : ∀ h : Fin m,
      |(q ⟨0,hm⟩ : ℝ)|^((r ⟨0,hm⟩ : ℝ)*(gamma/5)) ≤ |(q h : ℝ)|^(r h))
    (hden : ∀ h, (2 : ℝ)^(3*m) ≤ |(q h : ℝ)|^(omega65 m theta*(gamma/5)))
    (hP : P ≠ 0) (hb : ∀ b ∈ P.support, ∀ h, b h ≤ r h)
    (hH : (rothIntegerHeight P : ℝ) ≤
      |(q ⟨0,hm⟩ : ℝ)|^(omega65 m theta*(r ⟨0,hm⟩ : ℝ)*(gamma/5))) :
    ∃ J : Fin m →₀ ℕ, (∑ h : Fin m, (J h : ℝ)/(r h : ℝ)) ≤ theta ∧
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun h => (p h : ℚ)/(q h : ℚ))
        (rothIntegerDividedDerivative J P) ≠ 0 := by
  obtain ⟨hC,hC'⟩ := gamma_fifth_range gamma hg hg5
  exact hilfssatz12_nonvanishing m hm theta (gamma/5) ht ht' hC hC'
    r p q P hr hsep hq hgrowth hden hP hb hH

end JSP000334.SchmidtHilfssatz12
