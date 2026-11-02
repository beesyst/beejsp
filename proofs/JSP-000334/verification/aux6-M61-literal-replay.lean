import SubspaceBridge.AuxiliarySourceIndex
import SubspaceBridge
open scoped BigOperators
namespace AuxiliaryLiteralChallenge

abbrev Vars (m : ℕ) := Fin m × Fin 3
abbrev Poly (m : ℕ) := MvPolynomial (Vars m) ℤ

noncomputable def height {m : ℕ} (P : Poly m) : ℝ :=
  (P.support.sup fun d => (P.coeff d).natAbs : ℕ)

noncomputable def rowHeight (V : Fin 3 → ℤ) : ℝ :=
  (Finset.univ.sup fun i => (V i).natAbs : ℕ)

def blockHomogeneous {m : ℕ} (r : Fin m → ℕ) (P : Poly m) : Prop :=
  ∀ d ∈ P.support, ∀ h, ∑ i : Fin 3, d (h, i) = r h

noncomputable def dividedDerivative {m : ℕ}
    (J : Vars m →₀ ℕ) (P : Poly m) : Poly m :=
  P.sum fun d z => MvPolynomial.monomial (d - J)
    (z * ∏ u : Vars m, (Nat.choose (d u) (J u) : ℤ))

noncomputable def chart {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (k : Fin m → Fin 3) (u : Vars m) : MvPolynomial (Vars m) ℚ :=
  if u.2 = k u.1 then
    -(∑ i ∈ Finset.univ.erase (k u.1),
      MvPolynomial.C ((V u.1 i : ℚ) / (V u.1 (k u.1) : ℚ)) *
        MvPolynomial.X (u.1, i))
  else MvPolynomial.X u

noncomputable def restrict {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (k : Fin m → Fin 3) (P : Poly m) : MvPolynomial (Vars m) ℚ :=
  MvPolynomial.eval₂ (Int.castRingHom _) (chart V k) P

def highIndex {m : ℕ} (r : Fin m → ℕ) (V : Fin m → Fin 3 → ℤ)
    (T : ℝ) (P : Poly m) : Prop :=
  ∀ J : Vars m →₀ ℕ,
    (∑ h : Fin m, (∑ i : Fin 3, (J (h,i) : ℝ)) / (r h : ℝ)) < T →
    ∀ k : Fin m → Fin 3, (∀ h, V h (k h) ≠ 0) → restrict V k (dividedDerivative J P) = 0

noncomputable def contract : Prop :=
  ∀ (L : Fin 3 → Fin 3 → Fin 3 → ℤ), (∀ tau i, ∃ j, L tau i j ≠ 0) →
  ∃ D : ℝ, 1 ≤ D ∧
    ∀ eta : ℝ, 0 < eta →
    ∀ m : ℕ, 4 * (eta ^ 2)⁻¹ * Real.log 18 ≤ (m : ℝ) →
    ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
    ∃ P : Poly m, P ≠ 0 ∧ blockHomogeneous r P ∧
      height P ≤ D ^ (∑ h, r h) ∧
      ∀ tau i, highIndex r (fun _ => L tau i) ((1/3 - eta) * m) P

#check contract
#check (JSP000334.roth_auxiliary_integer_three_place : contract)
#print axioms JSP000334.roth_auxiliary_integer_three_place
end AuxiliaryLiteralChallenge
