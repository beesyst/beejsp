import SubspaceBridge.AuxiliarySourceIndex

open scoped BigOperators Classical
namespace SourceIndexResumeChallenge
noncomputable section
open JSP000334

def derivative {m : ℕ} (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) : MvPolynomial (RothBlockVars m) ℤ :=
  P.sum fun b c => MvPolynomial.monomial (b - J)
    (c * ∏ u : RothBlockVars m, (Nat.choose (b u) (J u) : ℤ))

def chart {m : ℕ} (V : Fin m → Fin 3 → ℤ) (k : Fin m → Fin 3)
    (u : RothBlockVars m) : MvPolynomial (RothBlockVars m) ℚ :=
  if u.2 = k u.1 then
    -(∑ i ∈ Finset.univ.erase (k u.1),
      MvPolynomial.C ((V u.1 i : ℚ) / (V u.1 (k u.1) : ℚ)) * MvPolynomial.X (u.1,i))
  else MvPolynomial.X u

def scaledChart {m : ℕ} (a : Fin 3 → ℤ) (k : Fin 3) (u : RothBlockVars m) :
    MvPolynomial (RothBlockVars m) ℤ :=
  if u.2 = k then
    -(∑ j ∈ Finset.univ.erase k, MvPolynomial.C (a j) * MvPolynomial.X (u.1,j))
  else MvPolynomial.C (a k) * MvPolynomial.X u

def pivotOrder {m : ℕ} (p : Fin 3) (i : Fin m → ℕ) : RothBlockVars m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.2 = p then i u.1 else 0)

theorem mixed_vanishing {m : ℕ} (r : Fin m → ℕ) (a : Fin 3 → ℤ)
    (p : Fin 3) (hp : a p ≠ 0) (T : ℝ) (P : MvPolynomial (RothBlockVars m) ℤ)
    (hz : ∀ i : Fin m → ℕ, (∑ h, (i h : ℝ) / r h) < T →
      MvPolynomial.eval₂Hom MvPolynomial.C (scaledChart a p)
        (derivative (pivotOrder p i) P) = 0)
    (J : RothBlockVars m →₀ ℕ)
    (hw : (∑ h, (∑ j : Fin 3, (J (h,j) : ℝ)) / r h) < T) :
    MvPolynomial.eval₂Hom MvPolynomial.C (scaledChart a p) (derivative J P) = 0 :=
  rothSource_scaled_mixed_vanishing r a p hp T P hz J hw

theorem exact_chart_transport {m : ℕ} (a : Fin 3 → ℤ) (p : Fin 3)
    (hp : a p ≠ 0) (k : Fin m → Fin 3) (hk : ∀ h, a (k h) ≠ 0)
    (P : MvPolynomial (RothBlockVars m) ℤ) :
    MvPolynomial.eval₂Hom (Int.castRingHom _)
      (fun u => MvPolynomial.C ((a p : ℚ)⁻¹) * chart (fun _ : Fin m => a) k u)
      (MvPolynomial.eval₂Hom MvPolynomial.C (scaledChart a p) P) =
      MvPolynomial.eval₂ (Int.castRingHom _) (chart (fun _ : Fin m => a) k) P :=
  rothSource_chart_transport a p hp k hk P

theorem block_excess {m : ℕ} (r : Fin m → ℕ) (P : MvPolynomial (RothBlockVars m) ℤ)
    (hP : ∀ d ∈ P.support, ∀ h, ∑ j : Fin 3, d (h,j) = r h)
    (J : RothBlockVars m →₀ ℕ) (h : Fin m) (hJ : r h < ∑ j : Fin 3, J (h,j)) :
    derivative J P = 0 := rothSource_derivative_zero_of_block_excess r P hP J h hJ

theorem complete_source_index (L : Fin 3 → Fin 3 → Fin 3 → ℤ)
    (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ (eta : ℝ), 0 < eta →
      ∀ (m : ℕ), 4 * (eta ^ 2)⁻¹ * Real.log 18 ≤ (m : ℝ) →
      ∀ (r : Fin m → ℕ), (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Fin m × Fin 3) ℤ,
        P ≠ 0 ∧ (∀ d ∈ P.support, ∀ h, ∑ j : Fin 3, d (h,j) = r h) ∧
        ((P.support.sup (fun d => (P.coeff d).natAbs) : ℕ) : ℝ) ≤ D ^ (∑ h, r h) ∧
        ∀ (tau i : Fin 3) (J : RothBlockVars m →₀ ℕ),
          (∑ h, (∑ j : Fin 3, (J (h,j) : ℝ)) / r h) < (1 / 3 - eta) * m →
          ∀ k : Fin m → Fin 3, (∀ h, L tau i (k h) ≠ 0) →
            MvPolynomial.eval₂ (Int.castRingHom _) (chart (fun _ : Fin m => L tau i) k)
              (derivative J P) = 0 := roth_auxiliary_integer_three_place L hL

end
end SourceIndexResumeChallenge

set_option pp.proofs false
#check SourceIndexResumeChallenge.mixed_vanishing
#print SourceIndexResumeChallenge.mixed_vanishing
#print axioms SourceIndexResumeChallenge.mixed_vanishing
#check SourceIndexResumeChallenge.exact_chart_transport
#print SourceIndexResumeChallenge.exact_chart_transport
#print axioms SourceIndexResumeChallenge.exact_chart_transport
#check SourceIndexResumeChallenge.block_excess
#print SourceIndexResumeChallenge.block_excess
#print axioms SourceIndexResumeChallenge.block_excess
#check SourceIndexResumeChallenge.complete_source_index
#print SourceIndexResumeChallenge.complete_source_index
#print axioms SourceIndexResumeChallenge.complete_source_index
