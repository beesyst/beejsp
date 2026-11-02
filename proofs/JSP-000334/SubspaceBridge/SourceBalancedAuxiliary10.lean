import SubspaceBridge.SourceBundledClaims10
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary10.SourceBalance10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10 SourceExpansion10

theorem source_auxiliary10_balanced (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ hmem : ∀ tau i j, SourceForms10.forms10 A2 A3 L tau i j ∈ K,
      ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧ ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log (60*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars10 m) ℤ, P ≠ 0 ∧ homogeneous10 r P ∧
      (height10 P : ℝ) ≤ D^(∑ h, r h) ∧
      (∀ tau, matrixIndex10 (fun i j => (⟨SourceForms10.forms10 A2 A3 L tau i j,hmem tau i j⟩ : K)) r eta P) ∧
      (∀ tau, matrixIndex10 (SourceForms10.forms10 A2 A3 L tau) r eta P) ∧
      matrixIndex10 (SourceForms10.finiteMatrix10 2 A2) r eta P ∧
      matrixIndex10 (SourceForms10.finiteMatrix10 3 A3) r eta P ∧
      (Claims r eta L P ∧ Claims r eta (SourceForms10.finiteMatrix10 2 A2) P ∧
        Claims r eta (SourceForms10.finiteMatrix10 3 A3) P) ∧
      (∀ J b : Vars10 m →₀ ℕ,
        ‖(expansion L J P).coeff b‖ ≤ E^(∑ h, r h) ∧
        ‖(expansion (SourceForms10.finiteMatrix10 2 A2) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
        ‖(expansion (SourceForms10.finiteMatrix10 3 A3) J P).coeff b‖ ≤ E^(∑ h, r h)) := by
  obtain ⟨K,hK,hmem,D,hD,hconstruction⟩ := source_auxiliary10_all_places A2 A3 L h2 h3 hL ha
  obtain ⟨E,hE,hbound⟩ := source_coefficient_bounds A2 A3 L D hD
  refine ⟨K,hK,hmem,D,E,hD,hE,?_⟩
  intro eta heta m hm r hr
  obtain ⟨P,hn,hhom,hheight,hfield,hreal,hp2,hp3⟩ := hconstruction eta heta m hm r hr
  refine ⟨P,hn,hhom,hheight,hfield,hreal,hp2,hp3,?_,hbound m r hr P hhom hheight⟩
  exact source_three_claims10 A2 A3 L h2 h3 hL r hr eta heta P hhom
    (hreal 0) hp2 hp3

end CompoundFeasibility.Auxiliary10.SourceBalance10
