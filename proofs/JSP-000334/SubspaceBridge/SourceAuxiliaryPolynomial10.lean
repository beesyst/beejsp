import SubspaceBridge.SourceVanishing10
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10 SourceExpansion10
open SourceBalance10 SourceVanishing10

theorem source_auxiliary_polynomial10 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ hmem : ∀ tau i j, SourceForms10.forms10 A2 A3 L tau i j ∈ K,
      ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧ ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log (60*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars10 m) ℤ, P ≠ 0 ∧ homogeneous10 r P ∧
      (∀ h, blockDegree10 P h = r h) ∧ (∀ u, P.degreeOf u ≤ r u.1) ∧
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
        ‖(expansion (SourceForms10.finiteMatrix10 3 A3) J P).coeff b‖ ≤ E^(∑ h, r h)) ∧
        (∀ (Q : Fin m → ℝ), (∀ h,1<Q h) → ∀ h0 : Fin m,
          ∀ delta : ℝ, 4000*eta<delta → delta<1 →
          (∀ h,1060*E<(Q h)^eta) → (∀ h,10*(eta⁻¹+1)<(Q h)^eta) →
          (∀ h,(r h0 : ℝ)*Real.log (Q h0)≤(r h : ℝ)*Real.log (Q h) ∧
            (r h : ℝ)*Real.log (Q h)≤(1+eta)*((r h0 : ℝ)*Real.log (Q h0))) →
          ∀ c : Fin 3 → Fin 10 → ℝ, (∀ tau i,|c tau i|≤1) → (∑ tau,∑ i,c tau i)=0 →
          ∀ w : Fin m → Fin 9 → Fin 10 → ℤ,
          (∀ h j i,‖(L *ᵥ (fun k => (w h j k : ℝ))) i‖≤(Q h)^(c 0 i-delta)) →
          (∀ h j i,‖(SourceForms10.finiteMatrix10 2 A2 *ᵥ (fun k => (w h j k : ℚ_[2]))) i‖≤(Q h)^(c 1 i)) →
          (∀ h j i,‖(SourceForms10.finiteMatrix10 3 A3 *ᵥ (fun k => (w h j k : ℚ_[3]))) i‖≤(Q h)^(c 2 i)) →
          (∀ a : Fin m → Fin 9 → ℕ, (∀ h j,1≤a h j ∧ a h j≤Nat.floor eta⁻¹+1) →
          ∀ J : Vars10 m →₀ ℕ, rothSourceDerivativeWeight r J<2*eta*m →
          integerValue J P (gridPoint w a)=0) ∧
          ∀ M : Fin m → Fin 10 → ℤ, (∀ h, M h ≠ 0) →
          (∀ h, LinearMap.ker (SchmidtNormal10.normalForm10 (M h)) =
            Submodule.span ℚ (Set.range (fun j i => (w h j i : ℚ)))) →
          (∀ h, LinearMap.ker (SchmidtNormal10.realNormalForm10 (M h)) =
            Submodule.span ℝ (Set.range (fun j i => (w h j i : ℝ)))) →
          (∀ J : Vars10 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
            (∀ y : Fin m → Fin 10 → ℚ, (∀ h, y h ∈ LinearMap.ker (SchmidtNormal10.normalForm10 (M h))) →
              MvPolynomial.eval (fun u => y u.1 u.2) (derivative10 J (P.map (Int.castRingHom ℚ))) = 0) ∧
            (∀ y : Fin m → Fin 10 → ℝ, (∀ h, y h ∈ LinearMap.ker (SchmidtNormal10.realNormalForm10 (M h))) →
              MvPolynomial.eval (fun u => y u.1 u.2) (derivative10 J (P.map (Int.castRingHom ℝ))) = 0)) ∧
          P.map (Int.castRingHom ℝ) ∈ SchmidtNormal10.sourceNormalIdeal10 M r ((m : ℝ)*eta)) := by
  obtain ⟨K,hK,hmem,D,E,hD,hE,hconstruction⟩ := source_auxiliary10_grid_vanishing A2 A3 L h2 h3 hL ha
  refine ⟨K,hK,hmem,D,E,hD,hE,?_⟩
  intro eta heta m hm r hr
  obtain ⟨P,hn,hhom,hheight,hfield,hreal,hp2,hp3,hclaims,hcfs,hgrid⟩ := hconstruction eta heta m hm r hr
  obtain ⟨hblock,hdegree⟩ := source_polynomial_degrees10 r P hhom hn
  refine ⟨P,hn,hhom,hblock,hdegree,hheight,hfield,hreal,hp2,hp3,hclaims,hcfs,?_⟩
  intro Q hQ h0 delta hd hd1 hgE hg hlog c hc hbalance w hw0 hw2 hw3
  have hvan := hgrid Q hQ h0 delta hd hd1 hgE hg hlog c hc hbalance w hw0 hw2 hw3
  refine ⟨hvan,?_⟩
  intro M hM hQspan hRspan
  exact integer_grid_high_normal_index10 r hr P hhom w M hM hQspan hRspan eta heta hvan

end CompoundFeasibility.Auxiliary10
