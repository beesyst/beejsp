import SubspaceBridge.WeightedFiveTermSource4
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_five_term_proper_cover4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) :
    ∃ F : Set (Submodule ℚ (Fin 4 → ℚ)),F.Finite ∧ (∀ P∈F,P≠⊤) ∧
      ∀ p∈WeightedFiveTermSolutions A B,
        ∃ P∈F,(fun i => ((p i : ℚˣ) : ℚ))∈P := by
  classical
  obtain ⟨L,hL,t,ht,hcoef⟩ := weighted_coefficient_denominator4 B hB
  let G : Set ℕ := {g | 0<g ∧ (g : ℤ)∣(∏ i,t i)}
  have hG : G.Finite := weighted_diagonal_gcd_values_finite4 t ht
  have hex (g : G) : ∃ F : Set (Submodule ℚ (Fin 4 → ℚ)),F.Finite ∧ (∀ P∈F,P≠⊤) ∧
      ∀ y : (Fin 4 → ℤ),weightedFixedProductQuadruples4 (fun i => (t i : ℚ)/(g.val : ℚ))
        ((L : ℚ)*A/(g.val : ℚ)) y → ∃ P∈F,(fun i => (y i : ℚ))∈P := by
    have hgn : (g.val : ℚ)≠0 := by exact_mod_cast ne_of_gt g.property.1
    exact weighted_fixed_product_cover4 (fun i => (t i : ℚ)/(g.val : ℚ)) ((L : ℚ)*A/(g.val : ℚ))
      (fun i => div_ne_zero (by exact_mod_cast ht i) hgn)
      (div_ne_zero (mul_ne_zero (by exact_mod_cast ne_of_gt hL) hA) hgn)
  choose F hF hproper hcover using hex
  let family : Set (Submodule ℚ (Fin 4 → ℚ)) :=
    ⋃ g : G,(fun P : Submodule ℚ (Fin 4 → ℚ) => P.comap (weightedDiagonalMap4 t)) '' F g
  have hfamily : family.Finite := by
    letI := hG.fintype
    exact Set.finite_iUnion (fun g => (hF g).image _)
  refine ⟨family,hfamily,?_,?_⟩
  · intro Q hQ
    obtain ⟨g,hg⟩ := Set.mem_iUnion.mp hQ
    obtain ⟨P,hPF,rfl⟩ := hg
    exact weighted_diagonal_comap_proper4 t ht P (hproper g P hPF)
  · intro p hp
    obtain ⟨z,s,g,hg,hgd,y,hz,he,hy⟩ := weighted_original_product_input4 A B L t ht hcoef p hp
    let gg : G := ⟨g,hg,hgd⟩
    obtain ⟨P,hPF,hyP⟩ := hcover gg y hy
    refine ⟨P.comap (weightedDiagonalMap4 t),Set.mem_iUnion.mpr ⟨gg,Set.mem_image_of_mem _ hPF⟩,?_⟩
    exact weighted_diagonal_original_mem4 t z y g p s hz he P hyP

end JSP000334
