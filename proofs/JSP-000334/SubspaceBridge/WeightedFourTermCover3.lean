import SubspaceBridge.WeightedFourTermInput3
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_four_term_proper_cover3 (A B C D : ℚ)
    (hA : A≠0) (hB : B≠0) (hC : C≠0) (hD : D≠0) :
    ∃ F : Set (Submodule ℚ (Fin 3 → ℚ)),F.Finite ∧ (∀ P∈F,P≠⊤) ∧
      ∀ p∈WeightedFourTermSolutions A B C D,
        ∃ P∈F,![((p.1 : ℚˣ) : ℚ),((p.2.1 : ℚˣ) : ℚ),((p.2.2 : ℚˣ) : ℚ)]∈P := by
  classical
  obtain ⟨L,hL,t,ht,hcoef⟩ := weighted_coefficient_denominator3 B C D hB hC hD
  let G : Set ℕ := {g | 0<g ∧ (g : ℤ)∣t 0*t 1*t 2}
  have hG : G.Finite := weighted_diagonal_gcd_values_finite3 t ht
  have hex (g : G) : ∃ F : Set (Submodule ℚ (Fin 3 → ℚ)),F.Finite ∧ (∀ P∈F,P≠⊤) ∧
      ∀ y : IntegerTriple,weightedFixedProductTriples3 (fun i => (t i : ℚ)/(g.val : ℚ))
        ((L : ℚ)*A/(g.val : ℚ)) y → ∃ P∈F,(fun i => (y i : ℚ))∈P := by
    have hgn : (g.val : ℚ)≠0 := by exact_mod_cast ne_of_gt g.property.1
    exact weighted_fixed_product_cover3 (fun i => (t i : ℚ)/(g.val : ℚ)) ((L : ℚ)*A/(g.val : ℚ))
      (fun i => div_ne_zero (by exact_mod_cast ht i) hgn)
      (div_ne_zero (mul_ne_zero (by exact_mod_cast ne_of_gt hL) hA) hgn)
  choose F hF hproper hcover using hex
  let family : Set (Submodule ℚ (Fin 3 → ℚ)) :=
    ⋃ g : G,(fun P : Submodule ℚ (Fin 3 → ℚ) => P.comap (weightedDiagonalMap3 t)) '' F g
  have hfamily : family.Finite := by
    letI := hG.fintype
    exact Set.finite_iUnion (fun g => (hF g).image _)
  refine ⟨family,hfamily,?_,?_⟩
  · intro Q hQ
    obtain ⟨g,hg⟩ := Set.mem_iUnion.mp hQ
    obtain ⟨P,hPF,rfl⟩ := hg
    exact weighted_diagonal_comap_proper3 t ht P (hproper g P hPF)
  · intro p hp
    obtain ⟨z,s,g,hg,hgd,y,hz,he,hy⟩ := weighted_original_product_input3 A B C D L t ht hcoef p hp
    let gg : G := ⟨g,hg,hgd⟩
    obtain ⟨P,hPF,hyP⟩ := hcover gg y hy
    refine ⟨P.comap (weightedDiagonalMap3 t),Set.mem_iUnion.mpr ⟨gg,Set.mem_image_of_mem _ hPF⟩,?_⟩
    have hm := weighted_diagonal_original_mem3 t z y g (![p.1,p.2.1,p.2.2]) s hz he P hyP
    have hv : (fun i : Fin 3 => (((![p.1,p.2.1,p.2.2] i) : ℚˣ) : ℚ))=
        ![((p.1 : ℚˣ) : ℚ),((p.2.1 : ℚˣ) : ℚ),((p.2.2 : ℚˣ) : ℚ)] := by
      ext i
      fin_cases i <;> rfl
    rwa [hv] at hm

end JSP000334
