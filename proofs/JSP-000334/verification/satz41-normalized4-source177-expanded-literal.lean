import SubspaceBridge.SourceNormalIndex4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceNormalizedHighIndex4Literal177
open SourceNormalIndex4 OriginalDeformedSource4 SourceMultiblock4 Auxiliary4 OriginalLastDual4 Auxiliary4.SourceEvaluation4 Auxiliary4.SourceGrid4

theorem source_normalized_selected_high_index4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c0 c2 c3 : Fin 4 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ V),
      sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q (hQV q hq) c0 c2 c3 2 <
        sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q (hQV q hq) c0 c2 c3 3*q^(-delta)) :
    ∃ U : Set ℝ, ∃ hUV : U ⊆ V, ¬ BddAbove U ∧
      ∃ u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3,
      ∃ F : (q : U) → DeformedAttaining4 A2 A3 L (sourceUnit42 L hLdet) q.val
        (hQV q.val (hUV q.property)) c0 c2 c3 delta (u q),
      ∃ S : Finset OriginalSelectedSystem4.MixedIndex4, S.Nonempty ∧
      ∃ W : Set ℝ, ∃ hWU : W ⊆ U, ¬ BddAbove W ∧
        ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' W) ∧
        (∀ q : U, q.val ∈ W →
          OriginalSelectedSystem4.publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
            (OriginalDeformation4.deformedWidths4 q.val c0
              (OriginalDeformation4.gapDeformation4
                (sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q.val
                  (hQV q.val (hUV q.property)) c0 c2 c3)) (F q).sigma) (fun i => c2 i/5) (fun i => c3 i/5) = S) ∧
        ∀ B : Set ℝ, ∀ hBW : B ⊆ W, ¬ BddAbove B →
∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ ∃ m : ℕ, 0 < m ∧
      ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      (∀ tau i j, SourceForms4.forms4 A2 A3 L tau i j ∈ K) ∧
      ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧
      ∀ rho : ℝ, 0 < rho → ∃ t : Fin m → B,
        StrictMono (fun h => (t h).val) ∧
        ∃ r : Fin m → ℕ, (∀ h, 0 < r h) ∧
        (∀ (h : Fin m) (hh : h.val+1 < m), (r ⟨h.val+1,hh⟩ : ℝ) ≤ rho*(r h : ℝ)) ∧
        ∃ P : MvPolynomial (Vars4 m) ℤ, P ≠ 0 ∧ homogeneous4 r P ∧
          (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
          matrixIndex4 L r eta P ∧ matrixIndex4 (SourceForms4.finiteMatrix4 2 A2) r eta P ∧
          matrixIndex4 (SourceForms4.finiteMatrix4 3 A3) r eta P ∧
          (∀ J b : Vars4 m →₀ ℕ,
            ‖(Auxiliary4.SourceExpansion4.expansion L J P).coeff b‖ ≤ E^(∑ h,r h) ∧
            ‖(Auxiliary4.SourceExpansion4.expansion (SourceForms4.finiteMatrix4 2 A2) J P).coeff b‖ ≤ E^(∑ h,r h) ∧
            ‖(Auxiliary4.SourceExpansion4.expansion (SourceForms4.finiteMatrix4 3 A3) J P).coeff b‖ ≤ E^(∑ h,r h)) ∧
          (∀ a : Fin m → Fin 3 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
          ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
            integerValue J P (gridPoint (fun h j => (((fun q : B => F ⟨q.val,hWU (hBW q.property)⟩) (t h)).w j.castSucc : Fin 4 → ℤ)) a) = 0) ∧
          ∃ (g : Fin m → ℤ) (M a : Fin m → Fin 4 → ℤ),
            (∀ h, g h ≠ 0 ∧ M h ≠ 0 ∧
              (∀ i, integerLastDual4 (fun j => (((fun q : B => F ⟨q.val,hWU (hBW q.property)⟩) (t h)).w j : Fin 4 → ℤ)) i = g h*M h i) ∧
              (∑ i, a h i*M h i) = 1 ∧ Ideal.span (Set.range (M h)) = ⊤ ∧
              LinearMap.ker (normalForm4 (M h)) =
                Submodule.span ℚ (Set.range (fun j : Fin 3 => fun i => ((((fun q : B => F ⟨q.val,hWU (hBW q.property)⟩) (t h)).w j.castSucc : Fin 4 → ℤ) i : ℚ))) ∧
              LinearMap.ker (realNormalForm4 (M h)) =
                Submodule.span ℝ (Set.range (fun j : Fin 3 => integerReal (((fun q : B => F ⟨q.val,hWU (hBW q.property)⟩) (t h)).w j.castSucc : Fin 4 → ℤ)))) ∧
            (∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
              (∀ y : Fin m → Fin 4 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm4 (M h))) →
                MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℚ))) = 0) ∧
              (∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
                MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℝ))) = 0)) ∧
            P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 M r ((m : ℝ)*eta) := by
  obtain ⟨T,hT,u0,_,hU,_,hframes,hready⟩ :=
    OriginalDeformation4.source_normalized_unbounded_deformation4 A2 A3 L h2 h3 hLdet hAlg
      delta hd c0 c2 c3 hc0 hc2 hc3 hb V hV hQV hgap
  let U : Set ℝ := {q | q ∈ V ∧ T < q}
  let hUV : U ⊆ V := fun _ hq => hq.1
  let hQU : ∀ q ∈ U, 1 < q := fun q hq => hQV q hq.1
  let u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3 :=
    fun q => u0 ⟨q.val,q.property.1⟩
  have hr (q : U) : OriginalDeformation4.deformationReady4 A2 A3 L (sourceUnit42 L hLdet)
      q.val (hQU q.val q.property) c0 c2 c3 delta (u q) :=
    (hready ⟨q.val,q.property.1⟩ q.property.2).2.2
  obtain ⟨F,S,hS,W,hWU,hW,hWp,hindex⟩ := OriginalSelectedSystem4.deformed_fixed_selected_system4
    A2 A3 L (sourceUnit42 L hLdet) c0 c2 c3 delta hd U hU hQU u hr
  refine ⟨U,hUV,hU,u,F,S,hS,W,hWU,hW,hWp,hindex,?_⟩
  intro B hBW hB
  exact same_selected_frame_high_index4
    (A2 := A2) (A3 := A3) (L := L) (hL := sourceUnit42 L hLdet)
    (c0 := c0) (c2 := c2) (c3 := c3) (delta := delta) (U := B)
    (hQU := fun q hq => hQV q (hUV (hWU (hBW hq))))
    (u := fun q : B => u ⟨q.val,hWU (hBW q.property)⟩)
    h2 h3 hLdet hAlg
    (fun q : B => F ⟨q.val,hWU (hBW q.property)⟩) hB hd hc2 hc3


end CompoundFeasibility.SourceNormalizedHighIndex4Literal177

#check CompoundFeasibility.SourceNormalizedHighIndex4Literal177.source_normalized_selected_high_index4
#print CompoundFeasibility.SourceNormalizedHighIndex4Literal177.source_normalized_selected_high_index4
#print axioms CompoundFeasibility.SourceNormalizedHighIndex4Literal177.source_normalized_selected_high_index4
