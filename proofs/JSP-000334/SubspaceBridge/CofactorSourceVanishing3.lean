import SubspaceBridge.CofactorSourceAssembly3
open scoped BigOperators Matrix
namespace JSP000334
noncomputable section

def cofactorSelectedBadQ3 (k₀ k₂ k₃ : Fin 3) (S : Set (Fin 3 → Fin 3)) (deltaSource : ℝ) : Set ℝ :=
  {Q | ∃ hQ : 1 < Q, ∃ c : Fin 3 → Fin 3 → ℝ,
    sourceWeightConditions3 c ∧
    (∀ s ∈ S, -deltaSource/2 ≤ c 0 (s 0)+c 1 (s 1)+c 2 (s 2)) ∧
      ∃ (B : Basis (Fin 3) ℝ RealTriple)
          (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q (c 1) (c 2)),
          lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q (c 1) (c 2)).toIntSubmodule.map integerTripleReal3 ∧
          LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) ∧
          (∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q (c 0) hQ)
            (integerTripleReal3 (u j : IntegerTriple)) =
              successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q (c 0) hQ) j) ∧
          dualFrameRelativeIndex3 (cofactorSourceLattice3 k₂ k₃ Q (c 1) (c 2)) u ≤ 6 ∧
          successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q (c 0) hQ) 1 < Q^(-deltaSource) ∧
          (∃ s ∈ S, cofactorSelectedProduct3 k₀ k₂ k₃ s
            (dualFrameVector3 (fun j => (u j : IntegerTriple)) 2) ≠ 0)}

theorem cofactorSelectedBadQ3_bddAbove (k₀ k₂ k₃ : Fin 3) (S : Set (Fin 3 → Fin 3))
    (hS : S.Nonempty) (deltaSource : ℝ) (hd : 0 < deltaSource) :
    BddAbove (cofactorSelectedBadQ3 k₀ k₂ k₃ S deltaSource) := by
  classical
  by_contra hU
  have hw (Q : ℝ) : ∃ c : Fin 3 → Fin 3 → ℝ,
      Q ∈ cofactorSelectedBadQ3 k₀ k₂ k₃ S deltaSource →
      sourceWeightConditions3 c ∧
      (∀ s ∈ S, -deltaSource/2 ≤ c 0 (s 0)+c 1 (s 1)+c 2 (s 2)) ∧
      ∀ hQ : 1 < Q,
      ∃ (B : Basis (Fin 3) ℝ RealTriple)
          (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q (c 1) (c 2)),
          lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q (c 1) (c 2)).toIntSubmodule.map integerTripleReal3 ∧
          LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) ∧
          (∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q (c 0) hQ)
            (integerTripleReal3 (u j : IntegerTriple)) =
              successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q (c 0) hQ) j) ∧
          dualFrameRelativeIndex3 (cofactorSourceLattice3 k₂ k₃ Q (c 1) (c 2)) u ≤ 6 ∧
          successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q (c 0) hQ) 1 < Q^(-deltaSource) ∧
          (∃ s ∈ S, cofactorSelectedProduct3 k₀ k₂ k₃ s
            (dualFrameVector3 (fun j => (u j : IntegerTriple)) 2) ≠ 0) := by
    by_cases h : Q ∈ cofactorSelectedBadQ3 k₀ k₂ k₃ S deltaSource
    · obtain ⟨hQ,c,hc,ht,hf⟩ := h
      exact ⟨c,fun _ => ⟨hc,ht,fun _ => hf⟩⟩
    · exact ⟨0,fun hh => (h hh).elim⟩
  choose c hc using hw
  exact cofactor_source_family_contradiction3 k₀ k₂ k₃ S hS deltaSource hd
    (cofactorSelectedBadQ3 k₀ k₂ k₃ S deltaSource) hU c
    (fun Q h => (hc Q h).1) (fun Q h => (hc Q h).2.1)
    (fun Q h => (hc Q h).2.2)

theorem cofactor_uniform_selected_vanishing3 (k₀ k₂ k₃ : Fin 3)
    (S : Set (Fin 3 → Fin 3)) (hS : S.Nonempty) (deltaSource : ℝ) (hd : 0 < deltaSource) :
    ∃ Q0 : ℝ, 1 ≤ Q0 ∧
      ∀ Q : ℝ, Q0 < Q → ∀ hQ : 1 < Q,
      ∀ c : Fin 3 → Fin 3 → ℝ, sourceWeightConditions3 c →
        (∀ s ∈ S, -deltaSource/2 ≤ c 0 (s 0)+c 1 (s 1)+c 2 (s 2)) →
      ∀ (B : Basis (Fin 3) ℝ RealTriple)
        (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q (c 1) (c 2)),
          lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q (c 1) (c 2)).toIntSubmodule.map integerTripleReal3 →
          LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) →
          (∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q (c 0) hQ)
            (integerTripleReal3 (u j : IntegerTriple)) =
              successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q (c 0) hQ) j) →
          successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q (c 0) hQ) 1 < Q^(-deltaSource) →
      ∀ s ∈ S, cofactorSelectedProduct3 k₀ k₂ k₃ s
        (dualFrameVector3 (fun j => (u j : IntegerTriple)) 2) = 0 := by
  obtain ⟨B0,hB0⟩ := cofactorSelectedBadQ3_bddAbove k₀ k₂ k₃ S hS deltaSource hd
  refine ⟨max 1 B0,le_max_left _ _,?_⟩
  intro Q hcut hQ c hc ht B u hB hu hatt hsmall s hs
  have hJ := source_attaining_frame_index_le_six3 _ B _ u hB hu hatt
  by_contra hnz
  have hbad : Q ∈ cofactorSelectedBadQ3 k₀ k₂ k₃ S deltaSource :=
    ⟨hQ,c,hc,ht,B,u,hB,hu,hatt,hJ,hsmall,s,hs,hnz⟩
  exact (not_lt_of_ge (hB0 hbad)) (lt_of_le_of_lt (le_max_right _ _) hcut)


end
end JSP000334
