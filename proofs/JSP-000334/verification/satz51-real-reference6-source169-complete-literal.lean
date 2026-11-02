import SubspaceBridge.OriginalMinimaProduct4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Product169Literal
open OriginalMinimaProduct4

theorem source_signature_literal
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ c4 C4 : ℝ, 0 < c4 ∧ 0 < C4 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ),
        (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) →
        (∑ i, (c0 i+c2 i+c3 i) = 0) →
        c4 ≤ (∏ i : Fin 4, sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 i) ∧
          (∏ i : Fin 4, sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 i) ≤ C4 := by
  exact source_original_uniform_minima_two_sided4 A2 A3 L h2 h3 hL

theorem complete_literal
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ c4 C4 : ℝ, 0 < c4 ∧ 0 < C4 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ),
        (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) →
        (∑ i, (c0 i+c2 i+c3 i) = 0) →
        let G := sourceLattice4 A2 A3
          (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))
        let lambda := fun j : Fin 4 => sInf {r : ℝ |
          ∃ u : Fin (j.val+1) → (Fin 4 → ℝ), LinearIndependent ℝ u ∧
            (∀ i, ∃ z : Fin 4 → ℤ, z ∈ G ∧ integerReal z = u i) ∧
            ∀ i, ‖originalCoordinates4 L hL Q hQ c0 (u i)‖ ≤ r}
        0 < lambda 0 ∧ 0 < lambda 1 ∧ 0 < lambda 2 ∧ 0 < lambda 3 ∧
          c4 ≤ lambda 0 * lambda 1 * lambda 2 * lambda 3 ∧
          lambda 0 * lambda 1 * lambda 2 * lambda 3 ≤ C4 := by
  obtain ⟨c4,C4,hc4,hC4,hbounds⟩ := source_original_uniform_minima_two_sided4 A2 A3 L h2 h3 hL
  refine ⟨c4,C4,hc4,hC4,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb
  dsimp only
  change 0 < sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 0 ∧
    0 < sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 1 ∧
    0 < sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 2 ∧
    0 < sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 3 ∧ _
  have hp := (sourceMinima4_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1
  refine ⟨hp 0,hp 1,hp 2,hp 3,?_⟩
  have he (a : Fin 4 → ℝ) : (∏ i, a i) = a 0*a 1*a 2*a 3 := by
    simp [Fin.prod_univ_succ,mul_assoc]
  have h := hbounds Q hQ c0 c2 c3 hc2 hc3 hb
  rw [he] at h
  exact h

end CompoundFeasibility.Product169Literal
#check CompoundFeasibility.Product169Literal.source_signature_literal
#print CompoundFeasibility.Product169Literal.source_signature_literal
#print axioms CompoundFeasibility.Product169Literal.source_signature_literal
#check CompoundFeasibility.Product169Literal.complete_literal
#print CompoundFeasibility.Product169Literal.complete_literal
#print axioms CompoundFeasibility.Product169Literal.complete_literal
