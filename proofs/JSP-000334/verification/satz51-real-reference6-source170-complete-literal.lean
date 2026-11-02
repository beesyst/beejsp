import SubspaceBridge.OriginalVariableGap4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.VariableGap170Literal
open OriginalVariableGap4

theorem source_signature_literal
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L)
    (c0 c2 c3 : Fin 4 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (hb : ∑ i, (c0 i+c2 i+c3 i) = 0)
    (hn : ¬ originalRothProperty4 A2 A3 L c0 c2 c3) :
    ∃ epsilon deltaGap c4 C4 B : ℝ, ∃ U V : Set ℝ, ∃ j : Fin 3,
      0 < epsilon ∧ deltaGap = (epsilon/2)/4 ∧ 0 < deltaGap ∧
      0 < c4 ∧ 0 < C4 ∧ 1 < B ∧
      U = {Q : ℝ | ∃ x : Fin 4 → ℤ,
        originalSourceSolution4 A2 A3 L c0 c2 c3 Q epsilon x} ∧
      ¬ BddAbove U ∧
      (∀ Q ∈ U, ∃ hQ : 1 < Q, ∃ x : Fin 4 → ℤ,
        originalSourceSolution4 A2 A3 L c0 c2 c3 Q epsilon x ∧
        x ∈ originalSourceGroup4 A2 A3 Q c2 c3 ∧
        coordinateGauge4 (originalCoordinates4 L hL Q hQ c0) (integerReal x) ≤ Q^(-epsilon) ∧
        sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 0 < Q^(-(epsilon/2))) ∧
      (∀ (Q : ℝ) (hQ : 1 < Q),
        c4 ≤ (∏ i : Fin 4, sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 i) ∧
        (∏ i : Fin 4, sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 i) ≤ C4) ∧
      V ⊆ U ∧ ¬ BddAbove V ∧ 1 ≤ j.val+1 ∧ j.val+1 ≤ 3 ∧
      ∀ Q ∈ V, B < Q ∧ ∃ hQ : 1 < Q,
        sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc <
          sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j.succ * Q^(-deltaGap) := by
  exact source_original_nonroth_gap4 A2 A3 L h2 h3 hL c0 c2 c3 hc2 hc3 hb hn

theorem complete_literal
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L)
    (c0 c2 c3 : Fin 4 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (hb : ∑ i, (c0 i+c2 i+c3 i) = 0)
    (hn : ¬ (∀ delta : ℝ, 0 < delta → ∃ B : ℝ, ∀ Q : ℝ, B < Q →
      ¬ ∃ x : Fin 4 → ℤ, (x ≠ 0 ∧ 1 < Q ∧ 0 < delta ∧
    (∀ i, |(L *ᵥ integerReal x) i| ≤ Q^(c0 i-delta)) ∧
    (∀ i, (padicNorm 2 ((A2 *ᵥ (fun j => (x j : ℚ))) i) : ℝ) ≤ Q^(c2 i)) ∧
    (∀ i, (padicNorm 3 ((A3 *ᵥ (fun j => (x j : ℚ))) i) : ℝ) ≤ Q^(c3 i))))) :
    ∃ epsilon deltaGap c4 C4 B : ℝ, ∃ U V : Set ℝ, ∃ j : Fin 3,
      0 < epsilon ∧ deltaGap = (epsilon/2)/4 ∧ 0 < deltaGap ∧
      0 < c4 ∧ 0 < C4 ∧ 1 < B ∧
      U = {Q : ℝ | ∃ x : Fin 4 → ℤ,
        (x ≠ 0 ∧ 1 < Q ∧ 0 < epsilon ∧
    (∀ i, |(L *ᵥ integerReal x) i| ≤ Q^(c0 i-epsilon)) ∧
    (∀ i, (padicNorm 2 ((A2 *ᵥ (fun j => (x j : ℚ))) i) : ℝ) ≤ Q^(c2 i)) ∧
    (∀ i, (padicNorm 3 ((A3 *ᵥ (fun j => (x j : ℚ))) i) : ℝ) ≤ Q^(c3 i)))} ∧
      ¬ BddAbove U ∧
      (∀ Q ∈ U, ∃ hQ : 1 < Q, ∃ x : Fin 4 → ℤ,
        (x ≠ 0 ∧ 1 < Q ∧ 0 < epsilon ∧
    (∀ i, |(L *ᵥ integerReal x) i| ≤ Q^(c0 i-epsilon)) ∧
    (∀ i, (padicNorm 2 ((A2 *ᵥ (fun j => (x j : ℚ))) i) : ℝ) ≤ Q^(c2 i)) ∧
    (∀ i, (padicNorm 3 ((A3 *ᵥ (fun j => (x j : ℚ))) i) : ℝ) ≤ Q^(c3 i))) ∧
        x ∈ (sourceLattice4 A2 A3 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))) ∧
        ‖originalCoordinates4 L hL Q hQ c0 (integerReal x)‖ ≤ Q^(-epsilon) ∧
        (sInf {r : ℝ | ∃ u : Fin ((0 : Fin 4).val+1) → (Fin 4 → ℝ),
          LinearIndependent ℝ u ∧
          (∀ i, ∃ z : Fin 4 → ℤ, z ∈ (sourceLattice4 A2 A3 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))) ∧ integerReal z = u i) ∧
          ∀ i, ‖originalCoordinates4 L hL Q hQ c0 (u i)‖ ≤ r}) < Q^(-(epsilon/2))) ∧
      (∀ (Q : ℝ) (hQ : 1 < Q),
        c4 ≤ ((sInf {r : ℝ | ∃ u : Fin ((0 : Fin 4).val+1) → (Fin 4 → ℝ),
          LinearIndependent ℝ u ∧
          (∀ i, ∃ z : Fin 4 → ℤ, z ∈ (sourceLattice4 A2 A3 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))) ∧ integerReal z = u i) ∧
          ∀ i, ‖originalCoordinates4 L hL Q hQ c0 (u i)‖ ≤ r}) * (sInf {r : ℝ | ∃ u : Fin ((1 : Fin 4).val+1) → (Fin 4 → ℝ),
          LinearIndependent ℝ u ∧
          (∀ i, ∃ z : Fin 4 → ℤ, z ∈ (sourceLattice4 A2 A3 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))) ∧ integerReal z = u i) ∧
          ∀ i, ‖originalCoordinates4 L hL Q hQ c0 (u i)‖ ≤ r}) * (sInf {r : ℝ | ∃ u : Fin ((2 : Fin 4).val+1) → (Fin 4 → ℝ),
          LinearIndependent ℝ u ∧
          (∀ i, ∃ z : Fin 4 → ℤ, z ∈ (sourceLattice4 A2 A3 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))) ∧ integerReal z = u i) ∧
          ∀ i, ‖originalCoordinates4 L hL Q hQ c0 (u i)‖ ≤ r}) * (sInf {r : ℝ | ∃ u : Fin ((3 : Fin 4).val+1) → (Fin 4 → ℝ),
          LinearIndependent ℝ u ∧
          (∀ i, ∃ z : Fin 4 → ℤ, z ∈ (sourceLattice4 A2 A3 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))) ∧ integerReal z = u i) ∧
          ∀ i, ‖originalCoordinates4 L hL Q hQ c0 (u i)‖ ≤ r})) ∧
        ((sInf {r : ℝ | ∃ u : Fin ((0 : Fin 4).val+1) → (Fin 4 → ℝ),
          LinearIndependent ℝ u ∧
          (∀ i, ∃ z : Fin 4 → ℤ, z ∈ (sourceLattice4 A2 A3 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))) ∧ integerReal z = u i) ∧
          ∀ i, ‖originalCoordinates4 L hL Q hQ c0 (u i)‖ ≤ r}) * (sInf {r : ℝ | ∃ u : Fin ((1 : Fin 4).val+1) → (Fin 4 → ℝ),
          LinearIndependent ℝ u ∧
          (∀ i, ∃ z : Fin 4 → ℤ, z ∈ (sourceLattice4 A2 A3 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))) ∧ integerReal z = u i) ∧
          ∀ i, ‖originalCoordinates4 L hL Q hQ c0 (u i)‖ ≤ r}) * (sInf {r : ℝ | ∃ u : Fin ((2 : Fin 4).val+1) → (Fin 4 → ℝ),
          LinearIndependent ℝ u ∧
          (∀ i, ∃ z : Fin 4 → ℤ, z ∈ (sourceLattice4 A2 A3 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))) ∧ integerReal z = u i) ∧
          ∀ i, ‖originalCoordinates4 L hL Q hQ c0 (u i)‖ ≤ r}) * (sInf {r : ℝ | ∃ u : Fin ((3 : Fin 4).val+1) → (Fin 4 → ℝ),
          LinearIndependent ℝ u ∧
          (∀ i, ∃ z : Fin 4 → ℤ, z ∈ (sourceLattice4 A2 A3 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))) ∧ integerReal z = u i) ∧
          ∀ i, ‖originalCoordinates4 L hL Q hQ c0 (u i)‖ ≤ r})) ≤ C4) ∧
      V ⊆ U ∧ ¬ BddAbove V ∧ 1 ≤ j.val+1 ∧ j.val+1 ≤ 3 ∧
      ∀ Q ∈ V, B < Q ∧ ∃ hQ : 1 < Q,
        (sInf {r : ℝ | ∃ u : Fin ((j.castSucc : Fin 4).val+1) → (Fin 4 → ℝ),
          LinearIndependent ℝ u ∧
          (∀ i, ∃ z : Fin 4 → ℤ, z ∈ (sourceLattice4 A2 A3 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))) ∧ integerReal z = u i) ∧
          ∀ i, ‖originalCoordinates4 L hL Q hQ c0 (u i)‖ ≤ r}) <
          (sInf {r : ℝ | ∃ u : Fin ((j.succ : Fin 4).val+1) → (Fin 4 → ℝ),
          LinearIndependent ℝ u ∧
          (∀ i, ∃ z : Fin 4 → ℤ, z ∈ (sourceLattice4 A2 A3 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))) ∧ integerReal z = u i) ∧
          ∀ i, ‖originalCoordinates4 L hL Q hQ c0 (u i)‖ ≤ r}) * Q^(-deltaGap) := by
  have he (a : Fin 4 → ℝ) : (∏ i, a i) = a 0*a 1*a 2*a 3 := by
    simp [Fin.prod_univ_succ, mul_assoc]
  simpa only [he] using
    (source_original_nonroth_gap4 A2 A3 L h2 h3 hL c0 c2 c3 hc2 hc3 hb hn)

end CompoundFeasibility.VariableGap170Literal
#check CompoundFeasibility.VariableGap170Literal.source_signature_literal
#print CompoundFeasibility.VariableGap170Literal.source_signature_literal
#print axioms CompoundFeasibility.VariableGap170Literal.source_signature_literal
#check CompoundFeasibility.VariableGap170Literal.complete_literal
#print CompoundFeasibility.VariableGap170Literal.complete_literal
#print axioms CompoundFeasibility.VariableGap170Literal.complete_literal
