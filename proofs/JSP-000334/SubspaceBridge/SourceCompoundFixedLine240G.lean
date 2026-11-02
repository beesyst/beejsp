import SubspaceBridge.SourceCompoundConcrete240G
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.CompoundConcrete240G
open Exterior52_237 Exterior52_238 CompoundLine52_240 OriginalDual10 SourceOriginalDual10

theorem source_compound_fixed_line240G
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c0 c2 c3 : Fin 5 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (delta : ℝ) (hd : 0 < delta) (Omega : Set ℝ) (hO : ¬ BddAbove Omega)
    (hq : ∀ Q ∈ Omega, 1 < Q)
    (hgap : ∀ (Q : ℝ) (hQO : Q ∈ Omega),
      sourceMinima5 A2 A3 L hL Q (hq Q hQO) c0 c2 c3 2 <
        sourceMinima5 A2 A3 L hL Q (hq Q hQO) c0 c2 c3 3*Q^(-delta))
    :
    ∃ T : ℝ, 1 < T ∧ ∃ b : Fin 10 → ℤ, b ≠ 0 ∧ ∃ Vprime : Set ℝ,
      Vprime ⊆ squareDomain240 {Q | Q ∈ Omega ∧ T < Q} ∧ ¬ BddAbove Vprime ∧
      ∃ V : Set ℝ, V ⊆ Omega ∧ ¬ BddAbove V ∧
        ∀ Q ∈ V, ∃ p : squareDomain240 {Q | Q ∈ Omega ∧ T < Q},
          p.val ∈ Vprime ∧ p.val = Q^2 ∧ ∃ hp : 1 < p.val,
          ∃ w : Fin 10 → originalSourceGroup10 (compound237 A2) (compound237 A3) p.val
            (normalizedWeights238 c2) (normalizedWeights238 c3),
          ∃ hw : LinearIndependent ℝ (fun j => integerReal (w j : Fin 10 → ℤ)),
            (∀ j, coordinateGauge10 (originalCoordinates10 (compound237 L) (compound_real_unit240 L hL)
              p.val hp (normalizedWeights238 c0)) (integerReal (w j : Fin 10 → ℤ)) =
              sourceMinima10 (compound237 A2) (compound237 A3) (compound237 L) (compound_real_unit240 L hL)
                p.val hp (normalizedWeights238 c0) (normalizedWeights238 c2) (normalizedWeights238 c3) j) ∧
            Submodule.span ℚ {lastDual10 (fun j i => ((w j : Fin 10 → ℤ) i : ℚ))
              (integer_frame_rational_independent10 _ hw)} = Submodule.span ℚ {fun i => (b i : ℚ)} := by
  have hB2 : (compound237 A2).det = 1 := compound_rat_det_one240G A2 h2d
  have hB3 : (compound237 A3).det = 1 := compound_rat_det_one240G A3 h3d
  have hB0 : (compound237 L).det = 1 := compound_real_det_one240G L hLd
  exact CompoundCore240C.source_compound_fixed_line_conditional240C
    A2 A3 L h2d h3d hLd hL hAlg c0 c2 c3 hc0 hc2 hc3 hb delta hd Omega hO hq hgap
    hB2 hB3 hB0

end CompoundFeasibility.CompoundConcrete240G
