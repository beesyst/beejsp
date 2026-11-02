import SubspaceBridge.SourceCompoundGap52_239
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.CompoundLine52_240
open Exterior52_237 Exterior52_238

theorem compound_real_algebraic240 (L : Matrix (Fin 5) (Fin 5) ℝ)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∀ s t, IsAlgebraic ℚ (compound237 L s t) := compound_algebraic238 L hAlg

theorem compound_real_unit240 (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) :
    IsUnit (compound237 L) := compound_unit238 L hL

theorem compound_weights240 (c0 c2 c3 : Fin 5 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0) :
    (∀ s, |normalizedWeights238 c0 s| ≤ 1) ∧
    (∀ s, -1 ≤ normalizedWeights238 c2 s ∧ normalizedWeights238 c2 s ≤ 0) ∧
    (∀ s, -1 ≤ normalizedWeights238 c3 s ∧ normalizedWeights238 c3 s ≤ 0) ∧
    (∑ s, (normalizedWeights238 c0 s+normalizedWeights238 c2 s+normalizedWeights238 c3 s)) = 0 :=
  ⟨normalized_real_bound238 c0 hc0,normalized_finite_bounds238 c2 hc2,
    normalized_finite_bounds238 c3 hc3,normalized_balance238 c0 c2 c3 hb⟩

end CompoundFeasibility.CompoundLine52_240
