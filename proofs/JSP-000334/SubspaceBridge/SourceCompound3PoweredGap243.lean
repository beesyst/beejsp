import SubspaceBridge.SourceCubeDomain243
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.CompoundLine53_243
open Exterior53_242

theorem source_powered_gap243 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1)
    (hL : IsUnit L) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c0 c2 c3 : Fin 5 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (Q : ℝ) (hQ : 1 < Q), T < Q →
      sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 1 <
        sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 2*Q^(-delta) →
      ∀ (p : ℝ) (hp : 1 < p), Q^3 = p →
        sourceMinima10 (compound3242 A2) (compound3242 A3) (compound3242 L) (compound_real_unit3242 L hL)
          p hp (normalizedWeights3242 c0) (normalizedWeights3242 c2) (normalizedWeights3242 c3) 8 <
        sourceMinima10 (compound3242 A2) (compound3242 A3) (compound3242 L) (compound_real_unit3242 L hL)
          p hp (normalizedWeights3242 c0) (normalizedWeights3242 c2) (normalizedWeights3242 c3) 9*p^(-(delta/6)) := by
  obtain ⟨_,_,_,_,_,_,_,hall⟩ := source_rank2_compound_gap3242 A2 A3 L h2d h3d hLd hL hAlg
  obtain ⟨T,hT,_,hs⟩ := hall delta hd
  refine ⟨T,hT,?_⟩
  intro Q hQ hTQ hg p hp he
  subst p
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hgap⟩ := hs Q hQ c0 c2 c3 hc0 hc2 hc3 hb hTQ hg
  simpa only [neg_div] using hgap

theorem exists_compound3_attaining_family243 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 5 → ℝ)
    (P : Set ℝ) (hp : ∀ p ∈ P, 1 < p) :
    ∃ w : ∀ p : P, Fin 10 → originalSourceGroup10 (compound3242 A2) (compound3242 A3) p.val
      (normalizedWeights3242 c2) (normalizedWeights3242 c3),
      (∀ p : P, LinearIndependent ℝ (fun j => integerReal (w p j : Fin 10 → ℤ))) ∧
      ∀ (p : P) j, coordinateGauge10
        (originalCoordinates10 (compound3242 L) (compound_real_unit3242 L hL) p.val (hp p.val p.property)
          (normalizedWeights3242 c0)) (integerReal (w p j : Fin 10 → ℤ)) =
        sourceMinima10 (compound3242 A2) (compound3242 A3) (compound3242 L) (compound_real_unit3242 L hL)
          p.val (hp p.val p.property) (normalizedWeights3242 c0) (normalizedWeights3242 c2) (normalizedWeights3242 c3) j := by
  have he (p : P) := exists_sourceMinima10_attaining (compound3242 A2) (compound3242 A3)
    (compound3242 L) (compound_real_unit3242 L hL) p.val (hp p.val p.property)
    (normalizedWeights3242 c0) (normalizedWeights3242 c2) (normalizedWeights3242 c3)
  choose w hw hpos hmono hatt hpoint using he
  exact ⟨w,hw,hatt⟩

end CompoundFeasibility.CompoundLine53_243
