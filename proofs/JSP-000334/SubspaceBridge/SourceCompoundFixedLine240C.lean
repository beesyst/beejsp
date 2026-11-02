import SubspaceBridge.SourceCompoundPoweredGap240C
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.CompoundCore240C
open Exterior52_237 Exterior52_238 CompoundLine52_240 OriginalDual10 SourceOriginalDual10

theorem source_compound_fixed_line_conditional240C
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
    (hB2 : (compound237 A2).det = 1) (hB3 : (compound237 A3).det = 1)
    (hB0 : (compound237 L).det = 1) :
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
  obtain ⟨T,hT,hcut⟩ := source_powered_gap240C A2 A3 L h2d h3d hLd hL hAlg c0 c2 c3 hc0 hc2 hc3 hb delta hd
  let U : Set ℝ := {Q | Q ∈ Omega ∧ T < Q}
  have hU : ¬ BddAbove U := JSP000334.sourceDual_unbounded_tail3 Omega hO T
  have hUO : U ⊆ Omega := fun _ h => h.1
  have hqU : ∀ Q ∈ U, 1 < Q := fun Q h => hq Q h.1
  let P := squareDomain240 U
  have hP : ¬ BddAbove P := squareDomain_unbounded240 U hU hqU
  have hp : ∀ p ∈ P, 1 < p := squareDomain_positive240 U hqU
  obtain ⟨lift,hlift⟩ := exists_square_section240 U
  obtain ⟨w,hw,hatt⟩ := exists_compound_attaining_family240C A2 A3 L hL c0 c2 c3 P hp
  have hg (p : P) :
      sourceMinima10 (compound237 A2) (compound237 A3) (compound237 L) (compound_real_unit240 L hL)
        p.val (hp p.val p.property) (normalizedWeights238 c0) (normalizedWeights238 c2) (normalizedWeights238 c3) 8 <
      sourceMinima10 (compound237 A2) (compound237 A3) (compound237 L) (compound_real_unit240 L hL)
        p.val (hp p.val p.property) (normalizedWeights238 c0) (normalizedWeights238 c2) (normalizedWeights238 c3) 9*
          p.val^(-(delta/4)) :=
    hcut (lift p).val (hqU _ (lift p).property) (lift p).property.2
      (hgap _ (lift p).property.1) p.val (hp p.val p.property) (hlift p)
  obtain ⟨hc0p,hc2p,hc3p,hbp⟩ := compound_weights240 c0 c2 c3 hc0 hc2 hc3 hb
  obtain ⟨b,hbn,Vprime,hVP,hVprime,hline⟩ := SourceRatioLine236.source_ratio_fixed_line236
    (compound237 A2) (compound237 A3) (compound237 L) hB2 hB3 hB0 (compound_real_unit240 L hL)
    (compound_real_algebraic240 L hAlg) (normalizedWeights238 c0) (normalizedWeights238 c2)
    (normalizedWeights238 c3) hc0p hc2p hc3p hbp (delta/4) (by positivity) P hP hp w hw hatt hg
  let V : Set ℝ := {Q | ∃ p : P, p.val ∈ Vprime ∧ (lift p).val = Q}
  refine ⟨T,hT,b,hbn,Vprime,hVP,hVprime,V,?_,
    square_pullback_unbounded240 U hqU lift hlift Vprime hVP hVprime,?_⟩
  · rintro Q ⟨p,hpV,rfl⟩
    exact hUO (lift p).property
  · intro Q hQV
    obtain ⟨p,hpV,he⟩ := hQV
    refine ⟨p,hpV,?_,hp p.val p.property,w p,hw p,hatt p,hline p hpV⟩
    exact (hlift p).symm.trans (congrArg (fun x : ℝ => x^2) he)

end CompoundFeasibility.CompoundCore240C
