import SubspaceBridge.SourceBlockGap245R
import SubspaceBridge.SourceBlockConcrete245T
import SubspaceBridge.SourceCubeDomain243
import SubspaceBridge.SourceRatioLine236
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.BlockRank4_245U
open Exterior53_242 OriginalDual10 SourceOriginalDual10 CompoundLine53_243
  BlockReduction245P BlockReduction245Q BlockReduction245R BlockConcrete245T

theorem source_block_fixed_line245U
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c0 c2 c3 : Fin 5 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (delta : ℝ) (hd : 0 < delta) (Omega : Set ℝ) (hO : ¬ BddAbove Omega)
    (hq : ∀ Q ∈ Omega, 1 < Q)
    (hgap : ∀ (Q : ℝ) (hQO : Q ∈ Omega),
      sourceMinima5 A2 A3 L hL Q (hq Q hQO) c0 c2 c3 3 <
        sourceMinima5 A2 A3 L hL Q (hq Q hQO) c0 c2 c3 4*Q^(-delta))
    :
    ∃ T : ℝ, 1 < T ∧ ∃ b : Fin 10 → ℤ, b ≠ 0 ∧ ∃ Vprime : Set ℝ,
      Vprime ⊆ cubeDomain243 {Q | Q ∈ Omega ∧ T < Q} ∧ ¬ BddAbove Vprime ∧
      ∃ V : Set ℝ, V ⊆ Omega ∧ ¬ BddAbove V ∧
        ∀ Q ∈ V, ∃ p : cubeDomain243 {Q | Q ∈ Omega ∧ T < Q},
          p.val ∈ Vprime ∧ p.val = Q^3 ∧ ∃ hp : 1 < p.val,
          ∃ w : Fin 10 → originalSourceGroup10 (block245P A2) (block245P A3) p.val
            (weightp245P c2) (weightp245P c3),
          ∃ hw : LinearIndependent ℝ (fun j => integerReal (w j : Fin 10 → ℤ)),
            (∀ j, coordinateGauge10 (originalCoordinates10 (block245P L) (block_unit245Q L hL)
              p.val hp (weight0245P c0)) (integerReal (w j : Fin 10 → ℤ)) =
              sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
                p.val hp (weight0245P c0) (weightp245P c2) (weightp245P c3) j) ∧
            (sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
              p.val hp (weight0245P c0) (weightp245P c2) (weightp245P c3) 8 <
            sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
              p.val hp (weight0245P c0) (weightp245P c2) (weightp245P c3) 9*p.val^(-(delta/3))) ∧
            Submodule.span ℚ {lastDual10 (fun j i => ((w j : Fin 10 → ℤ) i : ℚ))
              (integer_frame_rational_independent10 _ hw)} = Submodule.span ℚ {fun i => (b i : ℚ)} := by
  obtain ⟨T,hT,hdp,hcut⟩ := source_block_gap245R A2 A3 L hL c0 c2 c3 hc0 delta hd
  let U : Set ℝ := {Q | Q ∈ Omega ∧ T < Q}
  have hU : ¬ BddAbove U := JSP000334.sourceDual_unbounded_tail3 Omega hO T
  have hUO : U ⊆ Omega := fun _ h => h.1
  have hqU : ∀ Q ∈ U, 1 < Q := fun Q h => hq Q h.1
  let P := cubeDomain243 U
  have hP : ¬ BddAbove P := cubeDomain_unbounded243 U hU hqU
  have hp : ∀ p ∈ P, 1 < p := cubeDomain_positive243 U hqU
  obtain ⟨lift,hlift⟩ := exists_cube_section243 U
  have hex (p : P) := exists_sourceMinima10_attaining (block245P A2) (block245P A3)
    (block245P L) (block_unit245Q L hL) p.val (hp p.val p.property)
    (weight0245P c0) (weightp245P c2) (weightp245P c3)
  choose w hw hpos hmono hatt hpoint using hex
  have hg (p : P) :
      sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
        p.val (hp p.val p.property) (weight0245P c0) (weightp245P c2) (weightp245P c3) 8 <
      sourceMinima10 (block245P A2) (block245P A3) (block245P L) (block_unit245Q L hL)
        p.val (hp p.val p.property) (weight0245P c0) (weightp245P c2) (weightp245P c3) 9*
          p.val^(-(delta/3)) := by
    have h := hcut (lift p).val (hqU _ (lift p).property) (lift p).property.2
      (hgap _ (lift p).property.1)
    simpa only [hlift p, neg_div] using h
  obtain ⟨hB2,hB3,hB0,hBU,hAlgB,hc0p,hc2p,hc3p,hbp⟩ :=
    source_block_prerequisites245T A2 A3 L h2d h3d hLd hL hAlg c0 c2 c3 hc0 hc2 hc3 hb
  obtain ⟨b,hbn,Vprime,hVP,hVprime,hline⟩ := SourceRatioLine236.source_ratio_fixed_line236
    (block245P A2) (block245P A3) (block245P L) hB2 hB3 hB0 (block_unit245Q L hL)
    hAlgB (weight0245P c0) (weightp245P c2)
    (weightp245P c3) hc0p hc2p hc3p hbp (delta/3) hdp P hP hp w hw hatt hg
  let V : Set ℝ := {Q | ∃ p : P, p.val ∈ Vprime ∧ (lift p).val = Q}
  refine ⟨T,hT,b,hbn,Vprime,hVP,hVprime,V,?_,
    cube_pullback_unbounded243 U hqU lift hlift Vprime hVP hVprime,?_⟩
  · rintro Q ⟨p,hpV,rfl⟩
    exact hUO (lift p).property
  · intro Q hQV
    obtain ⟨p,hpV,he⟩ := hQV
    refine ⟨p,hpV,?_,hp p.val p.property,w p,hw p,hatt p,hg p,hline p hpV⟩
    exact (hlift p).symm.trans (congrArg (fun x : ℝ => x^3) he)

end CompoundFeasibility.BlockRank4_245U
