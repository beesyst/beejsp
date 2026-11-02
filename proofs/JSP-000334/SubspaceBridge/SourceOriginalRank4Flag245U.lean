import SubspaceBridge.SourceBlockFixedLine245U
import SubspaceBridge.SourceBlockRecovery245U
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.BlockRank4_245U
open BlockReduction245P BlockReduction245Q SourceFlag241

theorem source_original_fixed_rank4_245
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c0 c2 c3 : Fin 5 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (delta : ℝ) (hd : 0 < delta) (Omega : Set ℝ) (hO : ¬ BddAbove Omega)
    (hq : ∀ Q ∈ Omega, 1 < Q)
    (hgap : ∀ (Q : ℝ) (hQO : Q ∈ Omega),
      sourceMinima5 A2 A3 L hL Q (hq Q hQO) c0 c2 c3 3 <
        sourceMinima5 A2 A3 L hL Q (hq Q hQO) c0 c2 c3 4*Q^(-delta)) :
    ∃ P : Submodule ℚ (Fin 5 → ℚ), Module.finrank ℚ P = 4 ∧
      ∃ V : Set ℝ, ∃ hVO : V ⊆ Omega, ¬ BddAbove V ∧
        ∀ (Q : ℝ) (hQV : Q ∈ V),
          ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
            LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
            (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q (hq Q (hVO hQV)) c0)
              (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q (hq Q (hVO hQV)) c0 c2 c3 i) ∧
            P = Submodule.span ℚ (Set.range
              (fun j : Fin 4 => fun i => ((u (j.castSucc) : Fin 5 → ℤ) i : ℚ))) := by
  obtain ⟨D,Tsep,hD,hTs,hsep⟩ := source_separation245Q L hL
  obtain ⟨T0,hT0,b,hbn,Vprime,hVP,hVp,V,hVO,hV,hfixed⟩ :=
    source_block_fixed_line245U A2 A3 L h2d h3d hLd hL hAlg c0 c2 c3
      hc0 hc2 hc3 hb delta hd Omega hO hq hgap
  let U : Set ℝ := {Q | Q ∈ V ∧ Tsep < Q}
  have hU : ¬ BddAbove U := JSP000334.sourceDual_unbounded_tail3 V hV Tsep
  have hUO : U ⊆ Omega := fun _ h => hVO h.1
  have hlocal (Q : ℝ) (hQU : Q ∈ U) :
      ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
        LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
        (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q (hq Q (hUO hQU)) c0)
          (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q (hq Q (hUO hQU)) c0 c2 c3 i) ∧
        (∀ i, second245Q b i = 0) ∧
        (∀ j : Fin 4, originalNormal245U b (fun i => ((u j.castSucc : Fin 5 → ℤ) i : ℚ)) = 0) := by
    obtain ⟨p,hpV,hpEq,hp,w,hw,hatt,hpowered,hline⟩ := hfixed Q hQU.1
    rcases p with ⟨p,hpP⟩
    change p = Q^3 at hpEq
    subst p
    exact sameQ_annihilation245U A2 A3 L hL Q (hq Q (hUO hQU)) c0 c2 c3 delta hd
      (hgap Q (hUO hQU)) ((hsep A2 A3 Q (hq Q (hUO hQU)) c0 c2 c3 hc0).2 hQU.2)
      b w hw hatt hpowered hline
  obtain ⟨Q0,hQ0,hQ0large⟩ := not_bddAbove_iff.mp hU 0
  obtain ⟨u0,hu0,ha0,hdummy0,hann0⟩ := hlocal Q0 hQ0
  have hb5 := original_nonzero245U b hbn hdummy0
  refine ⟨LinearMap.ker (originalNormal245U b),original_kernel_rank245U b hb5,U,hUO,hU,?_⟩
  intro Q hQU
  obtain ⟨u,hu,ha,hdummy,hann⟩ := hlocal Q hQU
  exact ⟨u,hu,ha,original_kernel_span245U b hb5 _ (original_rational_independent241 _ hu) hann⟩

end CompoundFeasibility.BlockRank4_245U
