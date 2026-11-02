import SubspaceBridge.SourceWedgeRadical241
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag241
open Exterior52_237 Exterior52_238 ExteriorGap52_239 CompoundConcrete240G

theorem source_original_fixed_rank3_241
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c0 c2 c3 : Fin 5 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (delta : ℝ) (hd : 0 < delta) (Omega : Set ℝ) (hO : ¬ BddAbove Omega)
    (hq : ∀ Q ∈ Omega, 1 < Q)
    (hgap : ∀ (Q : ℝ) (hQO : Q ∈ Omega),
      sourceMinima5 A2 A3 L hL Q (hq Q hQO) c0 c2 c3 2 <
        sourceMinima5 A2 A3 L hL Q (hq Q hQO) c0 c2 c3 3*Q^(-delta)) :
    ∃ P : Submodule ℚ (Fin 5 → ℚ), Module.finrank ℚ P = 3 ∧
      ∃ V : Set ℝ, ∃ hVO : V ⊆ Omega, ¬ BddAbove V ∧
        ∀ (Q : ℝ) (hQV : Q ∈ V),
          ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
            LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
            (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q (hq Q (hVO hQV)) c0)
              (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q (hq Q (hVO hQV)) c0 c2 c3 i) ∧
            P = Submodule.span ℚ (Set.range
              (fun j : Fin 3 => fun i => ((u (Fin.castLE (by decide) j) : Fin 5 → ℤ) i : ℚ))) := by
  have h2 : IsUnit A2 := (Matrix.isUnit_iff_isUnit_det A2).mpr (by rw [h2d]; exact isUnit_one)
  have h3 : IsUnit A3 := (Matrix.isUnit_iff_isUnit_det A3).mpr (by rw [h3d]; exact isUnit_one)
  obtain ⟨C5,c10,kappa,hC,hc,hk,he,huniform⟩ := source_uniform_gap239 A2 A3 L h2 h3 hL
  obtain ⟨Tgap,hTgap,hg⟩ := huniform delta hd
  obtain ⟨Tshort,hTshort,hshort⟩ := short_wedge_cutoff241 kappa delta hd
  obtain ⟨T0,hT0,b,hbn,Vprime,hVP,hVp,V,hVO,hV,hfixed⟩ :=
    source_compound_fixed_line240G A2 A3 L h2d h3d hLd hL hAlg c0 c2 c3
      hc0 hc2 hc3 hb delta hd Omega hO hq hgap
  let U : Set ℝ := {Q | Q ∈ V ∧ max Tgap Tshort < Q}
  have hU : ¬ BddAbove U := JSP000334.sourceDual_unbounded_tail3 V hV (max Tgap Tshort)
  have hUO : U ⊆ Omega := fun _ h => hVO h.1
  have hlocal (Q : ℝ) (hQU : Q ∈ U) :
      ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
        LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
        (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q (hq Q (hUO hQU)) c0)
          (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q (hq Q (hUO hQU)) c0 c2 c3 i) ∧
        radical241 b = Submodule.span ℚ (Set.range
          (fun j : Fin 3 => fun i => ((u (Fin.castLE (by decide) j) : Fin 5 → ℤ) i : ℚ))) ∧
        Module.finrank ℚ (radical241 b) = 3 := by
    have hsource := hgap Q (hUO hQU)
    obtain ⟨hcomp,hpowgap⟩ := hg Q (hq Q (hUO hQU)) c0 c2 c3
      (fun i => (hc2 i).2) (fun i => (hc3 i).2) hb ((le_max_left _ _).trans_lt hQU.2) hsource
    obtain ⟨p,hpV,hpEq,hp,w,hw,hatt,hline⟩ := hfixed Q hQU.1
    rcases p with ⟨p,hpP⟩
    change p = Q^2 at hpEq
    subst p
    exact sameQ_radical_recovery241 A2 A3 L hL Q (hq Q (hUO hQU)) c0 c2 c3
      kappa delta hk hd (hshort Q ((le_max_right _ _).trans_lt hQU.2)) (hcomp 8).1 hpowgap
      hsource b hbn w hw hatt hline
  obtain ⟨Q0,hQ0,hQ0large⟩ := not_bddAbove_iff.mp hU 0
  obtain ⟨u0,hu0,ha0,hP0,hrank⟩ := hlocal Q0 hQ0
  refine ⟨radical241 b,hrank,U,hUO,hU,?_⟩
  intro Q hQU
  obtain ⟨u,hu,ha,hP,hr⟩ := hlocal Q hQU
  exact ⟨u,hu,ha,hP⟩

end CompoundFeasibility.SourceFlag241
