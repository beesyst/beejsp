import SubspaceBridge.SourcePoweredRank4_247
import SubspaceBridge.SourceSameQRecovery247
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag247
open Exterior54_246

theorem original_head_control247 (u : Fin 5 → Fin 5 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j)))
    (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : P = Submodule.span ℚ {fun i => (u 0 i : ℚ)}) :
    u 0 ≠ 0 ∧ (fun i => (u 0 i : ℚ)) ≠ 0 ∧ (fun i => (u 0 i : ℚ)) ∈ P := by
  have hr := SourceFlag241.original_rational_independent241 u hu
  refine ⟨?_,hr.ne_zero 0,?_⟩
  · intro hz
    apply hu.ne_zero 0
    rw [hz, map_zero]
  · rw [hP]
    exact Submodule.subset_span (Set.mem_singleton _)

theorem source_original_fixed_rank1_247
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c0 c2 c3 : Fin 5 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (delta : ℝ) (hd : 0 < delta) (Omega : Set ℝ) (hO : ¬ BddAbove Omega)
    (hq : ∀ Q ∈ Omega, 1 < Q)
    (hgap : ∀ (Q : ℝ) (hQO : Q ∈ Omega),
      sourceMinima5 A2 A3 L hL Q (hq Q hQO) c0 c2 c3 0 <
        sourceMinima5 A2 A3 L hL Q (hq Q hQO) c0 c2 c3 1*Q^(-delta)) :
    ∃ P : Submodule ℚ (Fin 5 → ℚ), Module.finrank ℚ P = 1 ∧
      ∃ V : Set ℝ, ∃ hVO : V ⊆ Omega, ¬ BddAbove V ∧
        ∀ (Q : ℝ) (hQV : Q ∈ V),
          ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
            LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
            (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q (hq Q (hVO hQV)) c0)
              (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q (hq Q (hVO hQV)) c0 c2 c3 i) ∧
            P = Submodule.span ℚ {fun i => ((u 0 : Fin 5 → ℤ) i : ℚ)} := by
  have h2 : IsUnit A2 := (Matrix.isUnit_iff_isUnit_det A2).mpr (by rw [h2d]; exact isUnit_one)
  have h3 : IsUnit A3 := (Matrix.isUnit_iff_isUnit_det A3).mpr (by rw [h3d]; exact isUnit_one)
  obtain ⟨C,c,kappa,hC,hc,hk,he,hcompare⟩ := source_uniform_comparison4246 A2 A3 L h2 h3 hL
  obtain ⟨Tshort,hTshort,hcut⟩ := short_four_cutoff247 kappa delta hd
  obtain ⟨H,hH,V,hVO,hV,hfixed⟩ := powered_fixed_rank4_247 A2 A3 L h2d h3d hLd hL hAlg
    c0 c2 c3 hc0 hc2 hc3 hb delta hd Omega hO hq hgap Tshort
  refine ⟨annihilator247 H,annihilator_rank247 H hH,V,hVO,hV,?_⟩
  intro Q hQV
  obtain ⟨hlarge,w,hw,ha,hspan⟩ := hfixed Q hQV
  exact sameQ_rank1_recovery247 A2 A3 L hL Q (hq Q (hVO hQV)) c0 c2 c3 kappa delta hk
    (hcut Q hlarge) (hgap Q (hVO hQV))
    ((hcompare Q (hq Q (hVO hQV)) c0 c2 c3 (fun i => (hc2 i).2) (fun i => (hc3 i).2) hb 4).1)
    H hH w hw ha hspan

end CompoundFeasibility.SourceFlag247
