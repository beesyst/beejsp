import SubspaceBridge.SourceFourthDomain247
import SubspaceBridge.SourceOriginalRank4Flag245U
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag247
open Exterior54_246

theorem powered_fixed_rank4_247
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c0 c2 c3 : Fin 5 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (delta : ℝ) (hd : 0 < delta) (Omega : Set ℝ) (hO : ¬ BddAbove Omega)
    (hq : ∀ Q ∈ Omega, 1 < Q)
    (hgap : ∀ (Q : ℝ) (hQO : Q ∈ Omega),
      sourceMinima5 A2 A3 L hL Q (hq Q hQO) c0 c2 c3 0 <
        sourceMinima5 A2 A3 L hL Q (hq Q hQO) c0 c2 c3 1*Q^(-delta)) (Tshort : ℝ) :
    ∃ H : Submodule ℚ (Fin 5 → ℚ), Module.finrank ℚ H = 4 ∧
      ∃ V : Set ℝ, ∃ hVO : V ⊆ Omega, ¬ BddAbove V ∧
        ∀ (Q : ℝ) (hQV : Q ∈ V), Tshort < Q ∧
          ∃ w : Fin 5 → originalSourceGroup5 (compound4246 A2) (compound4246 A3) (Q^4)
            (normalizedWeights4246 c2) (normalizedWeights4246 c3),
            LinearIndependent ℝ (fun j => integerReal (w j : Fin 5 → ℤ)) ∧
            (∀ j, coordinateGauge5 (originalCoordinates5 (compound4246 L) (compound_unit4246 L hL)
              (Q^4) (powered_gt_one4246 Q (hq Q (hVO hQV))) (normalizedWeights4246 c0))
              (integerReal (w j : Fin 5 → ℤ)) = compoundMinima4246 A2 A3 L hL Q
                (hq Q (hVO hQV)) c0 c2 c3 j) ∧
            H = Submodule.span ℚ (Set.range
              (fun j : Fin 4 => fun i => ((w j.castSucc : Fin 5 → ℤ) i : ℚ))) := by
  obtain ⟨C,c,kappa,hC,hc,hk,he,huniform⟩ :=
    source_rank1_compound4_gap246 A2 A3 L h2d h3d hLd hL hAlg
  obtain ⟨Tgap,hTgap,hdelta,hgate⟩ := huniform delta hd
  let U : Set ℝ := {Q | Q ∈ Omega ∧ max Tgap Tshort < Q}
  have hU : ¬ BddAbove U := JSP000334.sourceDual_unbounded_tail3 Omega hO (max Tgap Tshort)
  have hqU : ∀ Q ∈ U, 1 < Q := fun Q h => hq Q h.1
  let P := fourthDomain247 U
  have hP : ¬ BddAbove P := fourthDomain_unbounded247 U hU hqU
  have hp : ∀ p ∈ P, 1 < p := fourthDomain_positive247 U hqU
  obtain ⟨lift,hlift⟩ := exists_fourth_section247 U
  have hgp (p : ℝ) (hpP : p ∈ P) :
      sourceMinima5 (compound4246 A2) (compound4246 A3) (compound4246 L) (compound_unit4246 L hL)
        p (hp p hpP) (normalizedWeights4246 c0) (normalizedWeights4246 c2) (normalizedWeights4246 c3) 3 <
      sourceMinima5 (compound4246 A2) (compound4246 A3) (compound4246 L) (compound_unit4246 L hL)
        p (hp p hpP) (normalizedWeights4246 c0) (normalizedWeights4246 c2) (normalizedWeights4246 c3) 4 *
        p^(-(delta/8)) := by
    let q := lift ⟨p,hpP⟩
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hg⟩ := hgate q.val (hqU q.val q.property)
      c0 c2 c3 hc0 hc2 hc3 hb ((le_max_left _ _).trans_lt q.property.2)
      (hgap q.val q.property.1)
    have heq : q.val^4 = p := hlift ⟨p,hpP⟩
    simpa only [heq, neg_div] using hg
  obtain ⟨H,hH,Vprime,hVP,hVprime,hfixed⟩ :=
    BlockRank4_245U.source_original_fixed_rank4_245
      (compound4246 A2) (compound4246 A3) (compound4246 L)
      (compound_det_one4246 A2 h2d) (compound_det_one4246 A3 h3d) (compound_det_one4246 L hLd)
      (compound_unit4246 L hL) (compound_algebraic4246 L hAlg)
      (normalizedWeights4246 c0) (normalizedWeights4246 c2) (normalizedWeights4246 c3)
      (normalized_real_bound4246 c0 hc0) (normalized_finite_bounds4246 c2 hc2)
      (normalized_finite_bounds4246 c3 hc3) (normalized_balance4246 c0 c2 c3 hb)
      (delta/8) hdelta P hP hp hgp
  let V : Set ℝ := {Q | ∃ p : P, p.val ∈ Vprime ∧ (lift p).val = Q}
  have hVO : V ⊆ Omega := by
    rintro Q ⟨p,hpV,rfl⟩
    exact (lift p).property.1
  refine ⟨H,hH,V,hVO,fourth_pullback_unbounded247 U hqU lift hlift Vprime hVP hVprime,?_⟩
  intro Q hQV
  obtain ⟨p,hpV,heq⟩ := hQV
  have hlarge : Tshort < Q := by
    rw [← heq]
    exact (le_max_right _ _).trans_lt (lift p).property.2
  have hpower : p.val = Q^4 := (hlift p).symm.trans (congrArg (fun x : ℝ => x^4) heq)
  obtain ⟨w,hw,ha,hs⟩ := hfixed p.val hpV
  rcases p with ⟨p,hpP⟩
  change p = Q^4 at hpower
  subst p
  exact ⟨hlarge,w,hw,ha,hs⟩

end CompoundFeasibility.SourceFlag247
